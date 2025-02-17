// Copyright (C) 2020-2025 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
mod v0;

use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use clarity::boot_util::boot_code_id;
use clarity::vm::types::PrincipalData;
use libsigner::v0::messages::{
    BlockAccepted, BlockResponse, MessageSlotID, PeerInfo, SignerMessage,
};
use libsigner::{BlockProposal, SignerEntries, SignerEventTrait};
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::chainstate::nakamoto::signer_set::NakamotoSigners;
use stacks::chainstate::nakamoto::NakamotoBlock;
use stacks::chainstate::stacks::boot::{NakamotoSignerEntry, SIGNERS_NAME};
use stacks::chainstate::stacks::StacksPrivateKey;
use stacks::config::{Config as NeonConfig, EventKeyType, EventObserverConfig, InitialBalance};
use stacks::net::api::postblock_proposal::{
    BlockValidateOk, BlockValidateReject, BlockValidateResponse,
};
use stacks::types::chainstate::{StacksAddress, StacksPublicKey};
use stacks::types::PrivateKey;
use stacks::util::get_epoch_time_secs;
use stacks::util::hash::MerkleHashFunc;
use stacks::util::secp256k1::{MessageSignature, Secp256k1PublicKey};
use stacks_common::codec::StacksMessageCodec;
use stacks_common::consts::SIGNER_SLOTS_PER_USER;
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash::Sha512Trunc256Sum;
use stacks_signer::client::{ClientError, SignerSlotID, StackerDB, StacksClient};
use stacks_signer::config::{build_signer_config_tomls, GlobalConfig as SignerConfig, Network};
use stacks_signer::runloop::{SignerResult, State, StateInfo};
use stacks_signer::{Signer, SpawnedSigner};

use super::nakamoto_integrations::{check_nakamoto_empty_block_heuristics, wait_for};
use crate::neon::Counters;
use crate::run_loop::boot_nakamoto;
use crate::tests::bitcoin_regtest::BitcoinCoreController;
use crate::tests::nakamoto_integrations::{
    naka_neon_integration_conf, next_block_and_mine_commit, next_block_and_wait_for_commits,
    POX_4_DEFAULT_STACKER_BALANCE,
};
use crate::tests::neon_integrations::{
    get_chain_info, next_block_and_wait, run_until_burnchain_height, test_observer,
    wait_for_runloop,
};
use crate::tests::to_addr;
use crate::BitcoinRegtestController;

// Helper struct for holding the btc and stx neon nodes
#[allow(dead_code)]
pub struct RunningNodes {
    pub btc_regtest_controller: BitcoinRegtestController,
    pub btcd_controller: BitcoinCoreController,
    pub run_loop_thread: thread::JoinHandle<()>,
    pub run_loop_stopper: Arc<AtomicBool>,
    pub counters: Counters,
    pub coord_channel: Arc<Mutex<CoordinatorChannels>>,
    pub conf: NeonConfig,
}

/// A test harness for running a v0 or v1 signer integration test
pub struct SignerTest<S> {
    // The stx and bitcoin nodes and their run loops
    pub running_nodes: RunningNodes,
    // The spawned signers and their threads
    pub spawned_signers: Vec<S>,
    // The spawned signers and their threads
    #[allow(dead_code)]
    pub signer_configs: Vec<SignerConfig>,
    // the private keys of the signers
    pub signer_stacks_private_keys: Vec<StacksPrivateKey>,
    // link to the stacks node
    pub stacks_client: StacksClient,
    /// The number of cycles to stack for
    pub num_stacking_cycles: u64,
}

impl<S: Signer<T> + Send + 'static, T: SignerEventTrait + 'static> SignerTest<SpawnedSigner<S, T>> {
    pub fn new(num_signers: usize, initial_balances: Vec<(StacksAddress, u64)>) -> Self {
        Self::new_with_config_modifications(
            num_signers,
            initial_balances,
            |_| {},
            |_| {},
            None,
            None,
        )
    }

    pub fn new_with_config_modifications<F: FnMut(&mut SignerConfig), G: FnMut(&mut NeonConfig)>(
        num_signers: usize,
        initial_balances: Vec<(StacksAddress, u64)>,
        mut signer_config_modifier: F,
        mut node_config_modifier: G,
        btc_miner_pubkeys: Option<Vec<Secp256k1PublicKey>>,
        signer_stacks_private_keys: Option<Vec<StacksPrivateKey>>,
    ) -> Self {
        // Generate Signer Data
        let signer_stacks_private_keys = signer_stacks_private_keys
            .inspect(|keys| {
                assert_eq!(
                    keys.len(),
                    num_signers,
                    "Number of private keys does not match number of signers"
                )
            })
            .unwrap_or_else(|| {
                (0..num_signers)
                    .map(|_| StacksPrivateKey::random())
                    .collect()
            });

        let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);

        node_config_modifier(&mut naka_conf);

        // Add initial balances to the config
        for (address, amount) in initial_balances.iter() {
            naka_conf.add_initial_balance(PrincipalData::from(*address).to_string(), *amount);
        }

        // So the combination is... one, two, three, four, five? That's the stupidest combination I've ever heard in my life!
        // That's the kind of thing an idiot would have on his luggage!
        let password = "12345";
        naka_conf.connection_options.auth_token = Some(password.to_string());
        let run_stamp = rand::random();

        // Setup the signer and coordinator configurations
        let signer_configs: Vec<_> = build_signer_config_tomls(
            &signer_stacks_private_keys,
            &naka_conf.node.rpc_bind,
            Some(Duration::from_millis(128)), // Timeout defaults to 5 seconds. Let's override it to 128 milliseconds.
            &Network::Testnet,
            password,
            run_stamp,
            3000,
            Some(100_000),
            None,
            Some(9000),
            None,
        )
        .into_iter()
        .map(|toml| {
            let mut signer_config = SignerConfig::load_from_str(&toml).unwrap();
            signer_config_modifier(&mut signer_config);
            signer_config
        })
        .collect();
        assert_eq!(signer_configs.len(), num_signers);

        let spawned_signers = signer_configs
            .iter()
            .cloned()
            .map(SpawnedSigner::new)
            .collect();

        // Setup the nodes and deploy the contract to it
        let btc_miner_pubkeys = btc_miner_pubkeys
            .filter(|keys| !keys.is_empty())
            .unwrap_or_else(|| {
                let pk = Secp256k1PublicKey::from_hex(
                    naka_conf
                        .burnchain
                        .local_mining_public_key
                        .as_ref()
                        .unwrap(),
                )
                .unwrap();
                vec![pk]
            });

        let node = setup_stx_btc_node(
            naka_conf,
            &signer_stacks_private_keys,
            &signer_configs,
            btc_miner_pubkeys.as_slice(),
            node_config_modifier,
        );
        let config = signer_configs.first().unwrap();
        let stacks_client = StacksClient::from(config);

        Self {
            running_nodes: node,
            spawned_signers,
            signer_stacks_private_keys,
            stacks_client,
            num_stacking_cycles: 12_u64,
            signer_configs,
        }
    }

    /// Send a status request to each spawned signer
    pub fn send_status_request(&self, exclude: &HashSet<usize>) {
        for signer_ix in 0..self.spawned_signers.len() {
            if exclude.contains(&signer_ix) {
                continue;
            }
            let port = 3000 + signer_ix;
            let endpoint = format!("http://localhost:{port}");
            let path = format!("{endpoint}/status");

            debug!("Issue status request to {path}");
            let client = reqwest::blocking::Client::new();
            let response = client
                .get(path)
                .send()
                .expect("Failed to send status request");
            assert!(response.status().is_success())
        }
    }

    pub fn wait_for_registered(&mut self, timeout_secs: u64) {
        let mut finished_signers = HashSet::new();
        wait_for(timeout_secs, || {
            self.send_status_request(&finished_signers);
            thread::sleep(Duration::from_secs(1));
            let latest_states = self.get_states(&finished_signers);
            for (ix, state) in latest_states.iter().enumerate() {
                let Some(state) = state else { continue; };
                if state.runloop_state == State::RegisteredSigners {
                    finished_signers.insert(ix);
                } else {
                    warn!("Signer #{ix} returned state = {:?}, will try to wait for a registered signers state from them.", state.runloop_state);
                }
            }
            info!("Finished signers: {:?}", finished_signers.iter().collect::<Vec<_>>());
            Ok(finished_signers.len() == self.spawned_signers.len())
        }).expect("Timed out while waiting for the signers to be registered");
    }

    /// Send a status request to the signers to ensure they are registered for both reward cycles.
    pub fn wait_for_registered_both_reward_cycles(&mut self, timeout_secs: u64) {
        let mut finished_signers = HashSet::new();
        wait_for(timeout_secs, || {
            self.send_status_request(&finished_signers);
            thread::sleep(Duration::from_secs(1));
            let latest_states = self.get_states(&finished_signers);
            for (ix, state) in latest_states.iter().enumerate() {
                let Some(state) = state else {
                    continue;
                };
                debug!("Signer #{ix} state info: {state:?}");
                if state.runloop_state == State::RegisteredSigners && state.running_signers.len() == 2 {
                    finished_signers.insert(ix);
                } else {
                    warn!(
                        "Signer #{ix} returned state = {:?}, running signers = {:?}. Will try again",
                        state.runloop_state, state.running_signers
                    );
                }
            }
            debug!("Number of finished signers: {:?}", finished_signers.len());
            Ok(finished_signers.len() == self.spawned_signers.len())
        })
        .expect("Timed out while waiting for the signers to be registered for both reward cycles");
    }

    pub fn wait_for_cycle(&mut self, timeout_secs: u64, reward_cycle: u64) {
        let mut finished_signers = HashSet::new();
        wait_for(timeout_secs, || {
            self.send_status_request(&finished_signers);
            thread::sleep(Duration::from_secs(1));
            let latest_states = self.get_states(&finished_signers);
            for (ix, state) in latest_states.iter().enumerate() {
                let Some(state) = state else { continue; };
                let Some(reward_cycle_info) = state.reward_cycle_info else { continue; };
                if reward_cycle_info.reward_cycle == reward_cycle {
                    finished_signers.insert(ix);
                } else {
                    warn!("Signer #{ix} returned state = {state:?}, will try to wait for a cycle = {reward_cycle} state from them.");
                }
            }
            info!("Finished signers: {:?}", finished_signers.iter().collect::<Vec<_>>());
            Ok(finished_signers.len() == self.spawned_signers.len())
        }).unwrap();
    }

    /// Get status check results (if returned) from each signer without blocking
    /// Returns Some() or None() for each signer, in order of `self.spawned_signers`
    pub fn get_states(&mut self, exclude: &HashSet<usize>) -> Vec<Option<StateInfo>> {
        let mut output = Vec::new();
        for (ix, signer) in self.spawned_signers.iter().enumerate() {
            if exclude.contains(&ix) {
                output.push(None);
                continue;
            }
            let Ok(mut results) = signer.res_recv.try_recv() else {
                debug!("Could not receive latest state from signer #{ix}");
                output.push(None);
                continue;
            };
            assert!(results.len() <= 1, "Received multiple states from the signer receiver: this test function assumes it should only ever receive 1");
            let Some(SignerResult::StatusCheck(state_info)) = results.pop() else {
                debug!("Could not receive latest state from signer #{ix}");
                output.push(None);
                continue;
            };
            output.push(Some(state_info));
        }
        output
    }

    /// Mine a BTC block and wait for a new Stacks block to be mined
    /// Note: do not use nakamoto blocks mined heuristic if running a test with multiple miners
    fn mine_nakamoto_block(&mut self, timeout: Duration, use_nakamoto_blocks_mined: bool) {
        let mined_block_time = Instant::now();
        let mined_before = self.running_nodes.counters.naka_mined_blocks.get();
        let info_before = self.get_peer_info();
        next_block_and_mine_commit(
            &mut self.running_nodes.btc_regtest_controller,
            timeout.as_secs(),
            &self.running_nodes.conf,
            &self.running_nodes.counters,
        )
        .unwrap();

        wait_for(timeout.as_secs(), || {
            let info_after = self.get_peer_info();
            let blocks_mined = self.running_nodes.counters.naka_mined_blocks.get();
            Ok(info_after.stacks_tip_height > info_before.stacks_tip_height
                && (!use_nakamoto_blocks_mined || blocks_mined > mined_before))
        })
        .unwrap();
        let mined_block_elapsed_time = mined_block_time.elapsed();
        info!("Nakamoto block mine time elapsed: {mined_block_elapsed_time:?}");
    }

    fn mine_block_wait_on_processing(
        &mut self,
        node_confs: &[&NeonConfig],
        node_counters: &[&Counters],
        timeout: Duration,
    ) {
        let blocks_len = test_observer::get_blocks().len();
        let mined_block_time = Instant::now();
        next_block_and_wait_for_commits(
            &mut self.running_nodes.btc_regtest_controller,
            timeout.as_secs(),
            node_confs,
            node_counters,
            true,
        )
        .unwrap();
        let t_start = Instant::now();
        while test_observer::get_blocks().len() <= blocks_len {
            assert!(
                t_start.elapsed() < timeout,
                "Timed out while waiting for nakamoto block to be processed"
            );
            thread::sleep(Duration::from_secs(1));
        }
        let mined_block_elapsed_time = mined_block_time.elapsed();
        info!("Nakamoto block mine time elapsed: {mined_block_elapsed_time:?}");
    }

    /// Helper function to run some code and then wait for a nakamoto block to be mined.
    /// Chain information is captured before `f` is called, and then again after `f`
    /// to ensure that the block was mined.
    /// Note: this function does _not_ mine a BTC block.
    fn wait_for_nakamoto_block(&mut self, timeout_secs: u64, f: impl FnOnce() -> ()) {
        let blocks_before = self.running_nodes.counters.naka_mined_blocks.get();
        let info_before = self.get_peer_info();

        f();

        // Verify that the block was mined
        wait_for(timeout_secs, || {
            let blocks_mined = self.running_nodes.counters.naka_mined_blocks.get();
            let info = self.get_peer_info();
            Ok(blocks_mined > blocks_before
                && info.stacks_tip_height > info_before.stacks_tip_height)
        })
        .expect("Timed out waiting for nakamoto block to be mined");
    }

    /// Wait for a confirmed block and return a list of individual
    /// signer signatures
    fn wait_for_confirmed_block_v0(
        &mut self,
        block_signer_sighash: &Sha512Trunc256Sum,
        timeout: Duration,
    ) -> Vec<MessageSignature> {
        let block_obj = self.wait_for_confirmed_block_with_hash(block_signer_sighash, timeout);
        block_obj
            .get("signer_signature")
            .unwrap()
            .as_array()
            .expect("Expected signer_signature to be an array")
            .iter()
            .cloned()
            .map(serde_json::from_value::<MessageSignature>)
            .collect::<Result<Vec<_>, _>>()
            .expect("Unable to deserialize array of MessageSignature")
    }

    /// Wait for a confirmed block and return a list of individual
    /// signer signatures
    fn wait_for_confirmed_block_with_hash(
        &mut self,
        block_signer_sighash: &Sha512Trunc256Sum,
        timeout: Duration,
    ) -> serde_json::Map<String, serde_json::Value> {
        let t_start = Instant::now();
        while t_start.elapsed() <= timeout {
            let blocks = test_observer::get_blocks();
            if let Some(block) = blocks.iter().find_map(|block_json| {
                let block_obj = block_json.as_object().unwrap();
                let sighash = block_obj
                    // use the try operator because non-nakamoto blocks
                    // do not supply this field
                    .get("signer_signature_hash")?
                    .as_str()
                    .unwrap();
                if *sighash != format!("0x{block_signer_sighash}") {
                    return None;
                }
                Some(block_obj.clone())
            }) {
                return block;
            }
            thread::sleep(Duration::from_millis(500));
        }
        panic!("Timed out while waiting for confirmation of block with signer sighash = {block_signer_sighash}")
    }

    fn wait_for_validate_ok_response(&mut self, timeout: Duration) -> BlockValidateOk {
        // Wait for the block to show up in the test observer
        let t_start = Instant::now();
        loop {
            let responses = test_observer::get_proposal_responses();
            for response in responses {
                let BlockValidateResponse::Ok(validation) = response else {
                    continue;
                };
                return validation;
            }
            assert!(
                t_start.elapsed() < timeout,
                "Timed out while waiting for block proposal ok event"
            );
            thread::sleep(Duration::from_secs(1));
        }
    }

    fn wait_for_validate_reject_response(
        &mut self,
        timeout: Duration,
        signer_signature_hash: Sha512Trunc256Sum,
    ) -> BlockValidateReject {
        // Wait for the block to show up in the test observer
        let t_start = Instant::now();
        loop {
            let responses = test_observer::get_proposal_responses();
            for response in responses {
                let BlockValidateResponse::Reject(rejection) = response else {
                    continue;
                };
                if rejection.signer_signature_hash == signer_signature_hash {
                    return rejection;
                }
            }
            assert!(
                t_start.elapsed() < timeout,
                "Timed out while waiting for block proposal reject event"
            );
            thread::sleep(Duration::from_secs(1));
        }
    }

    // Must be called AFTER booting the chainstate
    fn run_until_epoch_3_boundary(&mut self) {
        let epochs = self.running_nodes.conf.burnchain.epochs.clone().unwrap();
        let epoch_3 = &epochs[StacksEpochId::Epoch30];

        let epoch_30_boundary = epoch_3.start_height - 1;
        // advance to epoch 3.0 and trigger a sign round (cannot vote on blocks in pre epoch 3.0)
        run_until_burnchain_height(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
            epoch_30_boundary,
            &self.running_nodes.conf,
        );
        info!("Advanced to Nakamoto epoch 3.0 boundary {epoch_30_boundary}! Ready to Sign Blocks!");
    }

    fn get_current_reward_cycle(&self) -> u64 {
        let block_height = get_chain_info(&self.running_nodes.conf).burn_block_height;
        let rc = self
            .running_nodes
            .btc_regtest_controller
            .get_burnchain()
            .block_height_to_reward_cycle(block_height)
            .unwrap();
        info!("Get current reward cycle: block_height = {block_height}, rc = {rc}");
        rc
    }

    fn get_signer_slots(
        &self,
        reward_cycle: u64,
    ) -> Result<Vec<(StacksAddress, u128)>, ClientError> {
        let valid_signer_set =
            u32::try_from(reward_cycle % 2).expect("FATAL: reward_cycle % 2 exceeds u32::MAX");
        let signer_stackerdb_contract_id = boot_code_id(SIGNERS_NAME, false);

        self.stacks_client
            .get_stackerdb_signer_slots(&signer_stackerdb_contract_id, valid_signer_set)
    }

    fn get_signer_slot_id(
        &self,
        reward_cycle: u64,
        signer_address: &StacksAddress,
    ) -> Result<Option<SignerSlotID>, ClientError> {
        let valid_signer_set =
            u32::try_from(reward_cycle % 2).expect("FATAL: reward_cycle % 2 exceeds u32::MAX");
        let signer_stackerdb_contract_id = boot_code_id(SIGNERS_NAME, false);

        let slots = self
            .stacks_client
            .get_stackerdb_signer_slots(&signer_stackerdb_contract_id, valid_signer_set)?;

        Ok(slots
            .iter()
            .position(|(address, _)| address == signer_address)
            .map(|pos| {
                SignerSlotID(u32::try_from(pos).expect("FATAL: number of signers exceeds u32::MAX"))
            }))
    }

    fn get_signer_indices(&self, reward_cycle: u64) -> Vec<SignerSlotID> {
        self.get_signer_slots(reward_cycle)
            .expect("FATAL: failed to get signer slots from stackerdb")
            .iter()
            .enumerate()
            .map(|(pos, _)| {
                SignerSlotID(u32::try_from(pos).expect("FATAL: number of signers exceeds u32::MAX"))
            })
            .collect::<Vec<_>>()
    }

    /// Get the signer public keys for the given reward cycle
    fn get_signer_public_keys(&self, reward_cycle: u64) -> Vec<StacksPublicKey> {
        let entries = self.get_reward_set_signers(reward_cycle);
        let entries = SignerEntries::parse(false, &entries).unwrap();
        entries.signer_pks
    }

    /// Get the signers for the given reward cycle
    pub fn get_reward_set_signers(&self, reward_cycle: u64) -> Vec<NakamotoSignerEntry> {
        self.stacks_client
            .get_reward_set_signers(reward_cycle)
            .unwrap()
            .unwrap()
    }

    #[allow(dead_code)]
    fn get_signer_metrics(&self) -> String {
        #[cfg(feature = "monitoring_prom")]
        {
            let client = reqwest::blocking::Client::new();
            client
                .get("http://localhost:9000/metrics")
                .send()
                .unwrap()
                .text()
                .unwrap()
        }
        #[cfg(not(feature = "monitoring_prom"))]
        String::new()
    }

    pub fn shutdown(self) {
        check_nakamoto_empty_block_heuristics();

        self.running_nodes
            .coord_channel
            .lock()
            .expect("Mutex poisoned")
            .stop_chains_coordinator();

        self.running_nodes
            .run_loop_stopper
            .store(false, Ordering::SeqCst);
        self.running_nodes.run_loop_thread.join().unwrap();
        for signer in self.spawned_signers {
            assert!(signer.stop().is_none());
        }
    }

    /// Get the latest block response from the given slot
    pub fn get_latest_block_response(&self, slot_id: u32) -> BlockResponse {
        let mut stackerdb = StackerDB::new_normal(
            &self.running_nodes.conf.node.rpc_bind,
            StacksPrivateKey::random(), // We are just reading so don't care what the key is
            false,
            self.get_current_reward_cycle(),
            SignerSlotID(0), // We are just reading so again, don't care about index.
        );
        let latest_msgs = StackerDB::get_messages(
            stackerdb
                .get_session_mut(&MessageSlotID::BlockResponse)
                .expect("Failed to get BlockResponse stackerdb session"),
            &[slot_id],
        )
        .expect("Failed to get message from stackerdb");
        let latest_msg = latest_msgs.last().unwrap();
        let SignerMessage::BlockResponse(block_response) = latest_msg else {
            panic!("Latest message from slot #{slot_id} isn't a block acceptance");
        };
        block_response.clone()
    }

    /// Get the latest block acceptance from the given slot
    pub fn get_latest_block_acceptance(&self, slot_id: u32) -> BlockAccepted {
        self.get_latest_block_response(slot_id)
            .as_block_accepted()
            .expect("Latest block response from slot #{slot_id} isn't a block acceptance")
            .clone()
    }

    /// Get miner stackerDB messages
    pub fn get_miner_proposal_messages(&self) -> Vec<BlockProposal> {
        let proposals: Vec<_> = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                else {
                    return None;
                };
                match message {
                    SignerMessage::BlockProposal(proposal) => Some(proposal),
                    _ => None,
                }
            })
            .collect();
        proposals
    }

    /// Get /v2/info from the node
    pub fn get_peer_info(&self) -> PeerInfo {
        self.stacks_client
            .get_peer_info()
            .expect("Failed to get peer info")
    }

    pub fn verify_no_block_response_found(
        &self,
        stackerdb: &mut StackerDB<MessageSlotID>,
        reward_cycle: u64,
        hash: Sha512Trunc256Sum,
    ) {
        let slot_ids: Vec<_> = self
            .get_signer_indices(reward_cycle)
            .iter()
            .map(|id| id.0)
            .collect();

        let latest_msgs = StackerDB::get_messages::<SignerMessage>(
            stackerdb
                .get_session_mut(&MessageSlotID::BlockResponse)
                .expect("Failed to get BlockResponse stackerdb session"),
            &slot_ids,
        )
        .expect("Failed to get messages from stackerdb");
        for msg in latest_msgs.iter() {
            if let SignerMessage::BlockResponse(response) = msg {
                assert_ne!(response.get_signer_signature_hash(), hash);
            }
        }
    }

    pub fn inject_accept_signature(
        &self,
        block: &NakamotoBlock,
        private_key: &StacksPrivateKey,
        reward_cycle: u64,
    ) {
        let mut stackerdb = StackerDB::new_normal(
            &self.running_nodes.conf.node.rpc_bind,
            private_key.clone(),
            false,
            reward_cycle,
            self.get_signer_slot_id(reward_cycle, &to_addr(private_key))
                .expect("Failed to get signer slot id")
                .expect("Signer does not have a slot id"),
        );

        let signature = private_key
            .sign(block.header.signer_signature_hash().bits())
            .expect("Failed to sign block");
        let accepted = BlockResponse::accepted(
            block.header.signer_signature_hash(),
            signature,
            get_epoch_time_secs().wrapping_add(u64::MAX),
        );
        stackerdb
            .send_message_with_retry::<SignerMessage>(accepted.into())
            .expect("Failed to send accept signature");
    }
}

fn setup_stx_btc_node<G: FnMut(&mut NeonConfig)>(
    mut naka_conf: NeonConfig,
    signer_stacks_private_keys: &[StacksPrivateKey],
    signer_configs: &[SignerConfig],
    btc_miner_pubkeys: &[Secp256k1PublicKey],
    mut node_config_modifier: G,
) -> RunningNodes {
    // Spawn the endpoints for observing signers
    for signer_config in signer_configs {
        naka_conf.events_observers.insert(EventObserverConfig {
            endpoint: signer_config.endpoint.to_string(),
            events_keys: vec![
                EventKeyType::StackerDBChunks,
                EventKeyType::BlockProposal,
                EventKeyType::BurnchainBlocks,
            ],
            timeout_ms: 1000,
            lossy: false,
        });
    }

    // Spawn a test observer for verification purposes
    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![
            EventKeyType::StackerDBChunks,
            EventKeyType::BlockProposal,
            EventKeyType::MinedBlocks,
            EventKeyType::BurnchainBlocks,
        ],
        timeout_ms: 1000,
        lossy: false,
    });

    // The signers need some initial balances in order to pay for epoch 2.5 transaction votes
    let mut initial_balances = Vec::new();

    // TODO: separate keys for stacking and signing (because they'll be different in prod)
    for key in signer_stacks_private_keys {
        initial_balances.push(InitialBalance {
            address: to_addr(key).into(),
            amount: POX_4_DEFAULT_STACKER_BALANCE,
        });
    }
    naka_conf.initial_balances.append(&mut initial_balances);
    naka_conf.node.stacker = true;
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(5);

    for signer_set in 0..2 {
        for message_id in 0..SIGNER_SLOTS_PER_USER {
            let contract_id =
                NakamotoSigners::make_signers_db_contract_id(signer_set, message_id, false);
            if !naka_conf.node.stacker_dbs.contains(&contract_id) {
                debug!("A miner/stacker must subscribe to the {contract_id} stacker db contract. Forcibly subscribing...");
                naka_conf.node.stacker_dbs.push(contract_id);
            }
        }
    }
    node_config_modifier(&mut naka_conf);

    info!("Make new BitcoinCoreController");
    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    info!("Make new BitcoinRegtestController");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);

    let epoch_2_5_start = usize::try_from(
        naka_conf
            .burnchain
            .epochs
            .as_ref()
            .unwrap()
            .iter()
            .find(|epoch| epoch.epoch_id == StacksEpochId::Epoch25)
            .unwrap()
            .start_height,
    )
    .expect("Failed to get epoch 2.5 start height");
    let bootstrap_block = epoch_2_5_start - 6;

    info!("Bootstraping to block {bootstrap_block}...");
    btc_regtest_controller.bootstrap_chain_to_pks(bootstrap_block, btc_miner_pubkeys);

    info!("Chain bootstrapped...");

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let counters = run_loop.counters();
    let blocks_processed = counters.blocks_processed.clone();

    let coord_channel = run_loop.coordinator_channels();
    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    info!("Wait for runloop...");
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    info!("Mine first block...");
    next_block_and_wait(&mut btc_regtest_controller, &counters.blocks_processed);

    // Second block will hold our VRF registration.
    info!("Mine second block...");
    next_block_and_wait(&mut btc_regtest_controller, &counters.blocks_processed);

    // Third block will be the first mined Stacks block.
    info!("Mine third block...");
    next_block_and_wait(&mut btc_regtest_controller, &counters.blocks_processed);

    RunningNodes {
        btcd_controller,
        btc_regtest_controller,
        run_loop_thread,
        run_loop_stopper,
        coord_channel,
        counters,
        conf: naka_conf,
    }
}
