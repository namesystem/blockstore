// Copyright (C) 2020-2024 Stacks Open Internet Foundation
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

use std::collections::{HashMap, HashSet};
use std::ops::Add;
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use std::{env, thread};

use clarity::vm::types::PrincipalData;
use libsigner::v0::messages::{
    BlockAccepted, BlockRejection, BlockResponse, MessageSlotID, MinerSlotID, PeerInfo, RejectCode,
    RejectReason, SignerMessage,
};
use libsigner::{
    BlockProposal, BlockProposalData, SignerSession, StackerDBSession, VERSION_STRING,
};
use stacks::address::AddressHashMode;
use stacks::burnchains::Txid;
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::operations::LeaderBlockCommitOp;
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader, NakamotoChainState};
use stacks::chainstate::stacks::address::PoxAddress;
use stacks::chainstate::stacks::boot::MINERS_NAME;
use stacks::chainstate::stacks::db::{StacksBlockHeaderTypes, StacksChainState, StacksHeaderInfo};
use stacks::chainstate::stacks::miner::{TransactionEvent, TransactionSuccessEvent};
use stacks::chainstate::stacks::{StacksTransaction, TenureChangeCause, TransactionPayload};
use stacks::codec::StacksMessageCodec;
use stacks::config::{Config as NeonConfig, EventKeyType, EventObserverConfig};
use stacks::core::{StacksEpochId, CHAIN_ID_TESTNET};
use stacks::libstackerdb::StackerDBChunkData;
use stacks::net::api::getsigner::GetSignerResponse;
use stacks::net::api::postblock_proposal::{
    BlockValidateResponse, ValidateRejectCode, TEST_VALIDATE_DELAY_DURATION_SECS,
    TEST_VALIDATE_STALL,
};
use stacks::net::relay::fault_injection::set_ignore_block;
use stacks::types::chainstate::{
    BlockHeaderHash, StacksAddress, StacksBlockId, StacksPrivateKey, StacksPublicKey,
};
use stacks::types::PublicKey;
use stacks::util::get_epoch_time_secs;
use stacks::util::hash::{hex_bytes, Hash160, MerkleHashFunc, Sha512Trunc256Sum};
use stacks::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks::util_lib::boot::boot_code_id;
use stacks::util_lib::signed_structured_data::pox4::{
    make_pox_4_signer_key_signature, Pox4SignatureTopic,
};
use stacks_common::bitvec::BitVec;
use stacks_common::types::chainstate::TrieHash;
use stacks_common::util::sleep_ms;
use stacks_signer::chainstate::{ProposalEvalConfig, SortitionsView};
use stacks_signer::client::{SignerSlotID, StackerDB};
use stacks_signer::config::{build_signer_config_tomls, GlobalConfig as SignerConfig, Network};
use stacks_signer::signerdb::SignerDb;
use stacks_signer::v0::tests::{
    TEST_IGNORE_ALL_BLOCK_PROPOSALS, TEST_PAUSE_BLOCK_BROADCAST, TEST_REJECT_ALL_BLOCK_PROPOSAL,
    TEST_SKIP_BLOCK_BROADCAST, TEST_SKIP_SIGNER_CLEANUP, TEST_STALL_BLOCK_VALIDATION_SUBMISSION,
};
use stacks_signer::v0::SpawnedSigner;
use tracing_subscriber::prelude::*;
use tracing_subscriber::{fmt, EnvFilter};

use super::SignerTest;
use crate::event_dispatcher::{MinedNakamotoBlockEvent, TEST_SKIP_BLOCK_ANNOUNCEMENT};
use crate::nakamoto_node::miner::{
    TEST_BLOCK_ANNOUNCE_STALL, TEST_BROADCAST_PROPOSAL_STALL, TEST_MINE_STALL,
    TEST_P2P_BROADCAST_STALL,
};
use crate::nakamoto_node::stackerdb_listener::TEST_IGNORE_SIGNERS;
use crate::neon::Counters;
use crate::run_loop::boot_nakamoto;
use crate::tests::nakamoto_integrations::{
    boot_to_epoch_25, boot_to_epoch_3_reward_set, next_block_and, next_block_and_controller,
    next_block_and_process_new_stacks_block, setup_epoch_3_reward_set, wait_for,
    POX_4_DEFAULT_STACKER_BALANCE, POX_4_DEFAULT_STACKER_STX_AMT,
};
use crate::tests::neon_integrations::{
    get_account, get_chain_info, get_chain_info_opt, get_pox_info, get_sortition_info,
    get_sortition_info_ch, next_block_and_wait, run_until_burnchain_height, submit_tx,
    submit_tx_fallible, test_observer,
};
use crate::tests::{
    self, gen_random_port, make_contract_call, make_contract_publish, make_stacks_transfer,
};
use crate::{nakamoto_node, BitcoinRegtestController, BurnchainController, Config, Keychain};

impl SignerTest<SpawnedSigner> {
    /// Run the test until the first epoch 2.5 reward cycle.
    /// Will activate pox-4 and register signers for the first full Epoch 2.5 reward cycle.
    fn boot_to_epoch_25_reward_cycle(&mut self) {
        boot_to_epoch_25(
            &self.running_nodes.conf,
            &self.running_nodes.counters.blocks_processed,
            &mut self.running_nodes.btc_regtest_controller,
        );

        next_block_and_wait(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
        );

        let http_origin = format!("http://{}", &self.running_nodes.conf.node.rpc_bind);
        let lock_period = 12;

        let epochs = self.running_nodes.conf.burnchain.epochs.clone().unwrap();
        let epoch_25 = &epochs[StacksEpochId::Epoch25];
        let epoch_25_start_height = epoch_25.start_height;
        // stack enough to activate pox-4
        let block_height = self
            .running_nodes
            .btc_regtest_controller
            .get_headers_height();
        let reward_cycle = self
            .running_nodes
            .btc_regtest_controller
            .get_burnchain()
            .block_height_to_reward_cycle(block_height)
            .unwrap();
        for stacker_sk in self.signer_stacks_private_keys.iter() {
            let pox_addr = PoxAddress::from_legacy(
                AddressHashMode::SerializeP2PKH,
                tests::to_addr(stacker_sk).bytes().clone(),
            );
            let pox_addr_tuple: clarity::vm::Value =
                pox_addr.clone().as_clarity_tuple().unwrap().into();
            let signature = make_pox_4_signer_key_signature(
                &pox_addr,
                stacker_sk,
                reward_cycle.into(),
                &Pox4SignatureTopic::StackStx,
                CHAIN_ID_TESTNET,
                lock_period,
                u128::MAX,
                1,
            )
            .unwrap()
            .to_rsv();

            let signer_pk = StacksPublicKey::from_private(stacker_sk);
            let stacking_tx = tests::make_contract_call(
                stacker_sk,
                0,
                1000,
                self.running_nodes.conf.burnchain.chain_id,
                &StacksAddress::burn_address(false),
                "pox-4",
                "stack-stx",
                &[
                    clarity::vm::Value::UInt(POX_4_DEFAULT_STACKER_STX_AMT),
                    pox_addr_tuple.clone(),
                    clarity::vm::Value::UInt(block_height as u128),
                    clarity::vm::Value::UInt(lock_period),
                    clarity::vm::Value::some(clarity::vm::Value::buff_from(signature).unwrap())
                        .unwrap(),
                    clarity::vm::Value::buff_from(signer_pk.to_bytes_compressed()).unwrap(),
                    clarity::vm::Value::UInt(u128::MAX),
                    clarity::vm::Value::UInt(1),
                ],
            );
            submit_tx(&http_origin, &stacking_tx);
        }
        next_block_and_wait(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
        );
        next_block_and_wait(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
        );

        let reward_cycle_len = self
            .running_nodes
            .conf
            .get_burnchain()
            .pox_constants
            .reward_cycle_length as u64;

        let epoch_25_reward_cycle_boundary =
            epoch_25_start_height.saturating_sub(epoch_25_start_height % reward_cycle_len);
        let next_reward_cycle_boundary =
            epoch_25_reward_cycle_boundary.wrapping_add(reward_cycle_len);
        let target_height = next_reward_cycle_boundary - 1;
        info!("Advancing to burn block height {target_height}...",);
        run_until_burnchain_height(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
            target_height,
            &self.running_nodes.conf,
        );
        debug!("Waiting for signer set calculation.");
        let mut reward_set_calculated = false;
        let short_timeout = Duration::from_secs(60);
        let now = std::time::Instant::now();
        // Make sure the signer set is calculated before continuing or signers may not
        // recognize that they are registered signers in the subsequent burn block event
        let reward_cycle = self.get_current_reward_cycle().wrapping_add(1);
        while !reward_set_calculated {
            let reward_set = self
                .stacks_client
                .get_reward_set_signers(reward_cycle)
                .expect("Failed to check if reward set is calculated");
            reward_set_calculated = reward_set.is_some();
            if reward_set_calculated {
                debug!("Signer set: {:?}", reward_set.unwrap());
            }
            std::thread::sleep(Duration::from_secs(1));
            assert!(
                now.elapsed() < short_timeout,
                "Timed out waiting for reward set calculation"
            );
        }
        debug!("Signer set calculated");
        // Manually consume one more block to ensure signers refresh their state
        debug!("Waiting for signers to initialize.");
        info!("Advancing to the first full Epoch 2.5 reward cycle boundary...");
        next_block_and_wait(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
        );
        self.wait_for_registered(30);
        debug!("Signers initialized");

        let current_burn_block_height = self
            .running_nodes
            .btc_regtest_controller
            .get_headers_height();
        info!("At burn block height {current_burn_block_height}. Ready to mine the first Epoch 2.5 reward cycle!");
    }

    /// Run the test until the epoch 3 boundary
    pub fn boot_to_epoch_3(&mut self) {
        boot_to_epoch_3_reward_set(
            &self.running_nodes.conf,
            &self.running_nodes.counters.blocks_processed,
            &self.signer_stacks_private_keys,
            &self.signer_stacks_private_keys,
            &mut self.running_nodes.btc_regtest_controller,
            Some(self.num_stacking_cycles),
        );
        info!("Waiting for signer set calculation.");
        // Make sure the signer set is calculated before continuing or signers may not
        // recognize that they are registered signers in the subsequent burn block event
        let reward_cycle = self.get_current_reward_cycle() + 1;
        wait_for(120, || {
            Ok(self
                .stacks_client
                .get_reward_set_signers(reward_cycle)
                .expect("Failed to check if reward set is calculated")
                .map(|reward_set| {
                    debug!("Signer set: {reward_set:?}");
                })
                .is_some())
        })
        .expect("Timed out waiting for reward set calculation");
        info!("Signer set calculated");

        // Manually consume one more block to ensure signers refresh their state
        info!("Waiting for signers to initialize.");
        next_block_and_wait(
            &mut self.running_nodes.btc_regtest_controller,
            &self.running_nodes.counters.blocks_processed,
        );
        self.wait_for_registered(30);
        info!("Signers initialized");

        self.run_until_epoch_3_boundary();
        wait_for(30, || {
            Ok(get_chain_info_opt(&self.running_nodes.conf).is_some())
        })
        .expect("Timed out waiting for network to restart after 3.0 boundary reached");

        // Wait until we see the first block of epoch 3.0.
        // Note, we don't use `nakamoto_blocks_mined` counter, because there
        // could be other miners mining blocks.
        let height_before = get_chain_info(&self.running_nodes.conf).stacks_tip_height;
        info!("Waiting for first Nakamoto block: {}", height_before + 1);
        self.mine_nakamoto_block(Duration::from_secs(30), false);
        wait_for(30, || {
            Ok(get_chain_info(&self.running_nodes.conf).stacks_tip_height > height_before)
        })
        .expect("Timed out waiting for first Nakamoto block after 3.0 boundary");
        info!("Ready to mine Nakamoto blocks!");
    }

    // Only call after already past the epoch 3.0 boundary
    fn mine_and_verify_confirmed_naka_block(
        &mut self,
        timeout: Duration,
        num_signers: usize,
        use_nakamoto_blocks_mined: bool,
    ) {
        info!("------------------------- Try mining one block -------------------------");

        let reward_cycle = self.get_current_reward_cycle();

        self.mine_nakamoto_block(timeout, use_nakamoto_blocks_mined);

        // Verify that the signers accepted the proposed block, sending back a validate ok response
        let proposed_signer_signature_hash = self
            .wait_for_validate_ok_response(timeout)
            .signer_signature_hash;
        let message = proposed_signer_signature_hash.0;

        info!("------------------------- Test Block Signed -------------------------");
        // Verify that the signers signed the proposed block
        let signature = self.wait_for_confirmed_block_v0(&proposed_signer_signature_hash, timeout);

        info!("Got {} signatures", signature.len());

        // NOTE: signature.len() does not need to equal signers.len(); the stacks miner can finish the block
        //  whenever it has crossed the threshold.
        assert!(signature.len() >= num_signers * 7 / 10);
        info!("Verifying signatures against signers for reward cycle {reward_cycle:?}");
        let signers = self.get_reward_set_signers(reward_cycle);

        // Verify that the signers signed the proposed block
        let mut signer_index = 0;
        let mut signature_index = 0;
        let mut signing_keys = HashSet::new();
        let start = Instant::now();
        debug!(
            "Validating {} signatures against {num_signers} signers",
            signature.len()
        );
        let validated = loop {
            // Since we've already checked `signature.len()`, this means we've
            //  validated all the signatures in this loop
            let Some(signature) = signature.get(signature_index) else {
                break true;
            };
            let Some(signer) = signers.get(signer_index) else {
                error!("Failed to validate the mined nakamoto block: ran out of signers to try to validate signatures");
                break false;
            };
            if !signing_keys.insert(signer.signing_key) {
                panic!("Duplicate signing key detected: {:?}", signer.signing_key);
            }
            let stacks_public_key = Secp256k1PublicKey::from_slice(signer.signing_key.as_slice())
                .expect("Failed to convert signing key to StacksPublicKey");
            let valid = stacks_public_key
                .verify(&message, signature)
                .expect("Failed to verify signature");
            if !valid {
                info!(
                    "Failed to verify signature for signer, will attempt to validate without this signer";
                    "signer_pk" => stacks_public_key.to_hex(),
                    "signer_index" => signer_index,
                    "signature_index" => signature_index,
                );
                signer_index += 1;
            } else {
                signer_index += 1;
                signature_index += 1;
            }
            // Shouldn't really ever timeout, but do this in case there is some sort of overflow/underflow happening.
            assert!(
                start.elapsed() < timeout,
                "Timed out waiting to confirm block signatures"
            );
        };

        assert!(validated);
    }

    // Only call after already past the epoch 3.0 boundary
    fn run_until_burnchain_height_nakamoto(
        &mut self,
        timeout: Duration,
        burnchain_height: u64,
        num_signers: usize,
    ) {
        let current_block_height = self
            .running_nodes
            .btc_regtest_controller
            .get_headers_height();
        let total_nmb_blocks_to_mine = burnchain_height.saturating_sub(current_block_height);
        debug!("Mining {total_nmb_blocks_to_mine} Nakamoto block(s) to reach burnchain height {burnchain_height}");
        for _ in 0..total_nmb_blocks_to_mine {
            self.mine_and_verify_confirmed_naka_block(timeout, num_signers, false);
        }
    }

    /// Propose a block to the signers
    fn propose_block(&mut self, block: NakamotoBlock, timeout: Duration) {
        let miners_contract_id = boot_code_id(MINERS_NAME, false);
        let mut session =
            StackerDBSession::new(&self.running_nodes.conf.node.rpc_bind, miners_contract_id);
        let burn_height = self
            .running_nodes
            .btc_regtest_controller
            .get_headers_height();
        let reward_cycle = self.get_current_reward_cycle();
        let signer_signature_hash = block.header.signer_signature_hash();
        let message = SignerMessage::BlockProposal(BlockProposal {
            block,
            burn_height,
            reward_cycle,
            block_proposal_data: BlockProposalData::empty(),
        });
        let miner_sk = self
            .running_nodes
            .conf
            .miner
            .mining_key
            .expect("No mining key");
        // Submit the block proposal to the miner's slot
        let mut accepted = false;
        let mut version = 0;
        let slot_id = MinerSlotID::BlockProposal.to_u8() as u32;
        let start = Instant::now();
        debug!("Proposing block to signers: {signer_signature_hash}");
        while !accepted {
            let mut chunk =
                StackerDBChunkData::new(slot_id * 2, version, message.serialize_to_vec());
            chunk.sign(&miner_sk).expect("Failed to sign message chunk");
            debug!("Produced a signature: {:?}", chunk.sig);
            let result = session.put_chunk(&chunk).expect("Failed to put chunk");
            accepted = result.accepted;
            version += 1;
            debug!("Test Put Chunk ACK: {result:?}");
            assert!(
                start.elapsed() < timeout,
                "Timed out waiting for block proposal to be accepted"
            );
        }
    }
}

/// A test harness for running multiple miners with v0::signers
pub struct MultipleMinerTest {
    signer_test: SignerTest<SpawnedSigner>,
    sender_sk: Secp256k1PrivateKey,
    sender_nonce: u64,
    send_amt: u64,
    send_fee: u64,
    conf_node_2: NeonConfig,
    rl2_thread: thread::JoinHandle<()>,
    rl2_counters: Counters,
    rl2_coord_channels: Arc<Mutex<CoordinatorChannels>>,
    rl2_stopper: Arc<AtomicBool>,
}

impl MultipleMinerTest {
    /// Create a new test harness for running multiple miners with num_signers underlying signers and enough funds to send
    /// num_txs transfer transactions.
    ///
    /// Will partition the signer set so that ~half are listening and using node 1 for RPC and events,
    /// and the rest are using node 2
    pub fn new(num_signers: usize, num_txs: u64) -> MultipleMinerTest {
        Self::new_with_config_modifications(num_signers, num_txs, |_| {}, |_| {}, |_| {})
    }

    /// Create a new test harness for running multiple miners with num_signers underlying signers and enough funds to send
    /// num_txs transfer transactions.
    ///
    /// Will also modify the signer config and the node 1 and node 2 configs with the provided
    /// modifiers. Will partition the signer set so that ~half are listening and using node 1 for RPC and events,
    /// and the rest are using node 2 unless otherwise specified via the signer config modifier.
    pub fn new_with_config_modifications<
        F: FnMut(&mut SignerConfig),
        G: FnMut(&mut NeonConfig),
        H: FnMut(&mut NeonConfig),
    >(
        num_signers: usize,
        num_transfer_txs: u64,
        mut signer_config_modifier: F,
        mut node_1_config_modifier: G,
        mut node_2_config_modifier: H,
    ) -> MultipleMinerTest {
        let sender_sk = Secp256k1PrivateKey::random();
        let sender_addr = tests::to_addr(&sender_sk);
        let send_amt = 1000;
        let send_fee = 180;

        let btc_miner_1_seed = vec![1, 1, 1, 1];
        let btc_miner_2_seed = vec![2, 2, 2, 2];
        let btc_miner_1_pk = Keychain::default(btc_miner_1_seed.clone()).get_pub_key();
        let btc_miner_2_pk = Keychain::default(btc_miner_2_seed.clone()).get_pub_key();

        let node_1_rpc = gen_random_port();
        let node_1_p2p = gen_random_port();
        let node_2_rpc = gen_random_port();
        let node_2_p2p = gen_random_port();

        let localhost = "127.0.0.1";
        let node_1_rpc_bind = format!("{localhost}:{node_1_rpc}");
        let node_2_rpc_bind = format!("{localhost}:{node_2_rpc}");
        let mut node_2_listeners = Vec::new();

        // partition the signer set so that ~half are listening and using node 1 for RPC and events,
        //  and the rest are using node 2
        let signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
            num_signers,
            vec![(sender_addr, (send_amt + send_fee) * num_transfer_txs)],
            |signer_config| {
                let node_host = if signer_config.endpoint.port() % 2 == 0 {
                    &node_1_rpc_bind
                } else {
                    &node_2_rpc_bind
                };
                signer_config.node_host = node_host.to_string();
                signer_config_modifier(signer_config);
            },
            |config| {
                config.node.rpc_bind = format!("{localhost}:{node_1_rpc}");
                config.node.p2p_bind = format!("{localhost}:{node_1_p2p}");
                config.node.data_url = format!("http://{localhost}:{node_1_rpc}");
                config.node.p2p_address = format!("{localhost}:{node_1_p2p}");
                config.miner.wait_on_interim_blocks = Duration::from_secs(5);
                config.node.pox_sync_sample_secs = 30;
                config.burnchain.pox_reward_length = Some(30);

                config.node.seed = btc_miner_1_seed.clone();
                config.node.local_peer_seed = btc_miner_1_seed.clone();
                config.burnchain.local_mining_public_key = Some(btc_miner_1_pk.to_hex());
                config.miner.mining_key = Some(Secp256k1PrivateKey::from_seed(&[1]));

                config.events_observers.retain(|listener| {
                    let Ok(addr) = std::net::SocketAddr::from_str(&listener.endpoint) else {
                        warn!(
                            "Cannot parse {} to a socket, assuming it isn't a signer-listener binding",
                            listener.endpoint
                        );
                        return true;
                    };
                    if addr.port() % 2 == 0 || addr.port() == test_observer::EVENT_OBSERVER_PORT {
                        return true;
                    }
                    node_2_listeners.push(listener.clone());
                    false
                });
                node_1_config_modifier(config);
            },
            Some(vec![btc_miner_1_pk, btc_miner_2_pk]),
            None,
        );
        let conf = signer_test.running_nodes.conf.clone();
        let mut conf_node_2 = conf.clone();
        conf_node_2.node.rpc_bind = format!("{localhost}:{node_2_rpc}");
        conf_node_2.node.p2p_bind = format!("{localhost}:{node_2_p2p}");
        conf_node_2.node.data_url = format!("http://{localhost}:{node_2_rpc}");
        conf_node_2.node.p2p_address = format!("{localhost}:{node_2_p2p}");
        conf_node_2.node.seed = btc_miner_2_seed.clone();
        conf_node_2.burnchain.local_mining_public_key = Some(btc_miner_2_pk.to_hex());
        conf_node_2.node.local_peer_seed = btc_miner_2_seed;
        conf_node_2.miner.mining_key = Some(StacksPrivateKey::from_seed(&[2]));
        conf_node_2.node.miner = true;
        conf_node_2.events_observers.clear();
        conf_node_2.events_observers.extend(node_2_listeners);
        assert!(!conf_node_2.events_observers.is_empty());
        node_2_config_modifier(&mut conf_node_2);

        let node_1_sk = StacksPrivateKey::from_seed(&conf.node.local_peer_seed);
        let node_1_pk = StacksPublicKey::from_private(&node_1_sk);

        conf_node_2.node.working_dir = format!("{}-1", conf_node_2.node.working_dir);

        conf_node_2.node.set_bootstrap_nodes(
            format!("{}@{}", &node_1_pk.to_hex(), conf.node.p2p_bind),
            conf.burnchain.chain_id,
            conf.burnchain.peer_version,
        );

        let mut run_loop_2 = boot_nakamoto::BootRunLoop::new(conf_node_2.clone()).unwrap();
        let rl2_stopper = run_loop_2.get_termination_switch();
        let rl2_coord_channels = run_loop_2.coordinator_channels();
        let rl2_counters = run_loop_2.counters();

        let rl2_thread = thread::Builder::new()
            .name("run_loop_2".into())
            .spawn(move || run_loop_2.start(None, 0))
            .unwrap();

        MultipleMinerTest {
            signer_test,
            sender_sk,
            sender_nonce: 0,
            send_amt,
            send_fee,
            conf_node_2,
            rl2_thread,
            rl2_counters,
            rl2_stopper,
            rl2_coord_channels,
        }
    }

    /// Boot node 1 to epoch 3.0 and wait for node 2 to catch up.
    pub fn boot_to_epoch_3(&mut self) {
        info!(
            "------------------------- Booting Both Miners to Epoch 3.0 -------------------------"
        );

        self.signer_test.boot_to_epoch_3();
        // Use a longer timeout for the miners to advance to epoch 3.0 and so that CI runners don't timeout.
        self.wait_for_chains(600);

        info!("------------------------- Reached Epoch 3.0 -------------------------");
    }

    /// Returns a tuple of the node 1 and node 2 miner private keys respectively
    pub fn get_miner_private_keys(&self) -> (StacksPrivateKey, StacksPrivateKey) {
        (
            self.signer_test
                .running_nodes
                .conf
                .miner
                .mining_key
                .unwrap(),
            self.conf_node_2.miner.mining_key.unwrap(),
        )
    }

    /// Returns a tuple of the node 1 and node 2 miner public keys respectively
    pub fn get_miner_public_keys(&self) -> (StacksPublicKey, StacksPublicKey) {
        let (sk1, sk2) = self.get_miner_private_keys();
        (
            StacksPublicKey::from_private(&sk1),
            StacksPublicKey::from_private(&sk2),
        )
    }

    /// Returns a tuple of the node 1 and node 2 miner private key hashes respectively
    pub fn get_miner_public_key_hashes(&self) -> (Hash160, Hash160) {
        let (pk1, pk2) = self.get_miner_public_keys();
        (
            Hash160::from_node_public_key(&pk1),
            Hash160::from_node_public_key(&pk2),
        )
    }

    /// Returns a tuple of the node 1 and node 2 miner node configs respectively
    pub fn get_node_configs(&self) -> (NeonConfig, NeonConfig) {
        (
            self.signer_test.running_nodes.conf.clone(),
            self.conf_node_2.clone(),
        )
    }

    pub fn btc_regtest_controller_mut(&mut self) -> &mut BitcoinRegtestController {
        &mut self.signer_test.running_nodes.btc_regtest_controller
    }

    /// Mine `nmb_blocks` blocks on the bitcoin regtest chain and wait for the sortition
    /// database to confirm the block.
    pub fn mine_bitcoin_blocks_and_confirm(
        &mut self,
        sortdb: &SortitionDB,
        nmb_blocks: u64,
        timeout_secs: u64,
    ) -> Result<(), String> {
        let burn_block_before = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;

        self.btc_regtest_controller_mut()
            .build_next_block(nmb_blocks);
        wait_for(timeout_secs, || {
            let burn_block = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
                .unwrap()
                .block_height;
            Ok(burn_block >= burn_block_before + nmb_blocks)
        })
    }

    /// Mine `nmb_blocks` blocks on the bitcoin regtest chain and wait for the sortition
    /// database to confirm the block and the test_observer to see the block.
    pub fn mine_bitcoin_blocks_and_confirm_with_test_observer(
        &mut self,
        sortdb: &SortitionDB,
        nmb_blocks: u64,
        timeout_secs: u64,
    ) -> Result<(), String> {
        let blocks_before = test_observer::get_blocks().len();
        let burn_block_before = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;

        self.btc_regtest_controller_mut()
            .build_next_block(nmb_blocks);
        wait_for(timeout_secs, || {
            let burn_block = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
                .unwrap()
                .block_height;
            let blocks = test_observer::get_blocks().len();
            Ok(burn_block >= burn_block_before + nmb_blocks
                && blocks >= blocks_before + nmb_blocks as usize)
        })
    }

    /// Mine a bitcoin block and wait for the sortition database to confirm the block and wait
    /// for a tenure change transaction to be subseqently mined in a stacks block at the appropriate height.
    pub fn mine_bitcoin_block_and_tenure_change_tx(
        &mut self,
        sortdb: &SortitionDB,
        cause: TenureChangeCause,
        timeout_secs: u64,
    ) -> Result<(), String> {
        let start = Instant::now();
        let stacks_height_before = self.get_peer_stacks_tip_height();
        self.mine_bitcoin_blocks_and_confirm(sortdb, 1, timeout_secs)?;
        wait_for_tenure_change_tx(
            timeout_secs.saturating_sub(start.elapsed().as_secs()),
            cause,
            stacks_height_before + 1,
        )
    }

    /// Sends a transfer tx to the stacks node and returns the txid
    pub fn send_transfer_tx(&mut self) -> String {
        let http_origin = format!(
            "http://{}",
            &self.signer_test.running_nodes.conf.node.rpc_bind
        );
        let recipient = PrincipalData::from(StacksAddress::burn_address(false));
        // submit a tx so that the miner will mine an extra block
        let transfer_tx = make_stacks_transfer(
            &self.sender_sk,
            self.sender_nonce,
            self.send_fee,
            self.signer_test.running_nodes.conf.burnchain.chain_id,
            &recipient,
            self.send_amt,
        );
        self.sender_nonce += 1;
        submit_tx(&http_origin, &transfer_tx)
    }

    /// Sends a transfer tx to the stacks node and waits for the stacks node to mine it
    /// Returns the txid of the transfer tx.
    pub fn send_and_mine_transfer_tx(&mut self, timeout_secs: u64) -> Result<String, String> {
        let stacks_height_before = self.get_peer_stacks_tip_height();
        let txid = self.send_transfer_tx();
        wait_for(timeout_secs, || {
            Ok(self.get_peer_stacks_tip_height() > stacks_height_before)
        })?;
        Ok(txid)
    }

    /// Return the Peer Info from node 1
    pub fn get_peer_info(&self) -> PeerInfo {
        self.signer_test.get_peer_info()
    }

    /// Returns the peer info's reported stacks tip height from node 1
    pub fn get_peer_stacks_tip_height(&self) -> u64 {
        self.get_peer_info().stacks_tip_height
    }

    /// Returns the peer stacks tip hash from node 1
    pub fn get_peer_stacks_tip(&self) -> BlockHeaderHash {
        self.get_peer_info().stacks_tip
    }

    /// Ensures that miner 2 submits a commit pointing to the current view reported by the stacks node as expected
    pub fn submit_commit_miner_2(&mut self, sortdb: &SortitionDB) {
        if !self.rl2_counters.naka_skip_commit_op.get() {
            warn!("Miner 2's commit ops were not paused. This may result in no commit being submitted.");
        }
        let burn_height = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;

        let stacks_height_before = self.get_peer_stacks_tip_height();
        let rl2_commits_before = self
            .rl2_counters
            .naka_submitted_commits
            .load(Ordering::SeqCst);

        info!("Unpausing commits from RL2");
        self.rl2_counters.naka_skip_commit_op.set(false);

        info!("Waiting for commits from RL2");
        wait_for(30, || {
            Ok(self
                .rl2_counters
                .naka_submitted_commits
                .load(Ordering::SeqCst)
                > rl2_commits_before
                && self
                    .rl2_counters
                    .naka_submitted_commit_last_burn_height
                    .load(Ordering::SeqCst)
                    >= burn_height
                && self
                    .rl2_counters
                    .naka_submitted_commit_last_stacks_tip
                    .load(Ordering::SeqCst)
                    >= stacks_height_before)
        })
        .expect("Timed out waiting for miner 2 to submit a commit op");

        info!("Pausing commits from RL2");
        self.rl2_counters.naka_skip_commit_op.set(true);
    }

    /// Ensures that miner 1 submits a commit pointing to the current view reported by the stacks node as expected
    pub fn submit_commit_miner_1(&mut self, sortdb: &SortitionDB) {
        if !self
            .signer_test
            .running_nodes
            .counters
            .naka_skip_commit_op
            .get()
        {
            warn!("Miner 1's commit ops were not paused. This may result in no commit being submitted.");
        }
        let burn_height = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;
        let stacks_height_before = self.get_peer_stacks_tip_height();
        let rl1_commits_before = self
            .signer_test
            .running_nodes
            .counters
            .naka_submitted_commits
            .load(Ordering::SeqCst);

        info!("Unpausing commits from RL1");
        self.signer_test
            .running_nodes
            .counters
            .naka_skip_commit_op
            .set(false);

        info!("Waiting for commits from RL1");
        wait_for(30, || {
            Ok(self
                .signer_test
                .running_nodes
                .counters
                .naka_submitted_commits
                .load(Ordering::SeqCst)
                > rl1_commits_before
                && self
                    .signer_test
                    .running_nodes
                    .counters
                    .naka_submitted_commit_last_burn_height
                    .load(Ordering::SeqCst)
                    >= burn_height
                && self
                    .signer_test
                    .running_nodes
                    .counters
                    .naka_submitted_commit_last_stacks_tip
                    .load(Ordering::SeqCst)
                    >= stacks_height_before)
        })
        .expect("Timed out waiting for miner 1 to submit a commit op");

        info!("Pausing commits from RL1");
        self.signer_test
            .running_nodes
            .counters
            .naka_skip_commit_op
            .set(true);
    }

    /// Shutdown the test harness
    pub fn shutdown(self) {
        info!("------------------------- Shutting Down Multiple Miners Test -------------------------");
        self.rl2_coord_channels
            .lock()
            .expect("Mutex poisoned")
            .stop_chains_coordinator();
        self.rl2_stopper.store(false, Ordering::SeqCst);
        self.rl2_thread.join().unwrap();
        self.signer_test.shutdown();
    }

    /// Wait for both miners to have the same stacks tip height
    pub fn wait_for_chains(&self, timeout_secs: u64) {
        wait_for(timeout_secs, || {
            let Some(node_1_info) = get_chain_info_opt(&self.signer_test.running_nodes.conf) else {
                return Ok(false);
            };
            let Some(node_2_info) = get_chain_info_opt(&self.conf_node_2) else {
                return Ok(false);
            };
            Ok(
                node_1_info.stacks_tip_height == node_2_info.stacks_tip_height
                    && node_1_info.burn_block_height == node_2_info.burn_block_height,
            )
        })
        .expect("Timed out waiting for boostrapped node to catch up to the miner");
    }
}

/// Returns whether the last block in the test observer contains a tenure change
/// transaction with the given cause.
fn last_block_contains_tenure_change_tx(cause: TenureChangeCause) -> bool {
    let blocks = test_observer::get_blocks();
    let last_block = &blocks.last().unwrap();
    let transactions = last_block["transactions"].as_array().unwrap();
    let tx = transactions.first().expect("No transactions in block");
    let raw_tx = tx["raw_tx"].as_str().unwrap();
    let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
    let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
    match &parsed.payload {
        TransactionPayload::TenureChange(payload) if payload.cause == cause => {
            info!("Found tenure change transaction: {parsed:?}");
            true
        }
        _ => false,
    }
}

/// Asserts that the last block in the test observer contains a tenure change with the given cause.
fn verify_last_block_contains_tenure_change_tx(cause: TenureChangeCause) {
    assert!(last_block_contains_tenure_change_tx(cause));
}

/// Verifies that the tip of the sortition database was won by the provided miner public key hash
fn verify_sortition_winner(sortdb: &SortitionDB, miner_pkh: &Hash160) {
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    assert!(tip.sortition);
    assert_eq!(&tip.miner_pk_hash.unwrap(), miner_pkh);
}

/// Waits for a tenure change transaction to be observed in the test_observer at the expected height
fn wait_for_tenure_change_tx(
    timeout_secs: u64,
    cause: TenureChangeCause,
    expected_height: u64,
) -> Result<(), String> {
    wait_for(timeout_secs, || {
        let blocks = test_observer::get_blocks();
        for block in blocks {
            let height = block["block_height"].as_u64().unwrap();
            if height == expected_height {
                let transactions = block["transactions"].as_array().unwrap();
                for tx in transactions {
                    let raw_tx = tx["raw_tx"].as_str().unwrap();
                    let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
                    let parsed =
                        StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
                    if let TransactionPayload::TenureChange(payload) = &parsed.payload {
                        if payload.cause == cause {
                            info!("Found tenure change transaction: {parsed:?}");
                            return Ok(true);
                        }
                    }
                }
            }
        }
        Ok(false)
    })
}

/// Waits for a block proposal to be observed in the test_observer stackerdb chunks at the expected height
/// and signed by the expected miner
fn wait_for_block_proposal(
    timeout_secs: u64,
    expected_height: u64,
    expected_miner: &StacksPublicKey,
) -> Result<NakamotoBlock, String> {
    let mut proposed_block = None;
    wait_for(timeout_secs, || {
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            let SignerMessage::BlockProposal(proposal) = message else {
                continue;
            };
            let miner_pk = proposal.block.header.recover_miner_pk().unwrap();
            let block_stacks_height = proposal.block.header.chain_length;
            if block_stacks_height != expected_height {
                continue;
            }
            if &miner_pk == expected_miner {
                proposed_block = Some(proposal.block);
                return Ok(true);
            }
        }
        Ok(false)
    })?;
    proposed_block.ok_or_else(|| "Failed to find block proposal".to_string())
}

/// Waits for a BlockPushed to be observed in the test_observer stackerdb chunks for a block
/// with the provided signer signature hash
fn wait_for_block_pushed(
    timeout_secs: u64,
    block_signer_signature_hash: Sha512Trunc256Sum,
) -> Result<NakamotoBlock, String> {
    let mut block = None;
    wait_for(timeout_secs, || {
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            if let SignerMessage::BlockPushed(pushed_block) = message {
                if pushed_block.header.signer_signature_hash() == block_signer_signature_hash {
                    block = Some(pushed_block);
                    return Ok(true);
                }
            }
        }
        Ok(false)
    })?;
    block.ok_or_else(|| "Failed to find block pushed".to_string())
}

/// Waits for a block with the provided expected height to be proposed and pushed by the miner with the provided public key.
fn wait_for_block_pushed_by_miner_key(
    timeout_secs: u64,
    expected_height: u64,
    miner_key: &StacksPublicKey,
) -> Result<NakamotoBlock, String> {
    let block_proposed = wait_for_block_proposal(timeout_secs, expected_height, miner_key)?;
    wait_for_block_pushed(timeout_secs, block_proposed.header.signer_signature_hash())
}

/// Waits for >30% of num_signers block rejection to be observed in the test_observer stackerdb chunks for a block
/// with the provided signer signature hash
fn wait_for_block_global_rejection(
    timeout_secs: u64,
    block_signer_signature_hash: Sha512Trunc256Sum,
    num_signers: usize,
) -> Result<(), String> {
    let mut found_rejections = HashSet::new();
    wait_for(timeout_secs, || {
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            if let SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                signer_signature_hash,
                signature,
                ..
            })) = message
            {
                if signer_signature_hash == block_signer_signature_hash {
                    found_rejections.insert(signature);
                }
            }
        }
        Ok(found_rejections.len() >= num_signers * 3 / 10)
    })
}

/// Waits for the provided number of block rejections to be observed in the test_observer stackerdb chunks for a block
/// with the provided signer signature hash
fn wait_for_block_rejections(
    timeout_secs: u64,
    block_signer_signature_hash: Sha512Trunc256Sum,
    num_rejections: usize,
) -> Result<(), String> {
    let mut found_rejections = HashSet::new();
    wait_for(timeout_secs, || {
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            if let SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                signer_signature_hash,
                signature,
                ..
            })) = message
            {
                if signer_signature_hash == block_signer_signature_hash {
                    found_rejections.insert(signature);
                }
            }
        }
        Ok(found_rejections.len() == num_rejections)
    })
}

/// Waits for >70% of the provided signers to send an acceptance for a block
/// with the provided signer signature hash
pub fn wait_for_block_global_acceptance_from_signers(
    timeout_secs: u64,
    signer_signature_hash: &Sha512Trunc256Sum,
    expected_signers: &[StacksPublicKey],
) -> Result<(), String> {
    // Make sure that at least 70% of signers accepted the block proposal
    wait_for(timeout_secs, || {
        let signatures = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                    .expect("Failed to deserialize SignerMessage");
                if let SignerMessage::BlockResponse(BlockResponse::Accepted(accepted)) = message {
                    if accepted.signer_signature_hash == *signer_signature_hash
                        && expected_signers.iter().any(|pk| {
                            pk.verify(accepted.signer_signature_hash.bits(), &accepted.signature)
                                .expect("Failed to verify signature")
                        })
                    {
                        return Some(accepted.signature);
                    }
                }
                None
            })
            .collect::<HashSet<_>>();
        Ok(signatures.len() > expected_signers.len() * 7 / 10)
    })
}

/// Waits for all of the provided signers to send an acceptance for a block
/// with the provided signer signature hash
pub fn wait_for_block_acceptance_from_signers(
    timeout_secs: u64,
    signer_signature_hash: &Sha512Trunc256Sum,
    expected_signers: &[StacksPublicKey],
) -> Result<Vec<BlockAccepted>, String> {
    let mut result = vec![];
    wait_for(timeout_secs, || {
        let signatures = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                    .expect("Failed to deserialize SignerMessage");
                if let SignerMessage::BlockResponse(BlockResponse::Accepted(accepted)) = message {
                    if accepted.signer_signature_hash == *signer_signature_hash
                        && expected_signers.iter().any(|pk| {
                            pk.verify(accepted.signer_signature_hash.bits(), &accepted.signature)
                                .expect("Failed to verify signature")
                        })
                    {
                        return Some((accepted.signature, accepted));
                    }
                }
                None
            })
            .collect::<HashMap<_, _>>();
        if signatures.len() == expected_signers.len() {
            result = signatures.values().cloned().collect();
            return Ok(true);
        }
        Ok(false)
    })?;
    Ok(result)
}

/// Waits for all of the provided signers to send a rejection for a block
/// with the provided signer signature hash
pub fn wait_for_block_rejections_from_signers(
    timeout_secs: u64,
    expected_signers: &[StacksPublicKey],
) -> Result<Vec<BlockRejection>, String> {
    let mut result = Vec::new();
    wait_for(timeout_secs, || {
        let stackerdb_events = test_observer::get_stackerdb_chunks();
        let block_rejections: HashMap<_, _> = stackerdb_events
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                    .expect("Failed to deserialize SignerMessage");
                match message {
                    SignerMessage::BlockResponse(BlockResponse::Rejected(rejection)) => {
                        let rejected_pubkey = rejection
                            .recover_public_key()
                            .expect("Failed to recover public key from rejection");
                        if expected_signers.contains(&rejected_pubkey) {
                            Some((rejected_pubkey, rejection))
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            })
            .collect();
        if block_rejections.len() == expected_signers.len() {
            result = block_rejections.values().cloned().collect();
            return Ok(true);
        }
        Ok(false)
    })?;
    Ok(result)
}

#[test]
#[ignore]
/// Test that a signer can respond to an invalid block proposal
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
///
/// Test Execution:
/// The stacks node is advanced to epoch 3.0 reward set calculation to ensure the signer set is determined.
/// An invalid block proposal is forcibly written to the miner's slot to simulate the miner proposing a block.
/// The signers process the invalid block by first verifying it against the stacks node block proposal endpoint.
/// The signer that submitted the initial block validation request, should issue a  broadcast a rejection of the
/// miner's proposed block back to the respective .signers-XXX-YYY contract.
///
/// Test Assertion:
/// Each signer successfully rejects the invalid block proposal.
fn block_proposal_rejection() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(num_signers, vec![]);
    signer_test.boot_to_epoch_3();
    let short_timeout = Duration::from_secs(30);

    info!("------------------------- Send Block Proposal To Signers -------------------------");
    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        block_proposal_timeout: Duration::from_secs(100),
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    block.header.timestamp = get_epoch_time_secs();

    // First propose a block to the signers that does not have the correct consensus hash or BitVec. This should be rejected BEFORE
    // the block is submitted to the node for validation.
    let block_signer_signature_hash_1 = block.header.signer_signature_hash();
    signer_test.propose_block(block.clone(), short_timeout);

    // Wait for the first block to be mined successfully so we have the most up to date sortition view
    signer_test.wait_for_validate_ok_response(short_timeout);

    // Propose a block to the signers that passes initial checks but will be rejected by the stacks node
    let view = SortitionsView::fetch_view(proposal_conf, &signer_test.stacks_client).unwrap();
    block.header.pox_treatment = BitVec::ones(1).unwrap();
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.header.chain_length = 35; // We have mined 35 blocks so far.

    let block_signer_signature_hash_2 = block.header.signer_signature_hash();
    signer_test.propose_block(block, short_timeout);

    info!("------------------------- Test Block Proposal Rejected -------------------------");
    // Verify the signers rejected the second block via the endpoint
    let reject =
        signer_test.wait_for_validate_reject_response(short_timeout, block_signer_signature_hash_2);
    assert!(matches!(
        reject.reason_code,
        ValidateRejectCode::InvalidBlock
    ));

    let start_polling = Instant::now();
    let mut found_signer_signature_hash_1 = false;
    let mut found_signer_signature_hash_2 = false;
    while !found_signer_signature_hash_1 && !found_signer_signature_hash_2 {
        std::thread::sleep(Duration::from_secs(1));
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            if let SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                reason: _reason,
                reason_code,
                signer_signature_hash,
                response_data,
                ..
            })) = message
            {
                if signer_signature_hash == block_signer_signature_hash_1 {
                    found_signer_signature_hash_1 = true;
                    assert_eq!(reason_code, RejectCode::SortitionViewMismatch,);
                    assert_eq!(response_data.reject_reason, RejectReason::InvalidBitvec);
                } else if signer_signature_hash == block_signer_signature_hash_2 {
                    found_signer_signature_hash_2 = true;
                    assert!(matches!(
                        reason_code,
                        RejectCode::ValidationFailed(ValidateRejectCode::InvalidBlock)
                    ));
                } else {
                    continue;
                }
            } else {
                continue;
            }
        }
        assert!(
            start_polling.elapsed() <= short_timeout,
            "Timed out after waiting for response from signer"
        );
    }
    signer_test.shutdown();
}

// Basic test to ensure that miners are able to gather block responses
// from signers and create blocks.
#[test]
#[ignore]
fn miner_gather_signatures() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    // Disable p2p broadcast of the nakamoto blocks, so that we rely
    //  on the signer's using StackerDB to get pushed blocks
    nakamoto_node::miner::TEST_P2P_BROADCAST_SKIP.set(true);

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(num_signers, vec![]);
    let timeout = Duration::from_secs(30);

    signer_test.boot_to_epoch_3();

    info!("------------------------- Test Mine and Verify Confirmed Nakamoto Block -------------------------");
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);

    // Test prometheus metrics response
    #[cfg(feature = "monitoring_prom")]
    {
        wait_for(30, || {
            let metrics_response = signer_test.get_signer_metrics();

            // Because 5 signers are running in the same process, the prometheus metrics
            // are incremented once for every signer. This is why we expect the metric to be
            // `10`, even though there are only two blocks proposed.
            let expected_result_1 =
                format!("stacks_signer_block_proposals_received {}", num_signers * 2);
            let expected_result_2 = format!(
                "stacks_signer_block_responses_sent{{response_type=\"accepted\"}} {}",
                num_signers * 2
            );
            Ok(metrics_response.contains(&expected_result_1)
                && metrics_response.contains(&expected_result_2))
        })
        .expect("Failed to advance prometheus metrics");
    }
}

#[test]
#[ignore]
/// Test that signers can handle a transition between Nakamoto reward cycles
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 2 full Nakamoto reward cycles, sending blocks to observing signers to sign and return.
///
/// Test Assertion:
/// All signers sign all blocks successfully.
/// The chain advances 2 full reward cycles.
fn mine_2_nakamoto_reward_cycles() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let nmb_reward_cycles = 2;
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(num_signers, vec![]);
    let timeout = Duration::from_secs(200);
    signer_test.boot_to_epoch_3();
    let curr_reward_cycle = signer_test.get_current_reward_cycle();
    // Mine 2 full Nakamoto reward cycles (epoch 3 starts in the middle of one, hence the + 1)
    let next_reward_cycle = curr_reward_cycle.saturating_add(1);
    let final_reward_cycle = next_reward_cycle.saturating_add(nmb_reward_cycles);
    let final_reward_cycle_height_boundary = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(final_reward_cycle)
        .saturating_sub(1);

    info!("------------------------- Test Mine 2 Nakamoto Reward Cycles -------------------------");
    signer_test.run_until_burnchain_height_nakamoto(
        timeout,
        final_reward_cycle_height_boundary,
        num_signers,
    );

    let current_burnchain_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height();
    assert_eq!(current_burnchain_height, final_reward_cycle_height_boundary);
    signer_test.shutdown();
}

#[test]
#[ignore]
fn forked_tenure_invalid() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let result = forked_tenure_testing(Duration::from_secs(5), Duration::from_secs(7), false);

    assert_ne!(
        result.tip_b.index_block_hash(),
        result.tip_a.index_block_hash()
    );
    assert_eq!(
        result.tip_b.index_block_hash(),
        result.tip_c.index_block_hash()
    );
    assert_ne!(result.tip_c, result.tip_a);

    // Block B was built atop block A
    assert_eq!(
        result.tip_b.stacks_block_height,
        result.tip_a.stacks_block_height + 1
    );
    assert_eq!(
        result.mined_b.parent_block_id,
        result.tip_a.index_block_hash().to_string()
    );

    // Block C was built AFTER Block B was built, but BEFORE it was broadcasted, so it should be built off of Block A
    assert_eq!(
        result.mined_c.parent_block_id,
        result.tip_a.index_block_hash().to_string()
    );
    assert_ne!(
        result
            .tip_c
            .anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .signer_signature_hash(),
        result.mined_c.signer_signature_hash,
        "Mined block during tenure C should not have become the chain tip"
    );

    assert!(result.tip_c_2.is_none());
    assert!(result.mined_c_2.is_none());

    // Tenure D should continue progress
    assert_ne!(result.tip_c, result.tip_d);
    assert_ne!(
        result.tip_b.index_block_hash(),
        result.tip_d.index_block_hash()
    );
    assert_ne!(result.tip_a, result.tip_d);

    // Tenure D builds off of Tenure B
    assert_eq!(
        result.tip_d.stacks_block_height,
        result.tip_b.stacks_block_height + 1,
    );
    assert_eq!(
        result.mined_d.parent_block_id,
        result.tip_b.index_block_hash().to_string()
    );
}

#[test]
#[ignore]
fn forked_tenure_okay() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let result = forked_tenure_testing(Duration::from_secs(360), Duration::from_secs(0), true);

    assert_ne!(result.tip_b, result.tip_a);
    assert_ne!(result.tip_b, result.tip_c);
    assert_ne!(result.tip_c, result.tip_a);

    // Block B was built atop block A
    assert_eq!(
        result.tip_b.stacks_block_height,
        result.tip_a.stacks_block_height + 1
    );
    assert_eq!(
        result.mined_b.parent_block_id,
        result.tip_a.index_block_hash().to_string()
    );

    // Block C was built AFTER Block B was built, but BEFORE it was broadcasted, so it should be built off of Block A
    assert_eq!(
        result.tip_c.stacks_block_height,
        result.tip_a.stacks_block_height + 1
    );
    assert_eq!(
        result.mined_c.parent_block_id,
        result.tip_a.index_block_hash().to_string()
    );

    let tenure_c_2 = result.tip_c_2.unwrap();
    assert_ne!(result.tip_c, tenure_c_2);
    assert_ne!(tenure_c_2, result.tip_d);
    assert_ne!(result.tip_c, result.tip_d);

    // Second block of tenure C builds off of block C
    assert_eq!(
        tenure_c_2.stacks_block_height,
        result.tip_c.stacks_block_height + 1,
    );
    assert_eq!(
        result.mined_c_2.unwrap().parent_block_id,
        result.tip_c.index_block_hash().to_string()
    );

    // Tenure D builds off of the second block of tenure C
    assert_eq!(
        result.tip_d.stacks_block_height,
        tenure_c_2.stacks_block_height + 1,
    );
    assert_eq!(
        result.mined_d.parent_block_id,
        tenure_c_2.index_block_hash().to_string()
    );
}

struct TenureForkingResult {
    tip_a: StacksHeaderInfo,
    tip_b: StacksHeaderInfo,
    tip_c: StacksHeaderInfo,
    tip_c_2: Option<StacksHeaderInfo>,
    tip_d: StacksHeaderInfo,
    mined_b: MinedNakamotoBlockEvent,
    mined_c: MinedNakamotoBlockEvent,
    mined_c_2: Option<MinedNakamotoBlockEvent>,
    mined_d: MinedNakamotoBlockEvent,
}

#[test]
#[ignore]
/// Test to make sure that the signers are capable of reloading their reward set
///  if the stacks-node doesn't have it available at the first block of a prepare phase (e.g., if there was no block)
fn reloads_signer_set_in() {
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_amt + send_fee)]);

    setup_epoch_3_reward_set(
        &signer_test.running_nodes.conf,
        &signer_test.running_nodes.counters.blocks_processed,
        &signer_test.signer_stacks_private_keys,
        &signer_test.signer_stacks_private_keys,
        &mut signer_test.running_nodes.btc_regtest_controller,
        Some(signer_test.num_stacking_cycles),
    );

    let naka_conf = &signer_test.running_nodes.conf;
    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let reward_cycle_len = naka_conf.get_burnchain().pox_constants.reward_cycle_length as u64;
    let prepare_phase_len = naka_conf.get_burnchain().pox_constants.prepare_length as u64;

    let epoch_3_start_height = epoch_3.start_height;
    assert!(
        epoch_3_start_height > 0,
        "Epoch 3.0 start height must be greater than 0"
    );
    let epoch_3_reward_cycle_boundary =
        epoch_3_start_height.saturating_sub(epoch_3_start_height % reward_cycle_len);
    let before_epoch_3_reward_set_calculation =
        epoch_3_reward_cycle_boundary.saturating_sub(prepare_phase_len);
    run_until_burnchain_height(
        &mut signer_test.running_nodes.btc_regtest_controller,
        &signer_test.running_nodes.counters.blocks_processed,
        before_epoch_3_reward_set_calculation,
        naka_conf,
    );

    info!("Waiting for signer set calculation.");
    let short_timeout = Duration::from_secs(30);
    // Make sure the signer set is calculated before continuing or signers may not
    // recognize that they are registered signers in the subsequent burn block event
    let reward_cycle = signer_test.get_current_reward_cycle() + 1;
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);
    wait_for(short_timeout.as_secs(), || {
        let reward_set = match signer_test
            .stacks_client
            .get_reward_set_signers(reward_cycle)
        {
            Ok(x) => x,
            Err(e) => {
                warn!("Failed to check if reward set is calculated yet: {e:?}. Will try again");
                return Ok(false);
            }
        };
        if let Some(ref set) = reward_set {
            info!("Signer set: {set:?}");
        }
        Ok(reward_set.is_some())
    })
    .expect("Timed out waiting for reward set to be calculated");
    info!("Signer set calculated");

    // Manually consume one more block to ensure signers refresh their state
    info!("Waiting for signers to initialize.");
    next_block_and_wait(
        &mut signer_test.running_nodes.btc_regtest_controller,
        &signer_test.running_nodes.counters.blocks_processed,
    );
    signer_test.wait_for_registered(30);
    info!("Signers initialized");

    signer_test.run_until_epoch_3_boundary();

    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();

    info!("Waiting 1 burnchain block for miner VRF key confirmation");
    // Wait one block to confirm the VRF register, wait until a block commit is submitted
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            Ok(commits_count >= 1)
        },
    )
    .unwrap();
    info!("Ready to mine Nakamoto blocks!");

    info!("------------------------- Reached Epoch 3.0 -------------------------");
    signer_test.shutdown();
}

/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// Miner A mines a regular tenure, its last block being block a_x.
/// Miner B starts its tenure, Miner B produces a Stacks block b_0, but miner C submits its block commit before b_0 is broadcasted.
/// Bitcoin block C, containing Miner C's block commit, is mined BEFORE miner C has a chance to update their block commit with b_0's information.
/// This test asserts:
///  * tenure C ignores b_0, and correctly builds off of block a_x.
fn forked_tenure_testing(
    proposal_limit: Duration,
    post_btc_block_pause: Duration,
    expect_tenure_c: bool,
) -> TenureForkingResult {
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            // make the duration long enough that the reorg attempt will definitely be accepted
            config.first_proposal_burn_block_timing = proposal_limit;
            // don't allow signers to post signed blocks (limits the amount of fault injection we
            // need)
            TEST_SKIP_BLOCK_BROADCAST.set(true);
        },
        |config| {
            config.miner.tenure_cost_limit_per_block_percentage = None;
        },
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();
    sleep_ms(1000);
    info!("------------------------- Reached Epoch 3.0 -------------------------");

    let naka_conf = signer_test.running_nodes.conf.clone();
    let miner_sk = naka_conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let Counters {
        naka_submitted_commits: commits_submitted,
        naka_mined_blocks: mined_blocks,
        naka_proposed_blocks: proposed_blocks,
        naka_rejected_blocks: rejected_blocks,
        naka_skip_commit_op: skip_commit_op,
        ..
    } = signer_test.running_nodes.counters.clone();

    let coord_channel = signer_test.running_nodes.coord_channel.clone();
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    info!("Starting Tenure A.");
    // In the next block, the miner should win the tenure and submit a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);

    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            let blocks_count = mined_blocks.load(Ordering::SeqCst);
            let blocks_processed = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            Ok(commits_count > commits_before
                && blocks_count > blocks_before
                && blocks_processed > blocks_processed_before)
        },
    )
    .unwrap();

    sleep_ms(1000);

    let tip_a = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    // For the next tenure, submit the commit op but do not allow any stacks blocks to be broadcasted
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);
    TEST_BLOCK_ANNOUNCE_STALL.set(true);

    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let commits_before = commits_submitted.load(Ordering::SeqCst);

    info!("Starting Tenure B.");
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    info!("Commit op is submitted; unpause tenure B's block");

    // Unpause the broadcast of Tenure B's block, do not submit commits.
    // However, do not allow B to be processed just yet
    skip_commit_op.set(true);
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Wait for a stacks block to be broadcasted
    let start_time = Instant::now();
    while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
        assert!(
            start_time.elapsed() < Duration::from_secs(30),
            "FAIL: Test timed out while waiting for block production",
        );
        thread::sleep(Duration::from_secs(1));
    }

    info!("Tenure B broadcasted a block. Wait {post_btc_block_pause:?}, issue the next bitcoin block, and un-stall block commits.");
    thread::sleep(post_btc_block_pause);

    // the block will be stored, not processed, so load it out of staging
    let tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
        .expect("Failed to get sortition tip");

    let tip_b_block = chainstate
        .nakamoto_blocks_db()
        .get_nakamoto_tenure_start_blocks(&tip_sn.consensus_hash)
        .unwrap()
        .first()
        .cloned()
        .unwrap();

    // synthesize a StacksHeaderInfo from this unprocessed block
    let tip_b = StacksHeaderInfo {
        anchored_header: StacksBlockHeaderTypes::Nakamoto(tip_b_block.header.clone()),
        microblock_tail: None,
        stacks_block_height: tip_b_block.header.chain_length,
        index_root: TrieHash([0x00; 32]), // we can't know this yet since the block hasn't been processed
        consensus_hash: tip_b_block.header.consensus_hash,
        burn_header_hash: tip_sn.burn_header_hash,
        burn_header_height: tip_sn.block_height as u32,
        burn_header_timestamp: tip_sn.burn_header_timestamp,
        anchored_block_size: tip_b_block.serialize_to_vec().len() as u64,
        burn_view: Some(tip_b_block.header.consensus_hash),
    };

    let blocks = test_observer::get_mined_nakamoto_blocks();
    let mined_b = blocks.last().unwrap().clone();

    // Block B was built atop block A
    assert_eq!(tip_b.stacks_block_height, tip_a.stacks_block_height + 1);
    assert_eq!(
        mined_b.parent_block_id,
        tip_a.index_block_hash().to_string()
    );
    assert_ne!(tip_b, tip_a);

    if !expect_tenure_c {
        // allow B to process, so it'll be distinct from C
        TEST_BLOCK_ANNOUNCE_STALL.set(false);
        sleep_ms(1000);
    }

    info!("Starting Tenure C.");

    // Submit a block commit op for tenure C
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = if expect_tenure_c {
        mined_blocks.load(Ordering::SeqCst)
    } else {
        proposed_blocks.load(Ordering::SeqCst)
    };
    let rejected_before = rejected_blocks.load(Ordering::SeqCst);
    skip_commit_op.set(false);

    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            if commits_count > commits_before {
                // now allow block B to process if it hasn't already.
                TEST_BLOCK_ANNOUNCE_STALL.set(false);
            }
            let rejected_count = rejected_blocks.load(Ordering::SeqCst);
            let (blocks_count, rbf_count, has_reject_count) = if expect_tenure_c {
                // if tenure C is going to be canonical, then we expect the miner to RBF its commit
                // once (i.e. for the block it mines and gets signed), and we expect zero
                // rejections.
                (mined_blocks.load(Ordering::SeqCst), 1, true)
            } else {
                // if tenure C is NOT going to be canonical, then we expect no RBFs (since the
                // miner can't get its block signed), and we expect at least one rejection
                (
                    proposed_blocks.load(Ordering::SeqCst),
                    0,
                    rejected_count > rejected_before,
                )
            };

            Ok(commits_count > commits_before + rbf_count
                && blocks_count > blocks_before
                && has_reject_count)
        },
    )
    .unwrap_or_else(|_| {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let rejected_count = rejected_blocks.load(Ordering::SeqCst);
        // see above for comments
        let (blocks_count, rbf_count, has_reject_count) = if expect_tenure_c {
            (mined_blocks.load(Ordering::SeqCst), 1, true)
        } else {
            (
                proposed_blocks.load(Ordering::SeqCst),
                0,
                rejected_count > rejected_before,
            )
        };
        error!("Tenure C failed to produce a block";
            "commits_count" => commits_count,
            "commits_before" => commits_before,
            "rbf_count" => rbf_count as u64,
            "blocks_count" => blocks_count,
            "blocks_before" => blocks_before,
            "rejected_count" => rejected_count,
            "rejected_before" => rejected_before,
            "has_reject_count" => has_reject_count,
        );
        panic!();
    });

    // allow blocks B and C to be processed
    sleep_ms(1000);

    info!("Tenure C produced (or proposed) a block!");
    let tip_c = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let blocks = test_observer::get_mined_nakamoto_blocks();
    let mined_c = blocks.last().unwrap().clone();

    if expect_tenure_c {
        assert_ne!(tip_b.index_block_hash(), tip_c.index_block_hash());
    } else {
        assert_eq!(tip_b.index_block_hash(), tip_c.index_block_hash());
    }
    assert_ne!(tip_c, tip_a);

    let (tip_c_2, mined_c_2) = if !expect_tenure_c {
        (None, None)
    } else {
        // Now let's produce a second block for tenure C and ensure it builds off of block C.
        let blocks_before = mined_blocks.load(Ordering::SeqCst);
        let start_time = Instant::now();
        // submit a tx so that the miner will mine an extra block
        let sender_nonce = 0;
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            sender_nonce,
            send_fee,
            naka_conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        let tx = submit_tx(&http_origin, &transfer_tx);
        info!("Submitted tx {tx} in Tenure C to mine a second block");
        while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
            assert!(
                start_time.elapsed() < Duration::from_secs(30),
                "FAIL: Test timed out while waiting for block production",
            );
            thread::sleep(Duration::from_secs(1));
        }

        // give C's second block a moment to process
        sleep_ms(1000);

        info!("Tenure C produced a second block!");

        let block_2_tenure_c =
            NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
                .unwrap()
                .unwrap();
        let blocks = test_observer::get_mined_nakamoto_blocks();
        let block_2_c = blocks.last().cloned().unwrap();
        (Some(block_2_tenure_c), Some(block_2_c))
    };

    // allow block C2 to be processed
    sleep_ms(1000);

    info!("Starting Tenure D.");

    // Submit a block commit op for tenure D and mine a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            let blocks_count = mined_blocks.load(Ordering::SeqCst);
            Ok(commits_count > commits_before && blocks_count > blocks_before)
        },
    )
    .unwrap();

    // allow block D to be processed
    sleep_ms(1000);

    let tip_d = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let mined_d = blocks.last().unwrap().clone();
    signer_test.shutdown();
    TenureForkingResult {
        tip_a,
        tip_b,
        tip_c,
        tip_c_2,
        tip_d,
        mined_b,
        mined_c,
        mined_c_2,
        mined_d,
    }
}

#[test]
#[ignore]
fn bitcoind_forking_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |_| {},
        |node_config| {
            let epochs = node_config.burnchain.epochs.as_mut().unwrap();
            epochs[StacksEpochId::Epoch30].end_height = 3_015;
            epochs[StacksEpochId::Epoch31].start_height = 3_015;
        },
        None,
        None,
    );
    let conf = signer_test.running_nodes.conf.clone();
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let miner_address = Keychain::default(conf.node.seed.clone())
        .origin_address(conf.is_mainnet())
        .unwrap();
    let miner_pk = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_mining_pubkey()
        .as_deref()
        .map(Secp256k1PublicKey::from_hex)
        .unwrap()
        .unwrap();

    let get_unconfirmed_commit_data = |btc_controller: &mut BitcoinRegtestController| {
        let unconfirmed_utxo = btc_controller
            .get_all_utxos(&miner_pk)
            .into_iter()
            .find(|utxo| utxo.confirmations == 0)?;
        let unconfirmed_txid = Txid::from_bitcoin_tx_hash(&unconfirmed_utxo.txid);
        let unconfirmed_tx = btc_controller.get_raw_transaction(&unconfirmed_txid);
        let unconfirmed_tx_opreturn_bytes = unconfirmed_tx.output[0].script_pubkey.as_bytes();
        info!(
            "Unconfirmed tx bytes: {}",
            stacks::util::hash::to_hex(unconfirmed_tx_opreturn_bytes)
        );
        let data = LeaderBlockCommitOp::parse_data(
            &unconfirmed_tx_opreturn_bytes[unconfirmed_tx_opreturn_bytes.len() - 77..],
        )
        .unwrap();
        Some(data)
    };

    signer_test.boot_to_epoch_3();
    info!("------------------------- Reached Epoch 3.0 -------------------------");
    let pre_epoch_3_nonce = get_account(&http_origin, &miner_address).nonce;
    let pre_fork_tenures = 10;

    for i in 0..pre_fork_tenures {
        info!("Mining pre-fork tenure {} of {pre_fork_tenures}", i + 1);
        signer_test.mine_nakamoto_block(Duration::from_secs(30), true);
    }

    let pre_fork_1_nonce = get_account(&http_origin, &miner_address).nonce;

    assert_eq!(pre_fork_1_nonce, pre_epoch_3_nonce + 2 * pre_fork_tenures);

    info!("------------------------- Triggering Bitcoin Fork -------------------------");

    let burn_block_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
    let burn_header_hash_to_fork = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_block_hash(burn_block_height);
    signer_test
        .running_nodes
        .btc_regtest_controller
        .invalidate_block(&burn_header_hash_to_fork);
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);

    info!("Wait for block off of shallow fork");

    TEST_MINE_STALL.set(true);

    let submitted_commits = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();

    // we need to mine some blocks to get back to being considered a frequent miner
    for i in 0..3 {
        let current_burn_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
        info!(
            "Mining block #{i} to be considered a frequent miner";
            "current_burn_height" => current_burn_height,
        );
        let commits_count = submitted_commits.load(Ordering::SeqCst);
        next_block_and_controller(
            &mut signer_test.running_nodes.btc_regtest_controller,
            60,
            |btc_controller| {
                let commits_submitted = submitted_commits
                    .load(Ordering::SeqCst);
                if commits_submitted <= commits_count {
                    // wait until a commit was submitted
                    return Ok(false)
                }
                let Some(payload) = get_unconfirmed_commit_data(btc_controller) else {
                    warn!("Commit submitted, but bitcoin doesn't see it in the unconfirmed UTXO set, will try to wait.");
                    return Ok(false)
                };
                let burn_parent_modulus = payload.burn_parent_modulus;
                let current_modulus = u8::try_from((current_burn_height + 1) % 5).unwrap();
                info!(
                    "Ongoing Commit Operation check";
                    "burn_parent_modulus" => burn_parent_modulus,
                    "current_modulus" => current_modulus,
                    "payload" => ?payload,
                );
                Ok(burn_parent_modulus == current_modulus)
            },
        )
        .unwrap();
    }

    let post_fork_1_nonce = get_account(&http_origin, &miner_address).nonce;

    // We should have forked 1 block (-2 nonces)
    assert_eq!(post_fork_1_nonce, pre_fork_1_nonce - 2);

    TEST_MINE_STALL.set(false);
    for i in 0..5 {
        info!("Mining post-fork tenure {} of 5", i + 1);
        signer_test.mine_nakamoto_block(Duration::from_secs(30), true);
    }

    let pre_fork_2_nonce = get_account(&http_origin, &miner_address).nonce;
    assert_eq!(pre_fork_2_nonce, post_fork_1_nonce + 2 * 5);

    info!(
        "New chain info: {:?}",
        get_chain_info(&signer_test.running_nodes.conf)
    );

    info!("------------------------- Triggering Deeper Bitcoin Fork -------------------------");

    let burn_block_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
    let burn_header_hash_to_fork = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_block_hash(burn_block_height - 3);
    signer_test
        .running_nodes
        .btc_regtest_controller
        .invalidate_block(&burn_header_hash_to_fork);
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(4);

    info!("Wait for block off of deep fork");

    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    // we need to mine some blocks to get back to being considered a frequent miner
    TEST_MINE_STALL.set(true);
    for i in 0..3 {
        let current_burn_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
        info!(
            "Mining block #{i} to be considered a frequent miner";
            "current_burn_height" => current_burn_height,
        );
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        next_block_and_controller(
            &mut signer_test.running_nodes.btc_regtest_controller,
            60,
            |btc_controller| {
                let commits_submitted = commits_submitted
                    .load(Ordering::SeqCst);
                if commits_submitted <= commits_count {
                    // wait until a commit was submitted
                    return Ok(false)
                }
                let Some(payload) = get_unconfirmed_commit_data(btc_controller) else {
                    warn!("Commit submitted, but bitcoin doesn't see it in the unconfirmed UTXO set, will try to wait.");
                    return Ok(false)
                };
                let burn_parent_modulus = payload.burn_parent_modulus;
                let current_modulus = u8::try_from((current_burn_height + 1) % 5).unwrap();
                info!(
                    "Ongoing Commit Operation check";
                    "burn_parent_modulus" => burn_parent_modulus,
                    "current_modulus" => current_modulus,
                    "payload" => ?payload,
                );
                Ok(burn_parent_modulus == current_modulus)
            },
        )
        .unwrap();
    }

    let post_fork_2_nonce = get_account(&http_origin, &miner_address).nonce;

    assert_eq!(post_fork_2_nonce, pre_fork_2_nonce - 4 * 2);

    TEST_MINE_STALL.set(false);

    for i in 0..5 {
        info!("Mining post-fork tenure {} of 5", i + 1);
        signer_test.mine_nakamoto_block(Duration::from_secs(30), true);
    }

    let test_end_nonce = get_account(&http_origin, &miner_address).nonce;
    assert_eq!(test_end_nonce, post_fork_2_nonce + 2 * 5);

    info!(
        "New chain info: {:?}",
        get_chain_info(&signer_test.running_nodes.conf)
    );
    signer_test.shutdown();
}

#[test]
#[ignore]
fn multiple_miners() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let max_nakamoto_tenures = 30;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        0,
        |_| {},
        |config| {
            config.burnchain.pox_reward_length = Some(30);
            config.miner.block_commit_delay = Duration::from_secs(0);
            config.miner.tenure_cost_limit_per_block_percentage = None;
        },
        |_| {},
    );

    let (conf_1, conf_2) = miners.get_node_configs();
    miners.boot_to_epoch_3();
    let pre_nakamoto_peer_1_height = get_chain_info(&conf_1).stacks_tip_height;

    // due to the random nature of mining sortitions, the way this test is structured
    //  is that we keep track of how many tenures each miner produced, and once enough sortitions
    //  have been produced such that each miner has produced 3 tenures, we stop and check the
    //  results at the end
    info!("------------------------- Mining At Most {max_nakamoto_tenures} Tenures -------------------------");
    let rl1_counters = miners.signer_test.running_nodes.counters.clone();
    let rl2_counters = miners.rl2_counters.clone();
    let (miner_1_pk, miner_2_pk) = miners.get_miner_public_keys();
    let mut btc_blocks_mined = 1;
    let mut miner_1_tenures = 0;
    let mut miner_2_tenures = 0;
    while !(miner_1_tenures >= 3 && miner_2_tenures >= 3) {
        assert!(
            max_nakamoto_tenures >= btc_blocks_mined,
            "Produced {btc_blocks_mined} sortitions, but didn't cover the test scenarios, aborting"
        );

        let info_1 = get_chain_info(&conf_1);
        let info_2 = get_chain_info(&conf_2);

        info!("Issue next block-build request\ninfo 1: {info_1:?}\ninfo 2: {info_2:?}\n");

        miners.signer_test.mine_block_wait_on_processing(
            &[&conf_1, &conf_2],
            &[&rl1_counters, &rl2_counters],
            Duration::from_secs(30),
        );

        btc_blocks_mined += 1;
        let blocks = get_nakamoto_headers(&conf_1);
        // for this test, there should be one block per tenure
        let consensus_hash_set: HashSet<_> =
            blocks.iter().map(|header| header.consensus_hash).collect();
        assert_eq!(
            consensus_hash_set.len(),
            blocks.len(),
            "In this test, there should only be one block per tenure"
        );
        miner_1_tenures = blocks
            .iter()
            .filter(|header| {
                let header = header.anchored_header.as_stacks_nakamoto().unwrap();
                miner_1_pk
                    .verify(
                        header.miner_signature_hash().as_bytes(),
                        &header.miner_signature,
                    )
                    .unwrap()
            })
            .count();
        miner_2_tenures = blocks
            .iter()
            .filter(|header| {
                let header = header.anchored_header.as_stacks_nakamoto().unwrap();
                miner_2_pk
                    .verify(
                        header.miner_signature_hash().as_bytes(),
                        &header.miner_signature,
                    )
                    .unwrap()
            })
            .count();
    }

    let new_chain_info_1 = get_chain_info(&conf_1);
    let new_chain_info_2 = get_chain_info(&conf_2);
    info!("New chain info: {new_chain_info_1:?}");
    info!("New chain info: {new_chain_info_2:?}");

    let peer_1_height = new_chain_info_1.stacks_tip_height;
    let peer_2_height = new_chain_info_2.stacks_tip_height;
    info!("Peer height information"; "peer_1" => peer_1_height, "peer_2" => peer_2_height, "pre_naka_height" => pre_nakamoto_peer_1_height);
    assert_eq!(peer_1_height, peer_2_height);
    assert_eq!(
        peer_1_height,
        pre_nakamoto_peer_1_height + btc_blocks_mined as u64 - 1
    );
    assert_eq!(
        btc_blocks_mined,
        u32::try_from(miner_1_tenures + miner_2_tenures).unwrap()
    );
    miners.shutdown();
}

/// Read processed nakamoto block IDs from the test observer, and use `config` to open
///  a chainstate DB and returns their corresponding StacksHeaderInfos
fn get_nakamoto_headers(config: &Config) -> Vec<StacksHeaderInfo> {
    let nakamoto_block_ids: HashSet<_> = test_observer::get_blocks()
        .into_iter()
        .filter_map(|block_json| {
            block_json.as_object().unwrap().get("miner_signature")?;
            let block_id = StacksBlockId::from_hex(
                &block_json
                    .as_object()
                    .unwrap()
                    .get("index_block_hash")
                    .unwrap()
                    .as_str()
                    .unwrap()[2..],
            )
            .unwrap();
            Some(block_id)
        })
        .collect();

    let (chainstate, _) = StacksChainState::open(
        config.is_mainnet(),
        config.burnchain.chain_id,
        &config.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    nakamoto_block_ids
        .into_iter()
        .map(|block_id| {
            NakamotoChainState::get_block_header(chainstate.db(), &block_id)
                .unwrap()
                .unwrap()
        })
        .collect()
}

#[test]
#[ignore]
// Test two nakamoto miners, with the signer set split between them.
//  One of the miners (run-loop-2) is prevented from submitting "good" block commits
//  using the "commit stall" test flag in combination with "block broadcast stalls".
//  (Because RL2 isn't able to RBF their initial commits after the tip is broadcasted).
// This test works by tracking two different scenarios:
//   1. RL2 must win a sortition that this block commit behavior would lead to a fork in.
//   2. After such a sortition, RL1 must win another block.
// The test asserts that every nakamoto sortition either has a successful tenure, or if
//  RL2 wins and they would be expected to fork, no blocks are produced. The test asserts
//  that every block produced increments the chain length.
fn miner_forking() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let first_proposal_burn_block_timing = 1;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        5,
        0,
        |signer_config| {
            // we're deliberately stalling proposals: don't punish this in this test!
            signer_config.block_proposal_timeout = Duration::from_secs(240);
            // make sure that we don't allow forking due to burn block timing
            signer_config.first_proposal_burn_block_timing =
                Duration::from_secs(first_proposal_burn_block_timing);
        },
        |_| {},
        |_| {},
    );

    let (conf_1, conf_2) = miners.get_node_configs();
    let (mining_pk_1, mining_pk_2) = miners.get_miner_public_keys();
    let (mining_pkh_1, mining_pkh_2) = miners.get_miner_public_key_hashes();

    let skip_commit_op_rl1 = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let skip_commit_op_rl2 = miners.rl2_counters.naka_skip_commit_op.clone();

    // Make sure that the first miner wins the first sortition.
    info!("Pausing miner 2's block commit submissions");
    skip_commit_op_rl2.set(true);
    miners.boot_to_epoch_3();

    let sortdb = conf_1.get_burnchain().open_sortition_db(true).unwrap();
    let nakamoto_blocks_count_before = get_nakamoto_headers(&conf_1).len();
    let pre_nakamoto_peer_1_height = get_chain_info(&conf_1).stacks_tip_height;

    info!("------------------------- RL1 Wins Sortition -------------------------");
    info!("Pausing stacks block proposal to force an empty tenure commit from RL2");
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![mining_pk_1, mining_pk_2]);

    info!("Pausing commits from RL1");
    skip_commit_op_rl1.set(true);

    info!("Mine RL1 Tenure");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block.");
    miners.wait_for_chains(120);

    // make sure the tenure was won by RL1
    verify_sortition_winner(&sortdb, &mining_pkh_1);
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

    info!(
        "------------------------- RL2 Wins Sortition With Outdated View -------------------------"
    );
    miners.submit_commit_miner_2(&sortdb);

    // unblock block mining
    let blocks_len = test_observer::get_blocks().len();
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Wait for the block to be broadcasted and processed
    wait_for(30, || Ok(test_observer::get_blocks().len() > blocks_len))
        .expect("Timed out waiting for a block to be processed");

    // sleep for 2*first_proposal_burn_block_timing to prevent the block timing from allowing a fork by the signer set
    thread::sleep(Duration::from_secs(first_proposal_burn_block_timing * 2));

    let nakamoto_headers: HashMap<_, _> = get_nakamoto_headers(&conf_1)
    .into_iter()
    .map(|header| {
        info!("Nakamoto block"; "height" => header.stacks_block_height, "consensus_hash" => %header.consensus_hash, "last_sortition_hash" => %tip.consensus_hash);
        (header.consensus_hash, header)
    })
    .collect();

    let header_info = nakamoto_headers.get(&tip.consensus_hash).unwrap();
    let header = header_info
        .anchored_header
        .as_stacks_nakamoto()
        .unwrap()
        .clone();

    mining_pk_1
        .verify(
            header.miner_signature_hash().as_bytes(),
            &header.miner_signature,
        )
        .unwrap();

    info!("Mine RL2 Tenure");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::Extended, 60)
        .expect("Failed to mine BTC block followed by tenure change tx.");
    miners.wait_for_chains(120);
    // fetch the current sortition info
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    // make sure the tenure was won by RL2
    verify_sortition_winner(&sortdb, &mining_pkh_2);

    let header_info = get_nakamoto_headers(&conf_1).into_iter().last().unwrap();
    let header = header_info
        .anchored_header
        .as_stacks_nakamoto()
        .unwrap()
        .clone();

    mining_pk_1
        .verify(
            header.miner_signature_hash().as_bytes(),
            &header.miner_signature,
        )
        .expect("RL1 did not produce our last block");

    let nakamoto_headers: HashMap<_, _> = get_nakamoto_headers(&conf_1)
        .into_iter()
        .map(|header| {
            info!("Nakamoto block"; "height" => header.stacks_block_height, "consensus_hash" => %header.consensus_hash, "last_sortition_hash" => %tip.consensus_hash);
            (header.consensus_hash, header)
        })
        .collect();

    assert!(
        !nakamoto_headers.contains_key(&tip.consensus_hash),
        "RL1 produced a block with the current consensus hash."
    );

    info!("------------------------- RL1 RBFs its Own Commit -------------------------");
    info!("Pausing stacks block proposal to test RBF capability");
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![mining_pk_1, mining_pk_2]);
    miners.submit_commit_miner_1(&sortdb);

    info!("Mine RL1 Tenure");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 60)
        .expect("Failed to mine BTC block.");
    miners.submit_commit_miner_1(&sortdb);
    // unblock block mining
    let blocks_len = test_observer::get_blocks().len();
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Wait for the block to be broadcasted and processed
    wait_for(30, || Ok(test_observer::get_blocks().len() > blocks_len))
        .expect("Timed out waiting for a block to be processed");

    info!("Ensure that RL1 performs an RBF after unblocking block broadcast");
    miners.submit_commit_miner_1(&sortdb);

    info!("Mine RL1 Tenure");
    miners
        .mine_bitcoin_blocks_and_confirm_with_test_observer(&sortdb, 1, 60)
        .expect("Failed to mine BTC block.");
    // fetch the current sortition info
    miners.wait_for_chains(120);
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    // make sure the tenure was won by RL1
    verify_sortition_winner(&sortdb, &mining_pkh_1);

    let nakamoto_headers: HashMap<_, _> = get_nakamoto_headers(&conf_1)
        .into_iter()
        .map(|header| {
            info!("Nakamoto block"; "height" => header.stacks_block_height, "consensus_hash" => %header.consensus_hash, "last_sortition_hash" => %tip.consensus_hash);
            (header.consensus_hash, header)
        })
        .collect();

    let header_info = nakamoto_headers.get(&tip.consensus_hash).unwrap();
    let header = header_info
        .anchored_header
        .as_stacks_nakamoto()
        .unwrap()
        .clone();

    mining_pk_1
        .verify(
            header.miner_signature_hash().as_bytes(),
            &header.miner_signature,
        )
        .unwrap();

    info!("------------------------- Verify Peer Data -------------------------");

    let peer_1_height = get_chain_info(&conf_1).stacks_tip_height;
    let peer_2_height = get_chain_info(&conf_2).stacks_tip_height;
    let nakamoto_blocks_count = get_nakamoto_headers(&conf_1).len();
    info!("Peer height information"; "peer_1" => peer_1_height, "peer_2" => peer_2_height, "pre_naka_height" => pre_nakamoto_peer_1_height);
    info!("Nakamoto blocks count before test: {nakamoto_blocks_count_before}, Nakamoto blocks count now: {nakamoto_blocks_count}");
    assert_eq!(peer_1_height, peer_2_height);

    let nakamoto_blocks_count = get_nakamoto_headers(&conf_1).len();

    assert_eq!(
        peer_1_height - pre_nakamoto_peer_1_height,
        u64::try_from(nakamoto_blocks_count - nakamoto_blocks_count_before).unwrap(), // subtract 1 for the first Nakamoto block
        "There should be no forks in this test"
    );

    miners.shutdown();
}

#[test]
#[ignore]
/// This test checks the behavior at the end of a tenure. Specifically:
/// - The miner will broadcast the last block of the tenure, even if the signing is
///   completed after the next burn block arrives
/// - The signers will not sign a block that arrives after the next burn block, but
///   will finish a signing process that was in progress when the next burn block arrived
fn end_of_tenure() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_amt + send_fee)]);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let long_timeout = Duration::from_secs(200);
    let short_timeout = Duration::from_secs(20);
    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let proposed_blocks = signer_test
        .running_nodes
        .counters
        .naka_proposed_blocks
        .clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    signer_test.boot_to_epoch_3();
    let curr_reward_cycle = signer_test.get_current_reward_cycle();
    // Advance to one before the next reward cycle to ensure we are on the reward cycle boundary
    let final_reward_cycle = curr_reward_cycle + 1;
    let final_reward_cycle_height_boundary = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(final_reward_cycle)
        - 2;

    // give the system a chance to mine a Nakamoto block
    // But it doesn't have to mine one for this test to succeed?
    wait_for(short_timeout.as_secs(), || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .unwrap();

    info!("------------------------- Test Mine to Next Reward Cycle Boundary  -------------------------");
    signer_test.run_until_burnchain_height_nakamoto(
        long_timeout,
        final_reward_cycle_height_boundary,
        num_signers,
    );
    println!("Advanced to next reward cycle boundary: {final_reward_cycle_height_boundary}");
    assert_eq!(
        signer_test.get_current_reward_cycle(),
        final_reward_cycle - 1
    );

    info!("------------------------- Test Block Validation Stalled -------------------------");
    TEST_VALIDATE_STALL.set(true);

    let proposals_before = proposed_blocks.load(Ordering::SeqCst);
    let blocks_before = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;

    let info = get_chain_info(&signer_test.running_nodes.conf);
    let start_height = info.stacks_tip_height;
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    info!("Submitted transfer tx and waiting for block proposal");
    let start_time = Instant::now();
    while proposed_blocks.load(Ordering::SeqCst) <= proposals_before {
        assert!(
            start_time.elapsed() <= short_timeout,
            "Timed out waiting for block proposal"
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    wait_for(short_timeout.as_secs(), || {
        let result = signer_test.get_current_reward_cycle() == final_reward_cycle;
        if !result {
            signer_test
                .running_nodes
                .btc_regtest_controller
                .build_next_block(1);
        }
        Ok(result)
    })
    .expect("Timed out waiting to enter the next reward cycle");

    wait_for(short_timeout.as_secs(), || {
        let blocks = test_observer::get_burn_blocks()
            .last()
            .unwrap()
            .get("burn_block_height")
            .unwrap()
            .as_u64()
            .unwrap();
        Ok(blocks > final_reward_cycle_height_boundary)
    })
    .expect("Timed out waiting for burn block events");

    signer_test.wait_for_cycle(30, final_reward_cycle);

    info!("Block proposed and burn blocks consumed. Verifying that stacks block is still not processed");

    assert_eq!(
        get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height,
        blocks_before
    );

    info!("Unpausing block validation and waiting for block to be processed");
    // Disable the stall and wait for the block to be processed
    TEST_VALIDATE_STALL.set(false);
    wait_for(short_timeout.as_secs(), || {
        let processed_now = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;
        Ok(processed_now > blocks_before)
    })
    .expect("Timed out waiting for block to be mined");

    let info = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(info.stacks_tip_height, start_height + 1);

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks that the miner will retry when enough signers reject the block.
fn retry_on_rejection() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let short_timeout = Duration::from_secs(30);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, (send_amt + send_fee) * 3)]);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();

    // wait until we get a sortition.
    // we might miss a block-commit at the start of epoch 3
    let burnchain = signer_test.running_nodes.conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    wait_for(30, || {
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(tip.sortition)
    })
    .expect("Timed out waiting for sortition");

    // mine a nakamoto block
    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let proposed_blocks = signer_test
        .running_nodes
        .counters
        .naka_proposed_blocks
        .clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let start_time = Instant::now();
    // submit a tx so that the miner will mine a stacks block
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine the first Nakamoto block");

    // a tenure has begun, so wait until we mine a block
    while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
        assert!(
            start_time.elapsed() < short_timeout,
            "FAIL: Test timed out while waiting for block production",
        );
        thread::sleep(Duration::from_secs(1));
    }

    // make all signers reject the block
    let rejecting_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .take(num_signers)
        .collect();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(rejecting_signers);

    let proposals_before = proposed_blocks.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);

    // submit a tx so that the miner will mine a block
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    info!("Submitted transfer tx and waiting for block proposal");
    loop {
        if proposed_blocks.load(Ordering::SeqCst) > proposals_before {
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }

    info!("Block proposed, verifying that it is not processed");
    // Wait 10 seconds to be sure that the timeout has occurred
    std::thread::sleep(Duration::from_secs(10));
    assert_eq!(mined_blocks.load(Ordering::SeqCst), blocks_before);

    // resume signing
    info!("Disable unconditional rejection and wait for the block to be processed");
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(vec![]);
    loop {
        if mined_blocks.load(Ordering::SeqCst) > blocks_before {
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks that the signers will broadcast a block once they receive enough signatures.
fn signers_broadcast_signed_blocks() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_amt + send_fee)]);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();
    let info_before = get_chain_info(&signer_test.running_nodes.conf);
    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let signer_pushed_blocks = signer_test
        .running_nodes
        .counters
        .naka_signer_pushed_blocks
        .clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    wait_for(30, || {
        let blocks_mined = mined_blocks.load(Ordering::SeqCst);
        let info = get_chain_info(&signer_test.running_nodes.conf);
        debug!(
            "blocks_mined: {blocks_mined},{blocks_before}, stacks_tip_height: {},{}",
            info.stacks_tip_height, info_before.stacks_tip_height
        );
        Ok(blocks_mined > blocks_before && info.stacks_tip_height > info_before.stacks_tip_height)
    })
    .expect("Timed out waiting for first nakamoto block to be mined");

    TEST_IGNORE_SIGNERS.set(true);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let signer_pushed_before = signer_pushed_blocks.load(Ordering::SeqCst);
    let info_before = get_chain_info(&signer_test.running_nodes.conf);

    // submit a tx so that the miner will mine a blockn
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    debug!("Transaction sent; waiting for block-mining");

    wait_for(30, || {
        let signer_pushed = signer_pushed_blocks
            .load(Ordering::SeqCst);
        let blocks_mined = mined_blocks
            .load(Ordering::SeqCst);
        let info = get_chain_info(&signer_test.running_nodes.conf);
        debug!(
            "blocks_mined: {blocks_mined},{blocks_before}, signers_pushed: {signer_pushed},{signer_pushed_before}, stacks_tip_height: {},{}",
            info.stacks_tip_height,
            info_before.stacks_tip_height
        );
        Ok(blocks_mined > blocks_before
            && info.stacks_tip_height > info_before.stacks_tip_height
            && signer_pushed > signer_pushed_before)
    })
    .expect("Timed out waiting for second nakamoto block to be mined");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner will produce a TenureExtend transaction after the signers' idle timeout is reached.
fn tenure_extend_after_idle_signers() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let idle_timeout = Duration::from_secs(30);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("---- Waiting for a tenure extend ----");

    // Now, wait for a block with a tenure extend
    wait_for(idle_timeout.as_secs() + 10, || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect("Timed out waiting for a block with a tenure extend");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner will include other transactions with a TenureExtend transaction.
fn tenure_extend_with_other_transactions() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let idle_timeout = Duration::from_secs(30);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("Pause miner so it doesn't propose a block before the tenure extend");
    TEST_MINE_STALL.set(true);

    // Submit a transaction to be included with the tenure extend
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        0,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let _tx = submit_tx(&http_origin, &transfer_tx);

    info!("---- Wait for tenure extend timeout ----");

    sleep_ms(idle_timeout.as_millis() as u64 + 1000);

    info!("---- Resume miner to propose a block with the tenure extend ----");
    TEST_MINE_STALL.set(false);

    // Now, wait for a block with a tenure extend
    wait_for(idle_timeout.as_secs() + 10, || {
        let blocks = test_observer::get_blocks();
        let last_block = &blocks.last().unwrap();
        let transactions = last_block["transactions"].as_array().unwrap();
        let (first_tx, other_txs) = transactions.split_first().unwrap();
        let raw_tx = first_tx["raw_tx"].as_str().unwrap();
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        let found_tenure_extend = match &parsed.payload {
            TransactionPayload::TenureChange(payload)
                if payload.cause == TenureChangeCause::Extended =>
            {
                info!("Found tenure extend transaction: {parsed:?}");
                true
            }
            _ => false,
        };
        if found_tenure_extend {
            let found_transfer = other_txs.iter().any(|tx| {
                let raw_tx = tx["raw_tx"].as_str().unwrap();
                let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
                let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
                match &parsed.payload {
                    TransactionPayload::TokenTransfer(..) => true,
                    _ => false,
                }
            });
            if found_transfer {
                info!("Found transfer transaction");
                Ok(true)
            } else {
                Err("No transfer transaction found together with the tenure extend".to_string())
            }
        } else {
            info!("No tenure change transaction found");
            Ok(false)
        }
    })
    .expect("Timed out waiting for a block with a tenure extend");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner will produce a TenureExtend transaction after the miner's idle timeout
/// even if they do not see the signers' tenure extend timestamp responses.
fn tenure_extend_after_idle_miner() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let _recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let idle_timeout = Duration::from_secs(30);
    let miner_idle_timeout = idle_timeout + Duration::from_secs(10);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_timeout = miner_idle_timeout;
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );
    let _http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("---- Start a new tenure but ignore block signatures so no timestamps are recorded ----");
    let tip_height_before = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;
    TEST_IGNORE_SIGNERS.set(true);
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        30,
        || {
            let tip_height = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;
            Ok(tip_height > tip_height_before)
        },
    )
    .expect("Failed to mine the tenure change block");

    // Now, wait for a block with a tenure change due to the new block
    wait_for_tenure_change_tx(30, TenureChangeCause::BlockFound, tip_height_before + 1)
        .expect("Timed out waiting for a block with a tenure change");

    info!("---- Waiting for a tenure extend ----");

    TEST_IGNORE_SIGNERS.set(false);
    // Now, wait for a block with a tenure extend
    wait_for_tenure_change_tx(
        miner_idle_timeout.as_secs() + 20,
        TenureChangeCause::Extended,
        tip_height_before + 2,
    )
    .expect("Timed out waiting for a block with a tenure extend");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner that attempts to produce a tenure extend too early will be rejected by the signers,
/// but will eventually succeed after the signers' idle timeout has passed.
fn tenure_extend_succeeds_after_rejected_attempt() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let _recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let idle_timeout = Duration::from_secs(30);
    let miner_idle_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_timeout = miner_idle_timeout;
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );
    let _http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    let stacks_tip_height = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("---- Waiting for a rejected tenure extend ----");
    // Now, wait for a block with a tenure extend proposal from the miner, but ensure it is rejected.
    let proposed_block = wait_for_block_proposal(30, stacks_tip_height + 2, &miner_pk)
        .expect("Timed out waiting for a tenure extend proposal");
    wait_for_block_global_rejection(
        30,
        proposed_block.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Timed out waiting for a tenure extend proposal to be rejected");
    assert_eq!(
        proposed_block
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::Extended
    );

    info!("---- Waiting for an accepted tenure extend ----");
    wait_for(idle_timeout.as_secs() + 10, || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect("Test timed out while waiting for an accepted tenure extend");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Verify that Nakamoto blocks that don't modify the tenure's execution cost
/// don't modify the idle timeout.
fn stx_transfers_dont_effect_idle_timeout() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let num_txs = 5;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let idle_timeout = Duration::from_secs(60);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * num_txs)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );
    let naka_conf = signer_test.running_nodes.conf.clone();
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    // Add a delay to the block validation process
    TEST_VALIDATE_DELAY_DURATION_SECS.set(5);

    let info_before = signer_test.get_peer_info();
    let blocks_before = signer_test.running_nodes.counters.naka_mined_blocks.get();
    info!("---- Nakamoto booted, starting test ----";
        "info_height" => info_before.stacks_tip_height,
        "blocks_before" => blocks_before,
    );
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("---- Getting current idle timeout ----");

    let reward_cycle = signer_test.get_current_reward_cycle();

    let signer_slot_ids = signer_test.get_signer_indices(reward_cycle).into_iter();
    assert_eq!(signer_slot_ids.count(), num_signers);

    let get_last_block_hash = || {
        let blocks = test_observer::get_blocks();
        let last_block = blocks.last().unwrap();
        let block_hash =
            hex_bytes(&last_block.get("block_hash").unwrap().as_str().unwrap()[2..]).unwrap();
        Sha512Trunc256Sum::from_vec(&block_hash).unwrap()
    };

    let last_block_hash = get_last_block_hash();

    let slot_id = 0_u32;

    let initial_acceptance = signer_test.get_latest_block_acceptance(slot_id);
    assert_eq!(initial_acceptance.signer_signature_hash, last_block_hash);

    info!(
        "---- Last idle timeout: {} ----",
        initial_acceptance.response_data.tenure_extend_timestamp
    );

    // Now, mine a few nakamoto blocks with just transfers

    let mut sender_nonce = 0;

    // Note that this response was BEFORE the block was globally accepted. it will report a guestimated idle time
    let initial_acceptance = initial_acceptance;
    let mut first_global_acceptance = None;
    for i in 0..num_txs {
        info!("---- Mining interim block {} ----", i + 1);
        signer_test.wait_for_nakamoto_block(30, || {
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            submit_tx(&http_origin, &transfer_tx);
            sender_nonce += 1;
        });

        let latest_acceptance = signer_test.get_latest_block_acceptance(slot_id);
        let last_block_hash = get_last_block_hash();

        assert_eq!(latest_acceptance.signer_signature_hash, last_block_hash);

        if first_global_acceptance.is_none() {
            assert!(latest_acceptance.response_data.tenure_extend_timestamp < initial_acceptance.response_data.tenure_extend_timestamp, "First global acceptance should be less than initial guesstimated acceptance as its based on block proposal time rather than epoch time at time of response.");
            first_global_acceptance = Some(latest_acceptance);
        } else {
            // Because the block only contains transfers, the idle timeout should not have changed between blocks post the tenure change
            assert_eq!(
                latest_acceptance.response_data.tenure_extend_timestamp,
                first_global_acceptance
                    .as_ref()
                    .map(|acceptance| acceptance.response_data.tenure_extend_timestamp)
                    .unwrap()
            );
        };
    }

    info!("---- Waiting for a tenure extend ----");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// Verify that a tenure extend will occur after an idle timeout
/// while actively mining.
fn idle_tenure_extend_active_mining() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let deployer_sk = Secp256k1PrivateKey::random();
    let deployer_addr = tests::to_addr(&deployer_sk);
    let send_amt = 100;
    let send_fee = 180;
    let num_txs = 5;
    let num_naka_blocks = 5;
    let tenure_count = 2;
    let tx_fee = 10000;
    let deploy_fee = 190200;
    let amount =
        deploy_fee + tx_fee * num_txs * tenure_count * num_naka_blocks * 100 + 100 * tenure_count;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let idle_timeout = Duration::from_secs(60);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, amount), (deployer_addr, amount)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            // accept all proposals in the node
            config.connection_options.block_proposal_max_age_secs = u64::MAX;
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );
    let naka_conf = signer_test.running_nodes.conf.clone();
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let mut sender_nonces: HashMap<String, u64> = HashMap::new();

    let get_and_increment_nonce =
        |sender_sk: &Secp256k1PrivateKey, sender_nonces: &mut HashMap<String, u64>| {
            let nonce = sender_nonces.get(&sender_sk.to_hex()).unwrap_or(&0);
            let result = *nonce;
            sender_nonces.insert(sender_sk.to_hex(), result + 1);
            result
        };

    signer_test.boot_to_epoch_3();

    // Add a delay to the block validation process
    TEST_VALIDATE_DELAY_DURATION_SECS.set(3);

    signer_test.mine_nakamoto_block(Duration::from_secs(60), true);

    info!("---- Getting current idle timeout ----");

    let get_last_block_hash = || {
        let blocks = test_observer::get_blocks();
        let last_block = blocks.last().unwrap();
        let block_hash =
            hex_bytes(&last_block.get("block_hash").unwrap().as_str().unwrap()[2..]).unwrap();
        Sha512Trunc256Sum::from_vec(&block_hash).unwrap()
    };

    let last_block_hash = get_last_block_hash();

    let slot_id = 0_u32;

    let get_last_block_hash = || {
        let blocks = test_observer::get_blocks();
        let last_block = blocks.last().unwrap();
        let block_hash =
            hex_bytes(&last_block.get("block_hash").unwrap().as_str().unwrap()[2..]).unwrap();
        Sha512Trunc256Sum::from_vec(&block_hash).unwrap()
    };

    let log_idle_diff = |timestamp: u64| {
        let now = get_epoch_time_secs();
        let diff = timestamp.saturating_sub(now);
        info!("----- Idle diff: {diff} seconds -----");
    };

    let initial_response = signer_test.get_latest_block_response(slot_id);
    assert_eq!(
        initial_response.get_signer_signature_hash(),
        last_block_hash
    );

    info!(
        "---- Last idle timeout: {} ----",
        initial_response.get_tenure_extend_timestamp()
    );

    // Deploy a contract that will be called a lot

    let contract_src = format!(
        r#"
(define-data-var my-var uint u0)
(define-public (f) (begin {} (ok 1))) (begin (f))
        "#,
        ["(var-get my-var)"; 250].join(" ")
    );

    // First, lets deploy the contract
    let deployer_nonce = get_and_increment_nonce(&deployer_sk, &mut sender_nonces);
    let contract_tx = make_contract_publish(
        &deployer_sk,
        deployer_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        "small-contract",
        &contract_src,
    );
    submit_tx(&http_origin, &contract_tx);

    info!("----- Submitted deploy txs, mining BTC block -----");

    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);
    let mut last_response = signer_test.get_latest_block_response(slot_id);

    // Make multiple tenures that get extended through idle timeouts
    for t in 1..=tenure_count {
        info!("----- Mining tenure {t} -----");
        log_idle_diff(last_response.get_tenure_extend_timestamp());
        // Now, start a tenure with contract calls
        for i in 1..=num_naka_blocks {
            // Just in case these Nakamoto blocks pass the idle timeout (probably because CI is slow), exit early
            if i != 1 && last_block_contains_tenure_change_tx(TenureChangeCause::Extended) {
                info!("---- Tenure extended before mining {i} nakamoto blocks -----");
                break;
            }
            info!("----- Mining nakamoto block {i} in tenure {t} -----");

            signer_test.wait_for_nakamoto_block(30, || {
                // Throw in a STX transfer to test mixed blocks
                let sender_nonce = get_and_increment_nonce(&sender_sk, &mut sender_nonces);
                let transfer_tx = make_stacks_transfer(
                    &sender_sk,
                    sender_nonce,
                    send_fee,
                    naka_conf.burnchain.chain_id,
                    &recipient,
                    send_amt,
                );
                submit_tx(&http_origin, &transfer_tx);

                for _ in 0..num_txs {
                    let deployer_nonce = get_and_increment_nonce(&deployer_sk, &mut sender_nonces);
                    // Fill up the mempool with contract calls
                    let contract_tx = make_contract_call(
                        &deployer_sk,
                        deployer_nonce,
                        tx_fee,
                        naka_conf.burnchain.chain_id,
                        &deployer_addr,
                        "small-contract",
                        "f",
                        &[],
                    );
                    match submit_tx_fallible(&http_origin, &contract_tx) {
                        Ok(_txid) => {}
                        Err(_e) => {
                            // If we fail to submit a tx, we need to make sure we don't
                            // increment the nonce for this sender, so we don't end up
                            // skipping a tx.
                            sender_nonces.insert(deployer_sk.to_hex(), deployer_nonce);
                        }
                    }
                }
            });
            let latest_response = signer_test.get_latest_block_response(slot_id);
            let naka_blocks = test_observer::get_mined_nakamoto_blocks();
            info!(
                "----- Latest tenure extend timestamp: {} -----",
                latest_response.get_tenure_extend_timestamp()
            );
            log_idle_diff(latest_response.get_tenure_extend_timestamp());
            info!(
                "----- Latest block transaction events: {} -----",
                naka_blocks.last().unwrap().tx_events.len()
            );
            assert_eq!(
                latest_response.get_signer_signature_hash(),
                get_last_block_hash(),
                "Expected the latest block response to be for the latest block"
            );
            assert_ne!(
                last_response.get_tenure_extend_timestamp(),
                latest_response.get_tenure_extend_timestamp(),
                "Tenure extend timestamp should change with each block"
            );
            last_response = latest_response;
        }

        let current_time = get_epoch_time_secs();
        let extend_diff = last_response
            .get_tenure_extend_timestamp()
            .saturating_sub(current_time);

        info!(
            "----- After mining {num_naka_blocks} nakamoto blocks in tenure {t}, waiting for TenureExtend -----";
            "tenure_extend_timestamp" => last_response.get_tenure_extend_timestamp(),
            "extend_diff" => extend_diff,
            "current_time" => current_time,
        );

        // Now, wait for the idle timeout to trigger
        wait_for(extend_diff + 30, || {
            Ok(last_block_contains_tenure_change_tx(
                TenureChangeCause::Extended,
            ))
        })
        .expect("Expected a tenure extend after idle timeout");

        last_response = signer_test.get_latest_block_response(slot_id);

        info!("----- Tenure {t} extended -----");
        log_idle_diff(last_response.get_tenure_extend_timestamp());
    }

    // After the last extend, mine a few more naka blocks
    for i in 1..=num_naka_blocks {
        // Just in case these Nakamoto blocks pass the idle timeout (probably because CI is slow), exit early
        if i != 1 && last_block_contains_tenure_change_tx(TenureChangeCause::Extended) {
            info!("---- Tenure extended before mining {i} nakamoto blocks -----");
            break;
        }
        info!("----- Mining nakamoto block {i} after last tenure extend -----");

        signer_test.wait_for_nakamoto_block(30, || {
            // Throw in a STX transfer to test mixed blocks
            let sender_nonce = get_and_increment_nonce(&sender_sk, &mut sender_nonces);
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            submit_tx(&http_origin, &transfer_tx);
        });
    }

    info!("------------------------- Test Shutdown -------------------------");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks the behaviour of signers when a sortition is empty. Specifically:
/// - An empty sortition will cause the signers to mark a miner as misbehaving once a timeout is exceeded.
/// - The miner will stop trying to mine once it sees a threshold of signers reject the block
/// - The empty sortition will trigger the miner to attempt a tenure extend.
/// - Signers will accept the tenure extend and sign subsequent blocks built off the old sortition
fn empty_sortition() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let block_proposal_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            // make the duration long enough that the miner will be marked as malicious
            config.block_proposal_timeout = block_proposal_timeout;
        },
        |_| {},
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let short_timeout = Duration::from_secs(20);

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    signer_test.boot_to_epoch_3();

    let Counters {
        naka_mined_blocks: mined_blocks,
        naka_submitted_commits: submitted_commits,
        naka_skip_commit_op: skip_commit_op,
        naka_rejected_blocks: rejected_blocks,
        ..
    } = signer_test.running_nodes.counters.clone();

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);

    info!("------------------------- Test Mine Regular Tenure A  -------------------------");
    let commits_before = submitted_commits.load(Ordering::SeqCst);
    // Mine a regular tenure
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = submitted_commits.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    info!("------------------------- Test Mine Empty Tenure B  -------------------------");
    info!("Pausing stacks block mining to trigger an empty sortition.");
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let commits_before = submitted_commits.load(Ordering::SeqCst);
    // Start new Tenure B
    // In the next block, the miner should win the tenure
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = submitted_commits.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    info!("Pausing stacks block proposal to force an empty tenure");
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);

    info!("Pausing commit op to prevent tenure C from starting...");
    skip_commit_op.set(true);

    let blocks_after = mined_blocks.load(Ordering::SeqCst);
    assert_eq!(blocks_after, blocks_before);

    let rejected_before = rejected_blocks.load(Ordering::SeqCst);

    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    std::thread::sleep(block_proposal_timeout.add(Duration::from_secs(1)));

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    info!("------------------------- Test Delayed Block is Rejected  -------------------------");
    let reward_cycle = signer_test.get_current_reward_cycle();
    let mut stackerdb = StackerDB::new_normal(
        &signer_test.running_nodes.conf.node.rpc_bind,
        StacksPrivateKey::random(), // We are just reading so don't care what the key is
        false,
        reward_cycle,
        SignerSlotID(0), // We are just reading so again, don't care about index.
    );

    let signer_slot_ids: Vec<_> = signer_test
        .get_signer_indices(reward_cycle)
        .iter()
        .map(|id| id.0)
        .collect();
    assert_eq!(signer_slot_ids.len(), num_signers);

    // The miner's proposed block should get rejected by all the signers
    let mut found_rejections = Vec::new();
    wait_for(short_timeout.as_secs(), || {
        for slot_id in signer_slot_ids.iter() {
            if found_rejections.contains(slot_id) {
                continue;
            }
            let mut latest_msgs = StackerDB::get_messages(
                stackerdb
                    .get_session_mut(&MessageSlotID::BlockResponse)
                    .expect("Failed to get BlockResponse stackerdb session"),
                &[*slot_id]
            ).expect("Failed to get message from stackerdb");
            assert!(latest_msgs.len() <= 1);
            let Some(latest_msg) = latest_msgs.pop() else {
                info!("No message yet from slot #{slot_id}, will wait to try again");
                continue;
            };
            if let SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                reason_code,
                metadata,
                response_data,
                ..
            })) = latest_msg
            {
                assert_eq!(reason_code, RejectCode::SortitionViewMismatch);
                assert_eq!(response_data.reject_reason, RejectReason::InvalidMiner);
                assert_eq!(metadata.server_version, VERSION_STRING.to_string());
                found_rejections.push(*slot_id);
            } else {
                info!("Latest message from slot #{slot_id} isn't a block rejection, will wait to see if the signer updates to a rejection");
            }
        }
        let rejections = rejected_blocks
            .load(Ordering::SeqCst);

        // wait until we've found rejections for all the signers, and the miner has confirmed that
        // the signers have rejected the block
        Ok(found_rejections.len() == signer_slot_ids.len() && rejections > rejected_before)
    }).unwrap();
    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks the behavior of signers when an empty sortition arrives
/// before the first block of the previous tenure has been approved.
/// Specifically:
/// - The empty sortition will trigger the miner to attempt a tenure extend.
/// - Signers will accept the tenure extend and sign subsequent blocks built
///   off the old sortition
fn empty_sortition_before_approval() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let block_proposal_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            // make the duration long enough that the miner will be marked as malicious
            config.block_proposal_timeout = block_proposal_timeout;
        },
        |_| {},
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    let skip_commit_op = signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let proposed_blocks = signer_test
        .running_nodes
        .counters
        .naka_proposed_blocks
        .clone();

    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .unwrap();

    let info = get_chain_info(&signer_test.running_nodes.conf);
    let burn_height_before = info.burn_block_height;
    let stacks_height_before = info.stacks_tip_height;

    info!("Forcing miner to ignore signatures for next block");
    TEST_IGNORE_SIGNERS.set(true);

    info!("Pausing block commits to trigger an empty sortition.");
    skip_commit_op.set(true);

    info!("------------------------- Test Mine Tenure A  -------------------------");
    let proposed_before = proposed_blocks.load(Ordering::SeqCst);
    // Mine a regular tenure and wait for a block proposal
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || Ok(proposed_blocks.load(Ordering::SeqCst) > proposed_before),
    )
    .expect("Failed to mine tenure A and propose a block");

    info!("------------------------- Test Mine Empty Tenure B  -------------------------");

    // Trigger an empty tenure
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let burn_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
            Ok(burn_height == burn_height_before + 2)
        },
    )
    .expect("Failed to mine empty tenure");

    info!("Unpause block commits");
    skip_commit_op.set(false);

    info!("Stop ignoring signers and wait for the tip to advance");
    TEST_IGNORE_SIGNERS.set(false);

    wait_for(60, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > stacks_height_before)
    })
    .expect("Failed to advance chain tip");

    let info = get_chain_info(&signer_test.running_nodes.conf);
    info!("Current state: {:?}", info);

    // Wait for a block with a tenure extend to be mined
    wait_for(60, || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect("Timed out waiting for tenure extend");

    let stacks_height_before = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;

    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    wait_for(60, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > stacks_height_before)
    })
    .expect("Failed to advance chain tip with STX transfer");

    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .expect("Failed to mine a normal tenure after the tenure extend");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks the behavior of signers when an empty sortition arrives
/// before the first block of the previous tenure has been proposed.
/// Specifically:
/// - The empty sortition will trigger the miner to attempt a tenure extend.
/// - Signers will accept the tenure extend and sign subsequent blocks built
///   off the old sortition
fn empty_sortition_before_proposal() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let block_proposal_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            // make the duration long enough that the miner will be marked as malicious
            config.block_proposal_timeout = block_proposal_timeout;
        },
        |_| {},
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    let skip_commit_op = signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();

    signer_test.boot_to_epoch_3();

    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .unwrap();

    let info = get_chain_info(&signer_test.running_nodes.conf);
    let stacks_height_before = info.stacks_tip_height;

    info!("Pause block commits to ensure we get an empty sortition");
    skip_commit_op.set(true);

    info!("Pause miner so it doesn't propose a block before the next tenure arrives");
    TEST_MINE_STALL.set(true);

    let burn_height_before = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;

    info!("------------------------- Test Mine Tenure A and B  -------------------------");
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(2);

    wait_for(60, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.burn_block_height == burn_height_before + 2)
    })
    .expect("Failed to advance chain tip");

    // Sleep a bit more to ensure the signers see both burn blocks
    sleep_ms(5_000);

    info!("Unpause miner");
    TEST_MINE_STALL.set(false);

    info!("Unpause block commits");
    skip_commit_op.set(false);

    wait_for(60, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > stacks_height_before)
    })
    .expect("Failed to advance chain tip");

    let info = get_chain_info(&signer_test.running_nodes.conf);
    info!("Current state: {info:?}");

    info!("------------------------- Ensure Miner Extends Tenure  -------------------------");

    // Wait for a block with a tenure extend to be mined
    wait_for(60, || {
        let blocks = test_observer::get_blocks();
        let last_block = blocks.last().unwrap();
        info!("Last block mined: {:?}", last_block);
        for tx in last_block["transactions"].as_array().unwrap() {
            let raw_tx = tx["raw_tx"].as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::TenureChange(payload) = &parsed.payload {
                match payload.cause {
                    TenureChangeCause::Extended => {
                        info!("Found tenure extend block");
                        return Ok(true);
                    }
                    TenureChangeCause::BlockFound => {}
                }
            };
        }
        Ok(false)
    })
    .expect("Timed out waiting for tenure extend");

    info!("------------------------- Test Miner Mines Transfer Tx  -------------------------");

    let stacks_height_before = get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height;

    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    wait_for(60, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > stacks_height_before)
    })
    .expect("Failed to advance chain tip with STX transfer");

    info!("------------------------- Test Miner Tenure C  -------------------------");

    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .expect("Failed to mine a normal tenure after the tenure extend");

    info!("------------------------- Shutdown -------------------------");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test checks that Epoch 2.5 signers will issue a mock signature per burn block they receive.
fn mock_sign_epoch_25() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |_| {},
        |node_config| {
            node_config.miner.pre_nakamoto_mock_signing = true;
            let epochs = node_config.burnchain.epochs.as_mut().unwrap();
            epochs[StacksEpochId::Epoch25].end_height = 251;
            epochs[StacksEpochId::Epoch30].start_height = 251;
            epochs[StacksEpochId::Epoch30].end_height = 265;
            epochs[StacksEpochId::Epoch31].start_height = 265;
        },
        None,
        None,
    );

    let epochs = signer_test
        .running_nodes
        .conf
        .burnchain
        .epochs
        .clone()
        .unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let epoch_3_boundary = epoch_3.start_height - 1; // We only advance to the boundary as epoch 2.5 miner gets torn down at the boundary

    signer_test.boot_to_epoch_25_reward_cycle();

    info!("------------------------- Test Processing Epoch 2.5 Tenures -------------------------");

    // Mine until epoch 3.0 and ensure that no more mock signatures are received
    let reward_cycle = signer_test.get_current_reward_cycle();
    let signer_slot_ids = signer_test.get_signer_indices(reward_cycle).into_iter();
    let signer_public_keys = signer_test.get_signer_public_keys(reward_cycle);
    assert_eq!(signer_slot_ids.count(), num_signers);

    let miners_stackerdb_contract = boot_code_id(MINERS_NAME, false);

    // Mine until epoch 3.0 and ensure we get a new mock block per epoch 2.5 sortition
    let main_poll_time = Instant::now();
    // Only advance to the boundary as the epoch 2.5 miner will be shut down at this point.
    while signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height()
        < epoch_3_boundary
    {
        let mut mock_block_mesage = None;
        let mock_poll_time = Instant::now();
        signer_test
            .running_nodes
            .btc_regtest_controller
            .build_next_block(1);
        let current_burn_block_height = signer_test
            .running_nodes
            .btc_regtest_controller
            .get_headers_height();
        debug!("Waiting for mock miner message for burn block height {current_burn_block_height}");
        while mock_block_mesage.is_none() {
            std::thread::sleep(Duration::from_millis(100));
            let chunks = test_observer::get_stackerdb_chunks();
            for chunk in chunks
                .into_iter()
                .filter_map(|chunk| {
                    if chunk.contract_id != miners_stackerdb_contract {
                        return None;
                    }
                    Some(chunk.modified_slots)
                })
                .flatten()
            {
                if chunk.data.is_empty() {
                    continue;
                }
                let SignerMessage::MockBlock(mock_block) =
                    SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                        .expect("Failed to deserialize SignerMessage")
                else {
                    continue;
                };
                if mock_block.mock_proposal.peer_info.burn_block_height == current_burn_block_height
                {
                    mock_block
                        .mock_signatures
                        .iter()
                        .for_each(|mock_signature| {
                            assert!(signer_public_keys.iter().any(|signer| {
                                mock_signature
                                    .verify(
                                        &StacksPublicKey::from_slice(signer.to_bytes().as_slice())
                                            .unwrap(),
                                    )
                                    .expect("Failed to verify mock signature")
                            }));
                        });
                    mock_block_mesage = Some(mock_block);
                    break;
                }
            }
            assert!(
                mock_poll_time.elapsed() <= Duration::from_secs(15),
                "Failed to find mock miner message within timeout"
            );
        }
        assert!(
            main_poll_time.elapsed() <= Duration::from_secs(145),
            "Timed out waiting to advance epoch 3.0 boundary"
        );
    }
}

#[test]
#[ignore]
fn multiple_miners_mock_sign_epoch_25() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let num_signers = 5;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        0,
        |_| {},
        |config| {
            config.miner.pre_nakamoto_mock_signing = true;
            let epochs = config.burnchain.epochs.as_mut().unwrap();
            epochs[StacksEpochId::Epoch25].end_height = 251;
            epochs[StacksEpochId::Epoch30].start_height = 251;
            epochs[StacksEpochId::Epoch30].end_height = 265;
            epochs[StacksEpochId::Epoch31].start_height = 265;
        },
        |_| {},
    );
    let epochs = miners
        .signer_test
        .running_nodes
        .conf
        .burnchain
        .epochs
        .clone()
        .unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let epoch_3_boundary = epoch_3.start_height - 1; // We only advance to the boundary as epoch 2.5 miner gets torn down at the boundary

    miners.signer_test.boot_to_epoch_25_reward_cycle();
    miners.wait_for_chains(600);

    info!("------------------------- Reached Epoch 2.5 Reward Cycle-------------------------");

    // Mine until epoch 3.0 and ensure that no more mock signatures are received
    let reward_cycle = miners.signer_test.get_current_reward_cycle();
    let signer_slot_ids = miners
        .signer_test
        .get_signer_indices(reward_cycle)
        .into_iter();
    let signer_public_keys = miners.signer_test.get_signer_public_keys(reward_cycle);
    assert_eq!(signer_slot_ids.count(), num_signers);

    let miners_stackerdb_contract = boot_code_id(MINERS_NAME, false);

    // Only advance to the boundary as the epoch 2.5 miner will be shut down at this point.
    while miners.btc_regtest_controller_mut().get_headers_height() < epoch_3_boundary {
        let mut mock_block_mesage = None;
        let mock_poll_time = Instant::now();
        miners.btc_regtest_controller_mut().build_next_block(1);
        let current_burn_block_height = miners.btc_regtest_controller_mut().get_headers_height();
        debug!("Waiting for mock miner message for burn block height {current_burn_block_height}");
        while mock_block_mesage.is_none() {
            std::thread::sleep(Duration::from_millis(100));
            let chunks = test_observer::get_stackerdb_chunks();
            for chunk in chunks
                .into_iter()
                .filter_map(|chunk| {
                    if chunk.contract_id != miners_stackerdb_contract {
                        return None;
                    }
                    Some(chunk.modified_slots)
                })
                .flatten()
            {
                if chunk.data.is_empty() {
                    continue;
                }
                let SignerMessage::MockBlock(mock_block) =
                    SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                        .expect("Failed to deserialize SignerMessage")
                else {
                    continue;
                };
                if mock_block.mock_proposal.peer_info.burn_block_height == current_burn_block_height
                {
                    mock_block
                        .mock_signatures
                        .iter()
                        .for_each(|mock_signature| {
                            assert!(signer_public_keys.iter().any(|signer| {
                                mock_signature
                                    .verify(
                                        &StacksPublicKey::from_slice(signer.to_bytes().as_slice())
                                            .unwrap(),
                                    )
                                    .expect("Failed to verify mock signature")
                            }));
                        });
                    mock_block_mesage = Some(mock_block);
                    break;
                }
            }
            assert!(
                mock_poll_time.elapsed() <= Duration::from_secs(15),
                "Failed to find mock miner message within timeout"
            );
        }
    }
}

#[test]
#[ignore]
/// This test asserts that signer set rollover works as expected.
/// Specifically, if a new set of signers are registered for an upcoming reward cycle,
/// old signers shut down operation and the new signers take over with the commencement of
/// the next reward cycle.
fn signer_set_rollover() {
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let new_num_signers = 4;

    let new_signer_private_keys: Vec<_> = (0..new_num_signers)
        .map(|_| StacksPrivateKey::random())
        .collect();
    let new_signer_public_keys: Vec<_> = new_signer_private_keys
        .iter()
        .map(|sk| Secp256k1PublicKey::from_private(sk).to_bytes_compressed())
        .collect();
    let new_signer_addresses: Vec<_> = new_signer_private_keys.iter().map(tests::to_addr).collect();
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    let mut initial_balances = new_signer_addresses
        .iter()
        .map(|addr| (*addr, POX_4_DEFAULT_STACKER_BALANCE))
        .collect::<Vec<_>>();

    initial_balances.push((sender_addr, (send_amt + send_fee) * 4));

    let run_stamp = rand::random();

    let rpc_port = 51024;
    let rpc_bind = format!("127.0.0.1:{rpc_port}");

    // Setup the new signers that will take over
    let new_signer_configs = build_signer_config_tomls(
        &new_signer_private_keys,
        &rpc_bind,
        Some(Duration::from_millis(128)), // Timeout defaults to 5 seconds. Let's override it to 128 milliseconds.
        &Network::Testnet,
        "12345",
        run_stamp,
        3000 + num_signers,
        Some(100_000),
        None,
        Some(9000 + num_signers),
        None,
    );

    let new_spawned_signers: Vec<_> = new_signer_configs
        .iter()
        .map(|conf| {
            info!("spawning signer");
            let signer_config = SignerConfig::load_from_str(conf).unwrap();
            SpawnedSigner::new(signer_config)
        })
        .collect();

    // Boot with some initial signer set
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        initial_balances,
        |_| {},
        |naka_conf| {
            for toml in new_signer_configs.clone() {
                let signer_config = SignerConfig::load_from_str(&toml).unwrap();
                info!(
                    "---- Adding signer endpoint to naka conf ({}) ----",
                    signer_config.endpoint
                );

                naka_conf.events_observers.insert(EventObserverConfig {
                    endpoint: format!("{}", signer_config.endpoint),
                    events_keys: vec![
                        EventKeyType::StackerDBChunks,
                        EventKeyType::BlockProposal,
                        EventKeyType::BurnchainBlocks,
                    ],
                    timeout_ms: 1000,
                });
            }
            naka_conf.node.rpc_bind = rpc_bind.clone();
        },
        None,
        None,
    );
    assert_eq!(
        new_spawned_signers[0].config.node_host,
        signer_test.running_nodes.conf.node.rpc_bind
    );
    // Only stack for one cycle so that the signer set changes
    signer_test.num_stacking_cycles = 1_u64;

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let short_timeout = Duration::from_secs(20);

    // Verify that naka_conf has our new signer's event observers
    for toml in &new_signer_configs {
        let signer_config = SignerConfig::load_from_str(toml).unwrap();
        let endpoint = format!("{}", signer_config.endpoint);
        assert!(signer_test
            .running_nodes
            .conf
            .events_observers
            .iter()
            .any(|observer| observer.endpoint == endpoint));
    }

    // Advance to the first reward cycle, stacking to the old signers beforehand

    info!("---- Booting to epoch 3 -----");
    signer_test.boot_to_epoch_3();

    // verify that the first reward cycle has the old signers in the reward set
    let reward_cycle = signer_test.get_current_reward_cycle();
    let signer_test_public_keys: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(|sk| Secp256k1PublicKey::from_private(sk).to_bytes_compressed())
        .collect();

    info!("---- Verifying that the current signers are the old signers ----");
    let current_signers = signer_test.get_reward_set_signers(reward_cycle);
    assert_eq!(current_signers.len(), num_signers);
    // Verify that the current signers are the same as the old signers
    for signer in current_signers.iter() {
        assert!(signer_test_public_keys.contains(&signer.signing_key.to_vec()));
        assert!(!new_signer_public_keys.contains(&signer.signing_key.to_vec()));
    }

    info!("---- Mining a block to trigger the signer set -----");
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);
    signer_test.mine_nakamoto_block(short_timeout, true);
    let mined_block = test_observer::get_mined_nakamoto_blocks().pop().unwrap();
    let block_sighash = mined_block.signer_signature_hash;
    let signer_signatures = mined_block.signer_signature;

    // verify the mined_block signatures against the OLD signer set
    for signature in signer_signatures.iter() {
        let pk = Secp256k1PublicKey::recover_to_pubkey(block_sighash.bits(), signature)
            .expect("FATAL: Failed to recover pubkey from block sighash");
        assert!(signer_test_public_keys.contains(&pk.to_bytes_compressed()));
        assert!(!new_signer_public_keys.contains(&pk.to_bytes_compressed()));
    }

    // advance to the next reward cycle, stacking to the new signers beforehand
    let reward_cycle = signer_test.get_current_reward_cycle();

    info!("---- Stacking new signers -----");

    let burn_block_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height();
    let accounts_to_check: Vec<_> = new_signer_private_keys.iter().map(tests::to_addr).collect();
    for stacker_sk in new_signer_private_keys.iter() {
        let pox_addr = PoxAddress::from_legacy(
            AddressHashMode::SerializeP2PKH,
            tests::to_addr(stacker_sk).bytes().clone(),
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            stacker_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            CHAIN_ID_TESTNET,
            1_u128,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = Secp256k1PublicKey::from_private(stacker_sk);
        let stacking_tx = tests::make_contract_call(
            stacker_sk,
            0,
            1000,
            signer_test.running_nodes.conf.burnchain.chain_id,
            &StacksAddress::burn_address(false),
            "pox-4",
            "stack-stx",
            &[
                clarity::vm::Value::UInt(POX_4_DEFAULT_STACKER_STX_AMT),
                pox_addr_tuple.clone(),
                clarity::vm::Value::UInt(burn_block_height as u128),
                clarity::vm::Value::UInt(1),
                clarity::vm::Value::some(clarity::vm::Value::buff_from(signature).unwrap())
                    .unwrap(),
                clarity::vm::Value::buff_from(signer_pk.to_bytes_compressed()).unwrap(),
                clarity::vm::Value::UInt(u128::MAX),
                clarity::vm::Value::UInt(1),
            ],
        );
        submit_tx(&http_origin, &stacking_tx);
    }

    wait_for(60, || {
        Ok(accounts_to_check
            .iter()
            .all(|acct| get_account(&http_origin, acct).nonce >= 1))
    })
    .expect("Timed out waiting for stacking txs to be mined");

    signer_test.mine_nakamoto_block(short_timeout, true);

    let next_reward_cycle = reward_cycle.saturating_add(1);

    let next_cycle_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .nakamoto_first_block_of_cycle(next_reward_cycle)
        .saturating_add(1);

    info!("---- Mining to next reward set calculation -----");
    signer_test.run_until_burnchain_height_nakamoto(
        Duration::from_secs(60),
        next_cycle_height.saturating_sub(3),
        new_num_signers,
    );

    // Verify that the new reward set is the new signers
    let reward_set = signer_test.get_reward_set_signers(next_reward_cycle);
    for signer in reward_set.iter() {
        assert!(!signer_test_public_keys.contains(&signer.signing_key.to_vec()));
        assert!(new_signer_public_keys.contains(&signer.signing_key.to_vec()));
    }

    info!("---- Mining to the next reward cycle (block {next_cycle_height}) -----",);
    signer_test.run_until_burnchain_height_nakamoto(
        Duration::from_secs(60),
        next_cycle_height,
        new_num_signers,
    );
    let new_reward_cycle = signer_test.get_current_reward_cycle();
    assert_eq!(new_reward_cycle, reward_cycle.saturating_add(1));

    info!("---- Verifying that the current signers are the new signers ----");
    let current_signers = signer_test.get_reward_set_signers(new_reward_cycle);
    assert_eq!(current_signers.len(), new_num_signers);
    for signer in current_signers.iter() {
        assert!(!signer_test_public_keys.contains(&signer.signing_key.to_vec()));
        assert!(new_signer_public_keys.contains(&signer.signing_key.to_vec()));
    }

    info!("---- Mining a block to verify new signer set -----");
    let sender_nonce = 1;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);
    signer_test.mine_nakamoto_block(short_timeout, true);
    let mined_block = test_observer::get_mined_nakamoto_blocks().pop().unwrap();

    info!("---- Verifying that the new signers signed the block -----");
    let signer_signatures = mined_block.signer_signature;

    // verify the mined_block signatures against the NEW signer set
    for signature in signer_signatures.iter() {
        let pk = Secp256k1PublicKey::recover_to_pubkey(block_sighash.bits(), signature)
            .expect("FATAL: Failed to recover pubkey from block sighash");
        assert!(!signer_test_public_keys.contains(&pk.to_bytes_compressed()));
        assert!(new_signer_public_keys.contains(&pk.to_bytes_compressed()));
    }

    signer_test.shutdown();
    for signer in new_spawned_signers {
        assert!(signer.stop().is_none());
    }
}

#[test]
#[ignore]
/// This test checks that the miners and signers will not produce Nakamoto blocks
/// until the minimum time has passed between blocks.
fn min_gap_between_blocks() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;

    let interim_blocks = 5;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let time_between_blocks_ms = 10_000;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * interim_blocks)],
        |_config| {},
        |config| {
            config.miner.min_time_between_blocks_ms = time_between_blocks_ms;
        },
        None,
        None,
    );

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();

    signer_test.boot_to_epoch_3();

    info!("Ensure that the first Nakamoto block was mined");
    let blocks = get_nakamoto_headers(&signer_test.running_nodes.conf);
    assert_eq!(blocks.len(), 1);
    // mine the interim blocks
    info!("Mining interim blocks");
    for interim_block_ix in 0..interim_blocks {
        let blocks_processed_before = mined_blocks.load(Ordering::SeqCst);
        // submit a tx so that the miner will mine an extra block
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            interim_block_ix, // same as the sender nonce
            send_fee,
            signer_test.running_nodes.conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        submit_tx(&http_origin, &transfer_tx);

        info!("Submitted transfer tx and waiting for block to be processed");
        wait_for(60, || {
            Ok(mined_blocks.load(Ordering::SeqCst) > blocks_processed_before)
        })
        .unwrap();
        info!("Mined interim block:{interim_block_ix}");
    }

    wait_for(60, || {
        let new_blocks = get_nakamoto_headers(&signer_test.running_nodes.conf);
        Ok(new_blocks.len() == blocks.len() + interim_blocks as usize)
    })
    .unwrap();

    // Verify that every Nakamoto block is mined after the gap is exceeded between each
    let mut blocks = get_nakamoto_headers(&signer_test.running_nodes.conf);
    blocks.sort_by(|a, b| a.stacks_block_height.cmp(&b.stacks_block_height));
    for i in 1..blocks.len() {
        let block = &blocks[i];
        let parent_block = &blocks[i - 1];
        assert_eq!(
            block.stacks_block_height,
            parent_block.stacks_block_height + 1
        );
        info!(
            "Checking that the time between blocks {} and {} is respected",
            parent_block.stacks_block_height, block.stacks_block_height
        );
        let block_time = block
            .anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .timestamp;
        let parent_block_time = parent_block
            .anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .timestamp;
        assert!(
            block_time > parent_block_time,
            "Block time is BEFORE parent block time"
        );
        assert!(
            Duration::from_secs(block_time - parent_block_time)
                >= Duration::from_millis(time_between_blocks_ms),
            "Block mined before gap was exceeded: {block_time}s - {parent_block_time}s > {time_between_blocks_ms}ms",
        );
    }
    debug!("Shutting down min_gap_between_blocks test");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test scenario where there are duplicate signers with the same private key
/// First submitted signature should take precedence
fn duplicate_signers() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    // Disable p2p broadcast of the nakamoto blocks, so that we rely
    //  on the signer's using StackerDB to get pushed blocks
    nakamoto_node::miner::TEST_P2P_BROADCAST_SKIP.set(true);

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_stacks_private_keys = (0..num_signers)
        .map(|_| StacksPrivateKey::random())
        .collect::<Vec<_>>();

    // First two signers have same private key
    signer_stacks_private_keys[1] = signer_stacks_private_keys[0];
    let unique_signers = num_signers - 1;
    let duplicate_pubkey = Secp256k1PublicKey::from_private(&signer_stacks_private_keys[0]);
    let duplicate_pubkey_from_copy =
        Secp256k1PublicKey::from_private(&signer_stacks_private_keys[1]);
    assert_eq!(
        duplicate_pubkey, duplicate_pubkey_from_copy,
        "Recovered pubkeys don't match"
    );

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |_| {},
        |_| {},
        None,
        Some(signer_stacks_private_keys),
    );

    signer_test.boot_to_epoch_3();
    let timeout = Duration::from_secs(30);

    info!("------------------------- Try mining one block -------------------------");

    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);

    info!("------------------------- Read all `BlockResponse::Accepted` messages -------------------------");

    let mut signer_accepted_responses = vec![];
    let start_polling = Instant::now();
    while start_polling.elapsed() <= timeout {
        std::thread::sleep(Duration::from_secs(1));
        let messages = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                SignerMessage::consensus_deserialize(&mut chunk.data.as_slice()).ok()
            })
            .filter_map(|message| match message {
                SignerMessage::BlockResponse(BlockResponse::Accepted(m)) => {
                    info!("Message(accepted): {m:?}");
                    Some(m)
                }
                _ => {
                    debug!("Message(ignored): {message:?}");
                    None
                }
            });
        signer_accepted_responses.extend(messages);
    }

    info!("------------------------- Assert there are {unique_signers} unique signatures and recovered pubkeys -------------------------");

    // Pick a message hash
    let accepted = signer_accepted_responses
        .iter()
        .min_by_key(|accepted| accepted.signer_signature_hash)
        .expect("No `BlockResponse::Accepted` messages recieved");
    let selected_sighash = accepted.signer_signature_hash;

    // Filter only resonses for selected block and collect unique pubkeys and signatures
    let (pubkeys, signatures): (HashSet<_>, HashSet<_>) = signer_accepted_responses
        .into_iter()
        .filter(|accepted| accepted.signer_signature_hash == selected_sighash)
        .map(|accepted| {
            let pubkey = Secp256k1PublicKey::recover_to_pubkey(
                accepted.signer_signature_hash.bits(),
                &accepted.signature,
            )
            .expect("Failed to recover pubkey");
            (pubkey, accepted.signature)
        })
        .unzip();

    assert_eq!(pubkeys.len(), unique_signers);
    assert_eq!(signatures.len(), unique_signers);

    signer_test.shutdown();
}

/// This test involves two miners, each mining tenures with 6 blocks each. Half
/// of the signers are attached to each miner, so the test also verifies that
/// the signers' messages successfully make their way to the active miner.
#[test]
#[ignore]
fn multiple_miners_with_nakamoto_blocks() {
    let num_signers = 5;
    let max_nakamoto_tenures = 20;
    let inter_blocks_per_tenure = 5;

    let mut miners =
        MultipleMinerTest::new(num_signers, inter_blocks_per_tenure * max_nakamoto_tenures);

    let (miner_1_pk, miner_2_pk) = miners.get_miner_public_keys();
    let (conf_1, conf_2) = miners.get_node_configs();
    let rl1_counters = miners.signer_test.running_nodes.counters.clone();
    let rl2_counters = miners.rl2_counters.clone();
    let blocks_mined1 = rl1_counters.naka_mined_blocks.clone();
    let blocks_mined2 = rl2_counters.naka_mined_blocks.clone();

    miners.boot_to_epoch_3();

    let pre_nakamoto_peer_1_height = get_chain_info(&conf_1).stacks_tip_height;

    // due to the random nature of mining sortitions, the way this test is structured
    //  is that we keep track of how many tenures each miner produced, and once enough sortitions
    //  have been produced such that each miner has produced 3 tenures, we stop and check the
    //  results at the end

    let mut btc_blocks_mined = 1_u64;
    let mut miner_1_tenures = 0_u64;
    let mut miner_2_tenures = 0_u64;
    while !(miner_1_tenures >= 3 && miner_2_tenures >= 3) {
        if btc_blocks_mined > max_nakamoto_tenures {
            panic!("Produced {btc_blocks_mined} sortitions, but didn't cover the test scenarios, aborting");
        }
        let blocks_processed_before =
            blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst);
        miners.signer_test.mine_block_wait_on_processing(
            &[&conf_1, &conf_2],
            &[&rl1_counters, &rl2_counters],
            Duration::from_secs(30),
        );
        btc_blocks_mined += 1;

        // wait for the new block to be processed
        wait_for(60, || {
            let blocks_processed =
                blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst);
            Ok(blocks_processed > blocks_processed_before)
        })
        .unwrap();

        info!(
            "Nakamoto blocks mined: {}",
            blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst)
        );

        // mine the interim blocks
        info!("Mining interim blocks");
        for interim_block_ix in 0..inter_blocks_per_tenure {
            miners
                .send_and_mine_transfer_tx(60)
                .expect("Failed to mine interim block");
            info!("Mined interim block {btc_blocks_mined}:{interim_block_ix}");
        }

        let blocks = get_nakamoto_headers(&conf_1);
        let mut seen_burn_hashes = HashSet::new();
        miner_1_tenures = 0;
        miner_2_tenures = 0;
        for header in blocks.iter() {
            if seen_burn_hashes.contains(&header.burn_header_hash) {
                continue;
            }
            seen_burn_hashes.insert(header.burn_header_hash);

            let header = header.anchored_header.as_stacks_nakamoto().unwrap();
            if miner_1_pk
                .verify(
                    header.miner_signature_hash().as_bytes(),
                    &header.miner_signature,
                )
                .unwrap()
            {
                miner_1_tenures += 1;
            }
            if miner_2_pk
                .verify(
                    header.miner_signature_hash().as_bytes(),
                    &header.miner_signature,
                )
                .unwrap()
            {
                miner_2_tenures += 1;
            }
        }
        info!("Miner 1 tenures: {miner_1_tenures}, Miner 2 tenures: {miner_2_tenures}");
    }
    let chain_info_1 = get_chain_info(&conf_1);
    let chain_info_2 = get_chain_info(&conf_2);
    info!("New chain info 1: {chain_info_1:?}");
    info!("New chain info 2: {chain_info_2:?}");

    let peer_1_height = chain_info_1.stacks_tip_height;
    let peer_2_height = chain_info_2.stacks_tip_height;
    info!("Peer height information"; "peer_1" => peer_1_height, "peer_2" => peer_2_height, "pre_naka_height" => pre_nakamoto_peer_1_height);
    assert_eq!(peer_1_height, peer_2_height);
    assert_eq!(
        peer_1_height,
        pre_nakamoto_peer_1_height + (btc_blocks_mined - 1) * (inter_blocks_per_tenure as u64 + 1)
    );
    assert_eq!(btc_blocks_mined, miner_1_tenures + miner_2_tenures);
    miners.shutdown();
}

/// This test involves two miners, 1 and 2. During miner 1's first tenure, miner
/// 2 is forced to ignore one of the blocks in that tenure. The next time miner
/// 2 mines a block, it should attempt to fork the chain at that point. The test
/// verifies that the fork is not successful and that miner 1 is able to
/// continue mining after this fork attempt.
#[test]
#[ignore]
fn partial_tenure_fork() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let max_nakamoto_tenures = 30;
    let inter_blocks_per_tenure = 5;

    // setup sender + recipient for a test stx transfer
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    let btc_miner_1_seed = vec![1, 1, 1, 1];
    let btc_miner_2_seed = vec![2, 2, 2, 2];
    let btc_miner_1_pk = Keychain::default(btc_miner_1_seed.clone()).get_pub_key();
    let btc_miner_2_pk = Keychain::default(btc_miner_2_seed.clone()).get_pub_key();

    let node_1_rpc = gen_random_port();
    let node_1_p2p = gen_random_port();
    let node_2_rpc = gen_random_port();
    let node_2_p2p = gen_random_port();

    let localhost = "127.0.0.1";
    let node_1_rpc_bind = format!("{localhost}:{node_1_rpc}");

    // All signers are listening to node 1
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(
            sender_addr,
            (send_amt + send_fee) * max_nakamoto_tenures * inter_blocks_per_tenure,
        )],
        |signer_config| {
            signer_config.node_host = node_1_rpc_bind.clone();
            signer_config.first_proposal_burn_block_timing = Duration::from_secs(0);
        },
        |config| {
            config.node.rpc_bind = format!("{localhost}:{node_1_rpc}");
            config.node.p2p_bind = format!("{localhost}:{node_1_p2p}");
            config.node.data_url = format!("http://{localhost}:{node_1_rpc}");
            config.node.p2p_address = format!("{localhost}:{node_1_p2p}");
            config.miner.wait_on_interim_blocks = Duration::from_secs(5);
            config.node.pox_sync_sample_secs = 30;
            config.miner.block_commit_delay = Duration::from_secs(0);

            config.node.seed = btc_miner_1_seed.clone();
            config.node.local_peer_seed = btc_miner_1_seed.clone();
            config.burnchain.local_mining_public_key = Some(btc_miner_1_pk.to_hex());
            config.miner.mining_key = Some(Secp256k1PrivateKey::from_seed(&[1]));

            // Increase the reward cycle length to avoid missing a prepare phase
            // while we are intentionally forking.
            config.burnchain.pox_reward_length = Some(40);
            config.burnchain.pox_prepare_length = Some(10);

            // Move epoch 2.5 and 3.0 earlier, so we have more time for the
            // test before re-stacking is required.
            if let Some(epochs) = config.burnchain.epochs.as_mut() {
                epochs[StacksEpochId::Epoch24].end_height = 131;
                epochs[StacksEpochId::Epoch25].start_height = 131;
                epochs[StacksEpochId::Epoch25].end_height = 166;
                epochs[StacksEpochId::Epoch30].start_height = 166;
            } else {
                panic!("Expected epochs to be set");
            }
        },
        Some(vec![btc_miner_1_pk, btc_miner_2_pk]),
        None,
    );
    let blocks_mined1 = signer_test.running_nodes.counters.naka_mined_blocks.clone();

    let conf = signer_test.running_nodes.conf.clone();
    let mut conf_node_2 = conf.clone();
    conf_node_2.node.rpc_bind = format!("{localhost}:{node_2_rpc}");
    conf_node_2.node.p2p_bind = format!("{localhost}:{node_2_p2p}");
    conf_node_2.node.data_url = format!("http://{localhost}:{node_2_rpc}");
    conf_node_2.node.p2p_address = format!("{localhost}:{node_2_p2p}");
    conf_node_2.node.seed = btc_miner_2_seed.clone();
    conf_node_2.burnchain.local_mining_public_key = Some(btc_miner_2_pk.to_hex());
    conf_node_2.node.local_peer_seed = btc_miner_2_seed;
    conf_node_2.miner.mining_key = Some(Secp256k1PrivateKey::from_seed(&[2]));
    conf_node_2.node.miner = true;
    conf_node_2.events_observers.clear();

    let node_1_sk = Secp256k1PrivateKey::from_seed(&conf.node.local_peer_seed);
    let node_1_pk = StacksPublicKey::from_private(&node_1_sk);

    conf_node_2.node.working_dir = format!("{}-1", conf_node_2.node.working_dir);

    conf_node_2.node.set_bootstrap_nodes(
        format!("{}@{}", &node_1_pk.to_hex(), conf.node.p2p_bind),
        conf.burnchain.chain_id,
        conf.burnchain.peer_version,
    );

    let mining_pk_1 = StacksPublicKey::from_private(&conf.miner.mining_key.unwrap());
    let mining_pk_2 = StacksPublicKey::from_private(&conf_node_2.miner.mining_key.unwrap());
    let mining_pkh_1 = Hash160::from_node_public_key(&mining_pk_1);
    let mining_pkh_2 = Hash160::from_node_public_key(&mining_pk_2);
    debug!("The mining key for miner 1 is {mining_pkh_1}");
    debug!("The mining key for miner 2 is {mining_pkh_2}");

    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    let mut run_loop_2 = boot_nakamoto::BootRunLoop::new(conf_node_2.clone()).unwrap();
    let rl2_coord_channels = run_loop_2.coordinator_channels();
    let run_loop_stopper_2 = run_loop_2.get_termination_switch();
    let Counters {
        naka_mined_blocks: blocks_mined2,
        naka_proposed_blocks: blocks_proposed2,
        naka_submitted_commits: commits_2,
        naka_skip_commit_op: rl2_skip_commit_op,
        ..
    } = run_loop_2.counters();
    let rl2_counters = run_loop_2.counters();
    let rl1_counters = signer_test.running_nodes.counters.clone();

    signer_test.boot_to_epoch_3();
    let run_loop_2_thread = thread::Builder::new()
        .name("run_loop_2".into())
        .spawn(move || run_loop_2.start(None, 0))
        .unwrap();

    let pre_nakamoto_peer_1_height = get_chain_info(&conf).stacks_tip_height;

    wait_for(200, || {
        let Some(node_1_info) = get_chain_info_opt(&conf) else {
            return Ok(false);
        };
        let Some(node_2_info) = get_chain_info_opt(&conf_node_2) else {
            return Ok(false);
        };
        Ok(node_1_info.stacks_tip_height == node_2_info.stacks_tip_height)
    })
    .expect("Timed out waiting for follower to catch up to the miner");

    info!("------------------------- Reached Epoch 3.0 -------------------------");

    // due to the random nature of mining sortitions, the way this test is structured
    //  is that we keep track of how many tenures each miner produced, and once enough sortitions
    //  have been produced such that each miner has produced 3 tenures, we stop and check the
    //  results at the end
    let mut btc_blocks_mined = 0;
    let mut miner_1_tenures = 0u64;
    let mut miner_2_tenures = 0u64;
    let mut fork_initiated = false;
    let mut min_miner_1_tenures = u64::MAX;
    let mut min_miner_2_tenures = u64::MAX;
    let mut ignore_block = 0;

    let mut miner_1_blocks = 0;
    let mut miner_2_blocks = 0;
    let mut min_miner_2_blocks = 0;
    let mut last_sortition_winner: Option<u64> = None;
    let mut miner_2_won_2_in_a_row = false;

    let commits_1 = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let rl1_skip_commit_op = signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();

    let sortdb = SortitionDB::open(
        &conf.get_burn_db_file_path(),
        false,
        conf.get_burnchain().pox_constants,
    )
    .unwrap();

    info!("-------- Waiting miner 2 to catch up to miner 1 --------");

    // Wait for miner 2 to catch up to miner 1
    // (note: use a high timeout to avoid potential failing on github workflow)
    wait_for(600, || {
        let info_1 = get_chain_info(&conf);
        let info_2 = get_chain_info(&conf_node_2);
        Ok(info_1.stacks_tip_height == info_2.stacks_tip_height)
    })
    .expect("Timed out waiting for miner 2 to catch up to miner 1");

    info!("-------- Miner 2 caught up to miner 1 --------");

    // Pause block commits
    rl1_skip_commit_op.set(true);
    rl2_skip_commit_op.set(true);

    let info_before = get_chain_info(&conf);

    // Mine the first block
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        180,
        || {
            let info_1 = get_chain_info(&conf);
            Ok(info_1.stacks_tip_height > info_before.stacks_tip_height)
        },
    )
    .expect("Timed out waiting for new Stacks block to be mined");

    info!("-------- Mined first block, wait for block commits --------");

    let info_before = get_chain_info(&conf);

    // Unpause block commits and wait for both miners' commits
    rl1_skip_commit_op.set(false);
    rl2_skip_commit_op.set(false);

    // Ensure that both miners' commits point at the stacks tip
    wait_for(60, || {
        let last_committed_1 = rl1_counters
            .naka_submitted_commit_last_stacks_tip
            .load(Ordering::SeqCst);
        let last_committed_2 = rl2_counters
            .naka_submitted_commit_last_stacks_tip
            .load(Ordering::SeqCst);
        Ok(last_committed_1 >= info_before.stacks_tip_height
            && last_committed_2 >= info_before.stacks_tip_height)
    })
    .expect("Timed out waiting for block commits");

    while miner_1_tenures < min_miner_1_tenures || miner_2_tenures < min_miner_2_tenures {
        if btc_blocks_mined >= max_nakamoto_tenures {
            panic!("Produced {btc_blocks_mined} sortitions, but didn't cover the test scenarios, aborting");
        }

        // Mine a block and wait for it to be processed, unless we are in a
        // forked tenure, in which case, just wait for the block proposal
        let mined_before_1 = blocks_mined1.load(Ordering::SeqCst);
        let mined_before_2 = blocks_mined2.load(Ordering::SeqCst);
        let proposed_before_2 = blocks_proposed2.load(Ordering::SeqCst);
        let proposed_before_1 = signer_test
            .running_nodes
            .counters
            .naka_proposed_blocks
            .load(Ordering::SeqCst);

        info!(
            "Next tenure checking";
            "fork_initiated?" => fork_initiated,
            "miner_1_tenures" => miner_1_tenures,
            "miner_2_tenures" => miner_2_tenures,
            "min_miner_1_tenures" => min_miner_2_tenures,
            "min_miner_2_tenures" => min_miner_2_tenures,
            "proposed_before_1" => proposed_before_1,
            "proposed_before_2" => proposed_before_2,
            "mined_before_1" => mined_before_1,
            "mined_before_2" => mined_before_2,
        );

        // Pause block commits
        rl1_skip_commit_op.set(true);
        rl2_skip_commit_op.set(true);

        let tip_before = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        let commits_before_1 = commits_1.load(Ordering::SeqCst);
        let commits_before_2 = commits_2.load(Ordering::SeqCst);

        next_block_and(
            &mut signer_test.running_nodes.btc_regtest_controller,
            60,
            || {
                let mined_1 = blocks_mined1.load(Ordering::SeqCst);
                let mined_2 = blocks_mined2.load(Ordering::SeqCst);
                let proposed_2 = blocks_proposed2.load(Ordering::SeqCst);

                Ok((fork_initiated && proposed_2 > proposed_before_2)
                    || mined_1 > mined_before_1
                    || mined_2 > mined_before_2)
            },
        )
        .expect("Timed out waiting for tenure change Stacks block");
        btc_blocks_mined += 1;

        // Unpause block commits
        info!("Unpausing block commits");
        rl1_skip_commit_op.set(false);
        rl2_skip_commit_op.set(false);

        // Wait for the block to be processed and the block commits to be submitted
        wait_for(60, || {
            let tip_after = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
            // Ensure that both block commits have been sent before continuing
            let commits_after_1 = commits_1.load(Ordering::SeqCst);
            let commits_after_2 = commits_2.load(Ordering::SeqCst);
            Ok(commits_after_1 > commits_before_1
                && commits_after_2 > commits_before_2
                && tip_after.consensus_hash != tip_before.consensus_hash)
        })
        .expect("Sortition DB tip did not change");

        let tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        info!("tip_after: {:?}", tip_sn);
        let miner = match tip_sn.miner_pk_hash {
            Some(pk_hash) => {
                if pk_hash == mining_pkh_1 {
                    1
                } else {
                    2
                }
            }
            None => {
                panic!("No sortition found");
            }
        };
        info!("Next tenure mined by miner {miner}");

        if let Some(last_sortition_winner) = last_sortition_winner {
            if last_sortition_winner == miner && miner == 2 {
                miner_2_won_2_in_a_row = true;
            } else {
                miner_2_won_2_in_a_row = false;
            }
        }
        last_sortition_winner = Some(miner);

        if miner == 1 && miner_1_tenures == 0 {
            // Setup miner 2 to ignore a block in this tenure
            ignore_block = pre_nakamoto_peer_1_height
                + (btc_blocks_mined - 1) * (inter_blocks_per_tenure + 1)
                + 3;
            set_ignore_block(ignore_block, &conf_node_2.node.working_dir);

            // Ensure that miner 2 runs at least one more tenure
            min_miner_2_tenures = miner_2_tenures + 1;
            fork_initiated = true;
            min_miner_2_blocks = miner_2_blocks;
        }
        if miner == 2 && miner_2_tenures == min_miner_2_tenures {
            // This is the forking tenure. Ensure that miner 1 runs one more
            // tenure after this to validate that it continues to build off of
            // the proper block.
            min_miner_1_tenures = miner_1_tenures + 1;
        }

        let mut blocks = inter_blocks_per_tenure;
        // mine (or attempt to mine) the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            let mined_before_1 = blocks_mined1.load(Ordering::SeqCst);
            let mined_before_2 = blocks_mined2.load(Ordering::SeqCst);
            let proposed_before_2 = blocks_proposed2.load(Ordering::SeqCst);

            info!(
                "Mining interim blocks";
                "fork_initiated?" => fork_initiated,
                "miner_1_tenures" => miner_1_tenures,
                "miner_2_tenures" => miner_2_tenures,
                "min_miner_1_tenures" => min_miner_2_tenures,
                "min_miner_2_tenures" => min_miner_2_tenures,
                "proposed_before_2" => proposed_before_2,
                "mined_before_1" => mined_before_1,
                "mined_before_2" => mined_before_2,
            );

            // submit a tx so that the miner will mine an extra block
            let sender_nonce = (btc_blocks_mined - 1) * inter_blocks_per_tenure + interim_block_ix;
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                signer_test.running_nodes.conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            // This may fail if the forking miner wins too many tenures and this account's
            // nonces get too high (TooMuchChaining)
            match submit_tx_fallible(&http_origin, &transfer_tx) {
                Ok(_) => {
                    wait_for(60, || {
                        let mined_1 = blocks_mined1.load(Ordering::SeqCst);
                        let mined_2 = blocks_mined2.load(Ordering::SeqCst);
                        let proposed_2 = blocks_proposed2.load(Ordering::SeqCst);

                        Ok((fork_initiated && proposed_2 > proposed_before_2)
                            || mined_1 > mined_before_1
                            || mined_2 > mined_before_2
                            // Special case where neither miner can mine a block:
                            || (fork_initiated && miner_2_won_2_in_a_row))
                    })
                    .expect("Timed out waiting for interim block to be mined");
                }
                Err(e) => {
                    if e.to_string().contains("TooMuchChaining") {
                        info!("TooMuchChaining error, skipping block");
                        blocks = interim_block_ix;
                        break;
                    } else {
                        panic!("Failed to submit tx: {e}");
                    }
                }
            }
            info!("Attempted to mine interim block {btc_blocks_mined}:{interim_block_ix}");
        }

        if miner == 1 {
            miner_1_tenures += 1;
            miner_1_blocks += blocks;
        } else {
            miner_2_tenures += 1;
            miner_2_blocks += blocks;
        }

        let mined_1 = blocks_mined1.load(Ordering::SeqCst);
        let mined_2 = blocks_mined2.load(Ordering::SeqCst);

        info!(
            "Miner 1 tenures: {miner_1_tenures}, Miner 2 tenures: {miner_2_tenures}, Miner 1 before: {mined_before_1}, Miner 2 before: {mined_before_2}, Miner 1 blocks: {mined_1}, Miner 2 blocks: {mined_2}",
        );

        if miner == 1 {
            assert_eq!(mined_1, mined_before_1 + blocks + 1);
        } else if miner_2_tenures < min_miner_2_tenures {
            assert_eq!(mined_2, mined_before_2 + blocks + 1);
        } else {
            // Miner 2 should have mined 0 blocks after the fork
            assert_eq!(mined_2, mined_before_2);
        }
    }

    info!(
        "New chain info 1: {:?}",
        get_chain_info(&signer_test.running_nodes.conf)
    );

    info!("New chain info 2: {:?}", get_chain_info(&conf_node_2));

    let peer_1_height = get_chain_info(&conf).stacks_tip_height;
    let peer_2_height = get_chain_info(&conf_node_2).stacks_tip_height;
    assert_eq!(peer_2_height, ignore_block - 1);
    // The height may be higher than expected due to extra transactions waiting
    // to be mined during the forking miner's tenure.
    // We cannot guarantee due to TooMuchChaining that the miner will mine inter_blocks_per_tenure
    // Must be at least the number of blocks mined by miner 1 and the number of blocks mined by miner 2
    // before the fork was initiated
    assert!(peer_1_height >= pre_nakamoto_peer_1_height + miner_1_blocks + min_miner_2_blocks);
    assert_eq!(btc_blocks_mined, miner_1_tenures + miner_2_tenures);

    let sortdb = SortitionDB::open(
        &conf_node_2.get_burn_db_file_path(),
        false,
        conf_node_2.get_burnchain().pox_constants,
    )
    .unwrap();

    let (chainstate, _) = StacksChainState::open(
        false,
        conf_node_2.burnchain.chain_id,
        &conf_node_2.get_chainstate_path_str(),
        None,
    )
    .unwrap();
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    assert_eq!(tip.stacks_block_height, ignore_block - 1);
    rl2_coord_channels
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper_2.store(false, Ordering::SeqCst);
    run_loop_2_thread.join().unwrap();
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers that accept a block locally, but that was rejected globally will accept a subsequent attempt
/// by the miner essentially reorg their prior locally accepted/signed block, i.e. the globally rejected block overrides
/// their local view.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 1 stacks block N (all signers sign it). The subsequent block N+1 is proposed, but rejected by >30% of the signers.
/// The miner then attempts to mine N+1', and all signers accept the block.
///
/// Test Assertion:
/// Stacks tip advances to N+1'
fn locally_accepted_blocks_overriden_by_global_rejection() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 3;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let short_timeout_secs = 20;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
    );

    let all_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    signer_test.boot_to_epoch_3();

    info!("------------------------- Test Mine Nakamoto Block N -------------------------");
    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will mine a stacks block
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine block N");
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height
    );
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());

    info!("------------------------- Attempt to Mine Nakamoto Block N+1 -------------------------");
    // Make half of the signers reject the block proposal by the miner to ensure its marked globally rejected
    let rejecting_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(num_signers / 2 + num_signers % 2)
        .collect();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(rejecting_signers.clone());
    test_observer::clear();
    let info_before = signer_test.get_peer_info();
    // Make a new stacks transaction to create a different block signature, but make sure to propose it
    // AFTER the signers are unfrozen so they don't inadvertently prevent the new block being accepted
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} to mine block N+1");

    let proposed_block_n_1 =
        wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+1' to be proposed");
    wait_for_block_rejections_from_signers(short_timeout_secs, &rejecting_signers)
        .expect("Timed out waiting for block rejection of N+1");
    let info_after = signer_test.get_peer_info();
    assert_eq!(info_before, info_after);

    info!("------------------------- Test Mine Nakamoto Block N+1' -------------------------");
    let info_before = signer_test.get_peer_info();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(Vec::new());
    test_observer::clear();

    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} to mine block N+1'");

    let block_n_1_prime = wait_for_block_pushed_by_miner_key(
        short_timeout_secs,
        info_before.stacks_tip_height + 1,
        &miner_pk,
    )
    .expect("Timed out waiting for block N+1' to be mined");

    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1
    );
    assert_eq!(info_after.stacks_tip, block_n_1_prime.header.block_hash());
    assert_ne!(block_n_1_prime, proposed_block_n_1);

    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers that reject a block locally, but that was accepted globally will accept
/// a subsequent block built on top of the accepted block
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 1 stacks block N (all signers sign it). The subsequent block N+1 is proposed, but rejected by <30% of the signers.
/// The miner then attempts to mine N+2, and all signers accept the block.
///
/// Test Assertion:
/// Stacks tip advances to N+2
fn locally_rejected_blocks_overriden_by_global_acceptance() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 3;

    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
    );

    let all_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let short_timeout = 30;
    signer_test.boot_to_epoch_3();

    info!("------------------------- Test Mine Nakamoto Block N -------------------------");
    let info_before = signer_test.get_peer_info();

    // submit a tx so that the miner will mine a stacks block N
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine block N");
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1
    );
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());

    info!("------------------------- Mine Nakamoto Block N+1 -------------------------");
    // Make less than 30% of the signers reject the block and ensure it is STILL marked globally accepted
    let rejecting_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(num_signers * 3 / 10)
        .collect();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(rejecting_signers.clone());
    test_observer::clear();

    // submit a tx so that the miner will mine a stacks block N+1
    let info_before = signer_test.get_peer_info();
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine block N+1");
    // The rejecting signers will reject the block, but it will still be accepted globally
    wait_for_block_rejections_from_signers(short_timeout, &rejecting_signers)
        .expect("Timed out waiting for block rejection of N+1");
    let block_n_1 =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+1 to be mined");

    // Assert the block was mined and the tip advanced to N+1
    let info_after = signer_test.get_peer_info();
    assert_eq!(info_after.stacks_tip, block_n_1.header.block_hash());
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1
    );

    info!("------------------------- Test Mine Nakamoto Block N+2 -------------------------");
    // Ensure that all signers accept the block proposal N+2
    let info_before = signer_test.get_peer_info();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(Vec::new());

    // submit a tx so that the miner will mine a stacks block N+2 and ensure ALL signers accept it
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} in to mine block N+2");
    let block_n_2 =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+2 to be pushed");
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height,
    );
    assert_eq!(info_after.stacks_tip, block_n_2.header.block_hash());
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers that have accepted a locally signed block N+1 built in tenure A can sign a block proposed during a
/// new tenure B built upon the last globally accepted block N if the timeout is exceeded, i.e. a reorg can occur at a tenure boundary.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 1 stacks block N (all signers sign it). The subsequent block N+1 is proposed, but <30% accept it. The remaining signers
/// do not make a decision on the block. A new tenure begins and the miner proposes a new block N+1' which all signers accept.
///
/// Test Assertion:
/// Stacks tip advances to N+1'
fn reorg_locally_accepted_blocks_across_tenures_succeeds() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 2;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
        |config| {
            // Just accept all reorg attempts
            config.tenure_last_block_proposal_timeout = Duration::from_secs(0);
        },
        |config| {
            config.miner.block_commit_delay = Duration::from_secs(0);
        },
        None,
        None,
    );
    let all_signers = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    signer_test.boot_to_epoch_3();
    info!("------------------------- Starting Tenure A -------------------------");
    info!("------------------------- Test Mine Nakamoto Block N -------------------------");
    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will mine a stacks block
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let txid = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");
    assert!(block_n
        .txs
        .iter()
        .any(|tx| { tx.txid().to_string() == txid }));
    // Ensure that the block was accepted globally so the stacks tip has advanced to N
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height
    );
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());

    info!("------------------------- Attempt to Mine Nakamoto Block N+1 -------------------------");
    // Make more than >70% of the signers ignore the block proposal to ensure it it is not globally accepted/rejected
    let ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(num_signers * 7 / 10)
        .collect();
    let non_ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .skip(num_signers * 7 / 10)
        .collect();
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(ignoring_signers.clone());
    // Clear the stackerdb chunks
    test_observer::clear();

    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will ATTEMPT to mine a stacks block N+1
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} in to attempt to mine block N+1");
    let block_n_1_proposal =
        wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+1 to be proposed");
    // Make sure that the non ignoring signers do actually accept it though
    wait_for_block_acceptance_from_signers(
        30,
        &block_n_1_proposal.header.signer_signature_hash(),
        &non_ignoring_signers,
    )
    .expect("Timed out waiting for block acceptances of N+1");
    let info_after = signer_test.get_peer_info();
    assert_eq!(info_after, info_before);
    assert_ne!(
        block_n_1_proposal.header.signer_signature_hash(),
        block_n.header.signer_signature_hash()
    );

    info!("------------------------- Starting Tenure B -------------------------");
    test_observer::clear();
    // Start a new tenure and ensure the miner can propose a new block N+1' that is accepted by all signers
    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    info!(
        "------------------------- Mine Nakamoto Block N+1' in Tenure B -------------------------"
    );
    let info_before = signer_test.get_peer_info();
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(Vec::new());

    let block_n_1_prime =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+1' to be mined");
    // Ensure that the block was accepted globally so the stacks tip has advanced to N+1' (even though they signed a sister block in the prior tenure)
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height
    );
    assert_eq!(info_after.stacks_tip, block_n_1_prime.header.block_hash());
    assert_ne!(
        block_n_1_prime.header.signer_signature_hash(),
        block_n_1_proposal.header.signer_signature_hash()
    );

    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers that have accepted a locally signed block N+1 built in tenure A cannot sign a block proposed during a
/// new tenure B built upon the last globally accepted block N if the timeout is not exceeded, i.e. a reorg cannot occur at a tenure boundary
/// before the specified timeout has been exceeded.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 1 stacks block N (all signers sign it). The subsequent block N+1 is proposed, but <30% accept it. The remaining signers
/// do not make a decision on the block. A new tenure begins and the miner proposes a new block N+1' which all signers reject as the timeout
/// has not been exceeded.
///
/// Test Assertion:
/// Stacks tip remains at N.
fn reorg_locally_accepted_blocks_across_tenures_fails() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 2;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
        |config| {
            // Do not alow any reorg attempts essentially
            config.tenure_last_block_proposal_timeout = Duration::from_secs(100_000);
        },
        |_| {},
        None,
        None,
    );
    let all_signers = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    signer_test.boot_to_epoch_3();
    info!("------------------------- Starting Tenure A -------------------------");
    info!("------------------------- Test Mine Nakamoto Block N -------------------------");
    let info_before = signer_test.get_peer_info();

    // submit a tx so that the miner will mine a stacks block
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine block N");
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");

    // Ensure that the block was accepted globally so the stacks tip has advanced to N
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height
    );
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());

    info!("------------------------- Attempt to Mine Nakamoto Block N+1 -------------------------");
    // Make more than >70% of the signers ignore the block proposal to ensure it it is not globally accepted/rejected
    let ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(num_signers * 7 / 10)
        .collect();
    let non_ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .skip(num_signers * 7 / 10)
        .collect();
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(ignoring_signers.clone());
    // Clear the stackerdb chunks
    test_observer::clear();

    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will ATTEMPT to mine a stacks block N+1
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);

    info!("Submitted tx {tx} in to attempt to mine block N+1");
    let block_n_1 = wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
        .expect("Timed out waiting for block N+1 to be proposed");
    wait_for_block_acceptance_from_signers(
        30,
        &block_n_1.header.signer_signature_hash(),
        &non_ignoring_signers,
    )
    .expect("Timed out waiting for block acceptances of N+1");

    let info_after = signer_test.get_peer_info();
    // Ensure that the block was NOT accepted globally so the stacks tip has NOT advanced to N+1
    assert_eq!(info_after, info_before);

    info!("------------------------- Starting Tenure B -------------------------");
    let info_before = signer_test.get_peer_info();

    // Clear the test observer so any old rejections are not counted
    test_observer::clear();

    // Start a new tenure and ensure the we see the expected rejections
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);
    wait_for_block_rejections_from_signers(30, &non_ignoring_signers)
        .expect("Timed out waiting for block rejections of N+1");

    let info_after = signer_test.get_peer_info();
    // Ensure that the block was NOT accepted globally so the stacks tip has NOT advanced to N+1'
    assert_eq!(info_after.stacks_tip, info_before.stacks_tip);
}

#[test]
#[ignore]
/// Test that when 70% of signers accept a block, mark it globally accepted, but a miner ends its tenure
/// before it receives these signatures, the miner can recover in the following tenure.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines 1 stacks block N (all signers sign it). The subsequent block N+1 is proposed, but >70% accept it.
/// The signers delay broadcasting the block and the miner ends its tenure before it receives these signatures. The
/// miner will propose an invalid block N+1' which all signers reject. The broadcast delay is removed and the miner
/// proposes a new block N+2 which all signers accept.
///
/// Test Assertion:
/// Stacks tip advances to N+2
fn miner_recovers_when_broadcast_block_delay_across_tenures_occurs() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 3;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
        |_config| {},
        |config| {
            // Accept all block proposals
            config.connection_options.block_proposal_max_age_secs = u64::MAX;
        },
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    signer_test.boot_to_epoch_3();

    info!("------------------------- Starting Tenure A -------------------------");
    info!("------------------------- Test Mine Nakamoto Block N -------------------------");

    // wait until we get a sortition.
    // we might miss a block-commit at the start of epoch 3
    let burnchain = signer_test.running_nodes.conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    wait_for(30, || {
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(tip.sortition)
    })
    .expect("Timed out waiting for sortition");

    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will mine a stacks block
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} in to mine block N");
    sender_nonce += 1;
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");

    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_before.stacks_tip_height + 1,
        info_after.stacks_tip_height
    );
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());

    info!("------------------------- Attempt to Mine Nakamoto Block N+1 -------------------------");
    // Propose a valid block, but force the miner to ignore the returned signatures and delay the block being
    // broadcasted to the miner so it can end its tenure before block confirmation obtained
    // Clear the stackerdb chunks
    info!("Forcing miner to ignore block responses for block N+1");
    TEST_IGNORE_SIGNERS.set(true);
    info!("Delaying signer block N+1 broadcasting to the miner");
    TEST_PAUSE_BLOCK_BROADCAST.set(true);
    test_observer::clear();
    let info_before = signer_test.get_peer_info();

    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    sender_nonce += 1;

    let tx = submit_tx(&http_origin, &transfer_tx);

    info!("Submitted tx {tx} in to attempt to mine block N+1");
    let block_n_1 = wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
        .expect("Timed out waiting for block N+1 to be proposed");
    let all_signers = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    wait_for_block_global_acceptance_from_signers(
        30,
        &block_n_1.header.signer_signature_hash(),
        &all_signers,
    )
    .expect("Timed out waiting for block N+1 to be accepted by signers");

    // Ensure that the block was not yet broadcasted to the miner so the stacks tip has NOT advanced to N+1
    let info_after = signer_test.get_peer_info();
    assert_eq!(info_after, info_before);

    info!("------------------------- Starting Tenure B -------------------------");
    test_observer::clear();
    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    info!(
        "------------------------- Attempt to Mine Nakamoto Block N+1' -------------------------"
    );
    // Wait for the miner to propose a new invalid block N+1'
    let block_n_1_prime = wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
        .expect("Timed out waiting for block N+1' to be proposed");
    assert_ne!(
        block_n_1_prime.header.signer_signature_hash(),
        block_n_1.header.signer_signature_hash()
    );
    info!("Allowing miner to accept block responses again. ");
    TEST_IGNORE_SIGNERS.set(false);
    info!("Allowing signers to broadcast block N+1 to the miner");
    TEST_PAUSE_BLOCK_BROADCAST.set(false);

    // Assert the N+1' block was rejected
    wait_for_block_global_rejection(
        30,
        block_n_1_prime.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Timed out waiting for block N+1' to be rejected");

    // Induce block N+2 to get mined
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );

    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} in to attempt to mine block N+2");

    info!("------------------------- Asserting a both N+1 and N+2 are accepted -------------------------");
    let block_n_2 =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 2, &miner_pk)
            .expect("Timed out waiting for block N+2 to be mined");

    let info_after = signer_test.get_peer_info();
    assert_eq!(
        block_n_2.header.parent_block_id,
        block_n_1.header.block_id()
    );
    assert_eq!(info_after.stacks_tip, block_n_2.header.block_hash());
    assert_eq!(
        info_before.stacks_tip_height + 2,
        info_after.stacks_tip_height
    );
}

/// Test a scenario where:
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure and proposes a block N with a TenureChangePayload
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B but its proposed blocks are rejected by the signers.
/// Mine 2 empty burn blocks (simulate fast blocks scenario)
/// Miner 2 proposes block N+1 with a TenureChangePayload
/// Signers accept and the stacks tip advances to N+1
/// Miner 2 proposes block N+2 with a TenureExtend
/// Signers accept and the stacks tip advances to N+2
/// Miner 2 proposes block N+3 with a TokenTransfer
/// Signers accept and the stacks tip advances to N+3
/// Mine an empty burn block
/// Miner 2 proposes block N+4 with a TenureExtend
/// Signers accept and the chain advances to N+4
/// Miner 1 wins the next tenure and proposes a block N+5 with a TenureChangePayload
/// Signers accept and the chain advances to N+5
/// Asserts:
/// - Block N+1 contains the TenureChangePayload
/// - Block N+2 contains the TenureExtend
/// - Block N+3 contains the TokenTransfer
/// - Block N+4 contains the TenureExtend
/// - Block N+5 contains the TenureChangePayload
/// - The stacks tip advances to N+5
#[test]
#[ignore]
fn continue_after_fast_block_no_sortition() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 1;

    let mut miners = MultipleMinerTest::new(num_signers, num_txs);
    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    let (_, miner_pk_2) = miners.get_miner_public_keys();

    let Counters {
        naka_rejected_blocks: rl1_rejections,
        naka_skip_commit_op: rl1_skip_commit_op,
        naka_submitted_commits: rl1_commits,
        naka_mined_blocks: blocks_mined1,
        ..
    } = miners.signer_test.running_nodes.counters.clone();

    let Counters {
        naka_skip_commit_op: rl2_skip_commit_op,
        naka_submitted_commits: rl2_commits,
        naka_mined_blocks: blocks_mined2,
        ..
    } = miners.rl2_counters.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let all_signers = miners
        .signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to start Tenure A");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Make Signers Reject All Subsequent Proposals -------------------------");

    let stacks_height_before = miners.get_peer_stacks_tip_height();

    // Make all signers ignore block proposals
    let ignoring_signers = all_signers.to_vec();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(ignoring_signers);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    let rejections_before = rl1_rejections.load(Ordering::SeqCst);
    miners.submit_commit_miner_2(&sortdb);
    let burn_height_before = get_burn_height();

    info!("------------------------- Miner 2 Mines an Empty Tenure B -------------------------";
        "burn_height_before" => burn_height_before,
        "rejections_before" => rejections_before,
    );
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 60)
        .expect("Failed to start Tenure B");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("----- Waiting for block rejections -----");
    let miner_2_block = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Failed to get Miner 2's Block Proposal");
    wait_for_block_global_rejection(
        30,
        miner_2_block.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Failed to get expected block rejections for Miner 2's block proposal");

    // Mine another couple burn blocks and ensure there is _no_ sortition
    info!("------------------------- Mine Two Burn Block(s) with No Sortitions -------------------------");
    for _ in 0..2 {
        let blocks_processed_before_1 = blocks_mined1.load(Ordering::SeqCst);
        let blocks_processed_before_2 = blocks_mined2.load(Ordering::SeqCst);
        let commits_before_1 = rl1_commits.load(Ordering::SeqCst);
        let commits_before_2 = rl2_commits.load(Ordering::SeqCst);

        miners
            .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
            .expect("Failed to mine empty sortition");
        btc_blocks_mined += 1;

        assert_eq!(rl1_commits.load(Ordering::SeqCst), commits_before_1);
        assert_eq!(rl2_commits.load(Ordering::SeqCst), commits_before_2);
        assert_eq!(
            blocks_mined1.load(Ordering::SeqCst),
            blocks_processed_before_1
        );
        assert_eq!(
            blocks_mined2.load(Ordering::SeqCst),
            blocks_processed_before_2
        );

        // assure we have NO sortition
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        assert!(!tip.sortition);
    }

    // Verify that no Stacks blocks have been mined (signers are ignoring) and no commits have been submitted by either miner
    let stacks_height = miners.get_peer_stacks_tip_height();
    assert_eq!(stacks_height, stacks_height_before);
    let stacks_height_before = stacks_height;

    info!("------------------------- Enabling Signer Block Proposals -------------------------";
        "stacks_height" => stacks_height_before,
    );
    // Allow signers to respond to proposals again
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(Vec::new());

    info!("------------------------- Wait for Miner B's Block N+1 -------------------------";
        "stacks_height_before" => %stacks_height_before);

    // wait for the new block to be processed
    // Since we may be proposing a ton of the same height, cannot use wait_for_block_pushed_by_miner_key for block N+1.
    let miner_2_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Did not mine Miner 2's Block N+1");

    info!(
        "------------------------- Verify Tenure Change Tx in Miner B's Block N+1 -------------------------"
    );
    assert_eq!(
        miner_2_block_n_1
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::BlockFound
    );

    info!("------------------------- Wait for Miner B's Block N+2 -------------------------");

    let miner_2_block_n_2 =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 2, &miner_pk_2)
            .expect("Did not mine Miner 2's Block N+2");
    assert_eq!(
        miners.get_peer_stacks_tip(),
        miner_2_block_n_2.header.block_hash()
    );

    info!("------------------------- Verify Miner B's Block N+2 -------------------------");
    assert_eq!(
        miner_2_block_n_2
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::Extended
    );

    info!("------------------------- Wait for Miner B's Block N+3 -------------------------");

    // submit a tx so that the miner will mine an extra block
    let txid = miners
        .send_and_mine_transfer_tx(30)
        .expect("Timed out waiting to mine Block N+3");

    info!("------------------------- Verify Miner B's Block N+3 -------------------------");

    let block_n_3 = wait_for_block_pushed_by_miner_key(30, stacks_height_before + 3, &miner_pk_2)
        .expect("Did not mine Miner 2's Block N+3");
    assert!(block_n_3
        .txs
        .iter()
        .any(|tx| { tx.txid().to_string() == txid }));

    info!("------------------------- Mine An Empty Sortition -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::Extended, 60)
        .expect("Failed to mine Miner B's Tenure Extend in Block N+4");
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    assert!(!tip.sortition);
    btc_blocks_mined += 1;

    info!("------------------------- Unpause Miner A's Block Commits -------------------------");
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Run Miner A's Tenure -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine Miner A's Tenure Change in Block N+5");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner A won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    let peer_info = miners.get_peer_info();

    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(peer_info.stacks_tip_height, starting_peer_height + 6);

    info!("------------------------- Shutdown -------------------------");
    miners.shutdown();
}

#[test]
#[ignore]
/// Test that we can mine a tenure extend and then continue mining afterwards.
fn continue_after_tenure_extend() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let send_amt = 100;
    let send_fee = 180;
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, (send_amt + send_fee) * 5)]);
    let timeout = Duration::from_secs(200);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    let burnchain = signer_test.running_nodes.conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    signer_test.boot_to_epoch_3();
    info!("------------------------- Mine A Normal Tenure -------------------------");
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);

    info!("------------------------- Pause Block Commits-------------------------");
    signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .set(true);
    info!("------------------------- Flush Pending Commits -------------------------");
    // Mine a couple blocks to flush the last submitted commit out.
    let peer_info = signer_test.get_peer_info();
    let burn_height_before = peer_info.burn_block_height;
    let stacks_height_before = peer_info.stacks_tip_height;
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(2);
    wait_for(30, || {
        let peer_info = signer_test.get_peer_info();
        Ok(peer_info.burn_block_height > burn_height_before + 1)
    })
    .expect("Timed out waiting for burn block height to increase");
    // assure we have NO sortition
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    assert!(!tip.sortition);

    info!("------------------------- Extend Tenure -------------------------");
    wait_for_tenure_change_tx(30, TenureChangeCause::Extended, stacks_height_before + 2)
        .expect("Timed out waiting for tenure change tx");

    // Verify that the miner can continue mining in the tenure with the tenure extend
    info!("------------------------- Mine After Tenure Extend -------------------------");
    for sender_nonce in 0..5 {
        let stacks_height_before = signer_test.get_peer_info().stacks_tip_height;
        // submit a tx so that the miner will mine an extra block
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            sender_nonce,
            send_fee,
            signer_test.running_nodes.conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        submit_tx(&http_origin, &transfer_tx);
        info!("Submitted transfer tx and waiting for block proposal");
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk)
            .expect("Timed out waiting to mine block");
    }

    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers can successfully sign a block proposal in the 0th tenure of a reward cycle
/// This ensures there is no race condition in the /v2/pox endpoint which could prevent it from updating
/// on time, possibly triggering an "off by one" like behaviour in the 0th tenure.
///
fn signing_in_0th_tenure_of_reward_cycle() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(num_signers, vec![]);
    let signer_public_keys = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    let long_timeout = Duration::from_secs(200);
    signer_test.boot_to_epoch_3();
    let curr_reward_cycle = signer_test.get_current_reward_cycle();
    let next_reward_cycle = curr_reward_cycle + 1;
    // Mine until the boundary of the first full Nakamoto reward cycles (epoch 3 starts in the middle of one)
    let next_reward_cycle_height_boundary = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(next_reward_cycle)
        .saturating_sub(1);

    info!("------------------------- Advancing to {next_reward_cycle} Boundary at Block {next_reward_cycle_height_boundary} -------------------------");
    signer_test.run_until_burnchain_height_nakamoto(
        long_timeout,
        next_reward_cycle_height_boundary,
        num_signers,
    );

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let get_v3_signer = |pubkey: &Secp256k1PublicKey, reward_cycle: u64| {
        let url = &format!(
            "{http_origin}/v3/signer/{pk}/{reward_cycle}",
            pk = pubkey.to_hex()
        );
        info!("Send request: GET {url}");
        reqwest::blocking::get(url)
            .unwrap_or_else(|e| panic!("GET request failed: {e}"))
            .json::<GetSignerResponse>()
            .unwrap()
            .blocks_signed
    };

    assert_eq!(signer_test.get_current_reward_cycle(), curr_reward_cycle);

    for signer in &signer_public_keys {
        let blocks_signed = get_v3_signer(signer, next_reward_cycle);
        assert_eq!(blocks_signed, 0);
    }

    info!("------------------------- Enter Reward Cycle {next_reward_cycle} -------------------------");
    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    for signer in &signer_public_keys {
        let blocks_signed = get_v3_signer(signer, next_reward_cycle);
        assert_eq!(blocks_signed, 0);
    }
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);

    wait_for(30, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .unwrap();

    let block_mined = test_observer::get_mined_nakamoto_blocks()
        .last()
        .unwrap()
        .clone();
    // Must ensure that the signers that signed the block have their blocks_signed updated appropriately
    for signature in &block_mined.signer_signature {
        let signer = signer_public_keys
            .iter()
            .find(|pk| {
                pk.verify(block_mined.signer_signature_hash.as_bytes(), signature)
                    .unwrap()
            })
            .expect("Unknown signer signature");
        let blocks_signed = get_v3_signer(signer, next_reward_cycle);
        assert_eq!(blocks_signed, 1);
    }
    assert_eq!(signer_test.get_current_reward_cycle(), next_reward_cycle);
}

/// This test involves two miners with a custom chain id, each mining tenures with 6 blocks each.
/// Half of the signers are attached to each miner, so the test also verifies that
/// the signers' messages successfully make their way to the active miner.
#[test]
#[ignore]
fn multiple_miners_with_custom_chain_id() {
    let num_signers = 5;
    let max_nakamoto_tenures = 20;
    let inter_blocks_per_tenure = 5;
    let num_txs = max_nakamoto_tenures * inter_blocks_per_tenure;

    let chain_id = 0x87654321;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| signer_config.chain_id = Some(chain_id),
        |config| {
            config.burnchain.chain_id = chain_id;
        },
        |_| {},
    );
    let (conf_1, conf_2) = miners.get_node_configs();

    miners.boot_to_epoch_3();

    let pre_nakamoto_peer_1_height = get_chain_info(&conf_1).stacks_tip_height;

    // due to the random nature of mining sortitions, the way this test is structured
    //  is that we keep track of how many tenures each miner produced, and once enough sortitions
    //  have been produced such that each miner has produced 3 tenures, we stop and check the
    //  results at the end
    let rl1_counters = miners.signer_test.running_nodes.counters.clone();
    let blocks_mined1 = miners
        .signer_test
        .running_nodes
        .counters
        .naka_mined_blocks
        .clone();

    let rl2_counters = miners.rl2_counters.clone();
    let blocks_mined2 = rl2_counters.naka_mined_blocks.clone();

    let (miner_1_pk, miner_2_pk) = miners.get_miner_public_keys();

    let mut btc_blocks_mined = 1;
    let mut miner_1_tenures = 0;
    let mut miner_2_tenures = 0;
    while !(miner_1_tenures >= 3 && miner_2_tenures >= 3) {
        if btc_blocks_mined > max_nakamoto_tenures {
            panic!("Produced {btc_blocks_mined} sortitions, but didn't cover the test scenarios, aborting");
        }
        let blocks_processed_before =
            blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst);
        miners.signer_test.mine_block_wait_on_processing(
            &[&conf_1, &conf_2],
            &[&rl1_counters, &rl2_counters],
            Duration::from_secs(30),
        );
        btc_blocks_mined += 1;

        // wait for the new block to be processed
        wait_for(60, || {
            let blocks_processed =
                blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst);
            Ok(blocks_processed > blocks_processed_before)
        })
        .unwrap();

        info!(
            "Nakamoto blocks mined: {}",
            blocks_mined1.load(Ordering::SeqCst) + blocks_mined2.load(Ordering::SeqCst)
        );

        // mine the interim blocks
        info!("Mining interim blocks");
        for interim_block_ix in 0..inter_blocks_per_tenure {
            miners
                .send_and_mine_transfer_tx(30)
                .expect("Timed out waiting to mine interim block");
            info!("Mined interim block {btc_blocks_mined}:{interim_block_ix}");
        }

        let blocks = get_nakamoto_headers(&conf_1);
        let mut seen_burn_hashes = HashSet::new();
        miner_1_tenures = 0;
        miner_2_tenures = 0;
        for header in blocks.iter() {
            if seen_burn_hashes.contains(&header.burn_header_hash) {
                continue;
            }
            seen_burn_hashes.insert(header.burn_header_hash);

            let header = header.anchored_header.as_stacks_nakamoto().unwrap();
            if miner_1_pk
                .verify(
                    header.miner_signature_hash().as_bytes(),
                    &header.miner_signature,
                )
                .unwrap()
            {
                miner_1_tenures += 1;
            }
            if miner_2_pk
                .verify(
                    header.miner_signature_hash().as_bytes(),
                    &header.miner_signature,
                )
                .unwrap()
            {
                miner_2_tenures += 1;
            }
        }
        info!("Miner 1 tenures: {miner_1_tenures}, Miner 2 tenures: {miner_2_tenures}");
    }

    let chain_info_1 = get_chain_info(&conf_1);
    let chain_info_2 = get_chain_info(&conf_2);
    info!("New chain info 1: {chain_info_1:?}");
    info!("New chain info 2: {chain_info_2:?}");

    let peer_1_height = chain_info_1.stacks_tip_height;
    let peer_2_height = chain_info_2.stacks_tip_height;
    info!("Peer height information"; "peer_1" => peer_1_height, "peer_2" => peer_2_height, "pre_naka_height" => pre_nakamoto_peer_1_height);
    assert_eq!(peer_1_height, peer_2_height);
    assert_eq!(
        peer_1_height,
        pre_nakamoto_peer_1_height + (btc_blocks_mined - 1) * (inter_blocks_per_tenure + 1)
    );
    assert_eq!(btc_blocks_mined, miner_1_tenures + miner_2_tenures);

    // Verify both nodes have the correct chain id;
    assert_eq!(chain_info_1.network_id, chain_id);
    assert_eq!(chain_info_2.network_id, chain_id);

    miners.shutdown();
}

#[test]
#[ignore]
/// This test checks the behavior of the `block_commit_delay_ms` configuration option.
fn block_commit_delay() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |config| {
            // make the duration long enough that the miner will be marked as malicious
            config.block_proposal_timeout = Duration::from_secs(600);
        },
        |config| {
            // Set the block commit delay to 10 minutes to ensure no block commit is sent
            config.miner.block_commit_delay = Duration::from_secs(600);
        },
        None,
        None,
    );

    signer_test.boot_to_epoch_3();

    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let commits_before = commits_submitted.load(Ordering::SeqCst);

    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .expect("Failed to mine first block");

    // Ensure that the block commit has been sent before continuing
    wait_for(60, || {
        Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
    })
    .expect("Timed out waiting for block commit after new Stacks block");

    // Prevent a block from being mined by making signers reject it.
    let all_signers = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(all_signers);

    info!("------------------------- Test Mine Burn Block  -------------------------");
    let burn_height_before = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
    let commits_before = commits_submitted.load(Ordering::SeqCst);

    // Mine a burn block and wait for it to be processed.
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let burn_height = get_chain_info(&signer_test.running_nodes.conf).burn_block_height;
            Ok(burn_height > burn_height_before)
        },
    )
    .unwrap();

    // Sleep an extra minute to ensure no block commits are sent
    sleep_ms(60_000);
    assert_eq!(commits_submitted.load(Ordering::SeqCst), commits_before);

    let blocks_before = mined_blocks.load(Ordering::SeqCst);

    info!("------------------------- Resume Signing -------------------------");
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(Vec::new());

    // Wait for a block to be mined
    wait_for(60, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .expect("Timed out waiting for block to be mined");

    // Wait for a block commit to be sent
    wait_for(60, || {
        Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
    })
    .expect("Timed out waiting for block commit after new Stacks block");

    signer_test.shutdown();
}

// Ensures that a signer that successfully submits a block to the node for validation
// will issue ConnectivityIssues rejections if a block submission times out.
// Also ensures that no other proposal gets submitted for validation if we
// are already waiting for a block submission response.
#[test]
#[ignore]
fn block_validation_response_timeout() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let timeout = Duration::from_secs(30);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.block_proposal_validation_timeout = timeout;
        },
        |_| {},
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();

    let block_proposals = signer_test
        .running_nodes
        .counters
        .naka_proposed_blocks
        .clone();

    info!("------------------------- Test Mine and Verify Confirmed Nakamoto Block -------------------------");
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);
    info!("------------------------- Test Block Validation Stalled -------------------------");
    TEST_VALIDATE_STALL.set(true);
    let validation_stall_start = Instant::now();

    let proposals_before = block_proposals.load(Ordering::SeqCst);

    // submit a tx so that the miner will attempt to mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    info!("Submitted transfer tx and waiting for block proposal");
    wait_for(30, || {
        Ok(block_proposals.load(Ordering::SeqCst) > proposals_before)
    })
    .expect("Timed out waiting for block proposal");

    assert!(
        validation_stall_start.elapsed() < timeout,
        "Test was too slow to propose another block before the timeout"
    );

    info!("------------------------- Propose Another Block Before Hitting the Timeout -------------------------");
    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        block_proposal_timeout: Duration::from_secs(100),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    block.header.timestamp = get_epoch_time_secs();

    let info_before = get_chain_info(&signer_test.running_nodes.conf);
    // Propose a block to the signers that passes initial checks but will not be submitted to the stacks node due to the submission stall
    let view = SortitionsView::fetch_view(proposal_conf, &signer_test.stacks_client).unwrap();
    block.header.pox_treatment = BitVec::ones(1).unwrap();
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.header.chain_length = info_before.stacks_tip_height + 1;

    let block_signer_signature_hash_1 = block.header.signer_signature_hash();
    signer_test.propose_block(block, timeout);

    info!("------------------------- Waiting for Timeout -------------------------");
    // Sleep the necessary timeout to make sure the validation times out.
    let elapsed = validation_stall_start.elapsed();
    let wait = timeout.saturating_sub(elapsed);
    info!("Sleeping for {} ms", wait.as_millis());
    std::thread::sleep(timeout.saturating_sub(elapsed));

    info!("------------------------- Wait for Block Rejection Due to Timeout -------------------------");
    // Verify that the signer that submits the block to the node will issue a ConnectivityIssues rejection
    wait_for(30, || {
        let chunks = test_observer::get_stackerdb_chunks();
        for chunk in chunks.into_iter().flat_map(|chunk| chunk.modified_slots) {
            let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
            else {
                continue;
            };
            let SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                reason: _reason,
                reason_code,
                signer_signature_hash,
                ..
            })) = message
            else {
                continue;
            };
            // We are waiting for the original block proposal which will have a diff signature to our
            // second proposed block.
            assert_ne!(
                signer_signature_hash, block_signer_signature_hash_1,
                "Received a rejection for the wrong block"
            );
            if matches!(reason_code, RejectCode::ConnectivityIssues(_)) {
                return Ok(true);
            }
        }
        Ok(false)
    })
    .expect("Timed out waiting for block proposal rejections");
    // Make sure our chain has still not advanced
    let info_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(info_before, info_after);
    let info_before = info_after;
    info!("Unpausing block validation");
    // Disable the stall and wait for the block to be processed successfully
    TEST_VALIDATE_STALL.set(false);
    wait_for(30, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > info_before.stacks_tip_height)
    })
    .expect("Timed out waiting for block to be processed");

    let info_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1,
    );
    info!("------------------------- Test Mine and Verify Confirmed Nakamoto Block -------------------------");
    let info_before = info_after;
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);

    wait_for(30, || {
        let info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(info.stacks_tip_height > info_before.stacks_tip_height)
    })
    .unwrap();

    let info_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1,
    );
}

// Verify that the miner timeout while waiting for signers will change accordingly
// to rejections.
#[test]
#[ignore]
fn block_validation_check_rejection_timeout_heuristic() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 20;
    let timeout = Duration::from_secs(30);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.block_proposal_validation_timeout = timeout;
        },
        |config| {
            config.miner.block_rejection_timeout_steps.clear();
            config
                .miner
                .block_rejection_timeout_steps
                .insert(0, Duration::from_secs(123));
            config
                .miner
                .block_rejection_timeout_steps
                .insert(10, Duration::from_secs(20));
            config
                .miner
                .block_rejection_timeout_steps
                .insert(15, Duration::from_secs(10));
            config
                .miner
                .block_rejection_timeout_steps
                .insert(20, Duration::from_secs(99));
        },
        None,
        None,
    );

    let all_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();

    signer_test.boot_to_epoch_3();

    // note we just use mined nakamoto_blocks as the second block is not going to be confirmed

    let mut test_rejections = |signer_split_index: usize, expected_timeout: u64| {
        let blocks_before = test_observer::get_mined_nakamoto_blocks().len();
        let (ignore_signers, reject_signers) = all_signers.split_at(signer_split_index);

        info!("------------------------- Check Rejections-based timeout with {} rejections -------------------------", reject_signers.len());

        TEST_REJECT_ALL_BLOCK_PROPOSAL.set(reject_signers.to_vec());
        TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(ignore_signers.to_vec());

        next_block_and(
            &mut signer_test.running_nodes.btc_regtest_controller,
            30,
            || Ok(test_observer::get_mined_nakamoto_blocks().len() > blocks_before),
        )
        .unwrap();

        wait_for_block_rejections_from_signers(timeout.as_secs(), &reject_signers).unwrap();

        wait_for(60, || {
            Ok(signer_test
                .running_nodes
                .counters
                .naka_miner_current_rejections
                .get()
                >= reject_signers.len() as u64)
        })
        .unwrap();
        assert_eq!(
            signer_test
                .running_nodes
                .counters
                .naka_miner_current_rejections_timeout_secs
                .get(),
            expected_timeout
        );
    };

    test_rejections(19, 123);
    test_rejections(18, 20);
    test_rejections(17, 10);
    test_rejections(16, 99);

    // reset reject/ignore
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(vec![]);
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(vec![]);

    info!("------------------------- Shutdown -------------------------");
    signer_test.shutdown();
}

/// Test scenario:
///
/// - when a signer submits a block validation request and
///   gets a 429,
/// - the signer stores the pending request
/// - and submits it again after the current block validation
///   request finishes.
#[test]
#[ignore]
fn block_validation_pending_table() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let timeout = Duration::from_secs(30);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let short_timeout = Duration::from_secs(20);

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |_| {},
        |_| {},
        None,
        None,
    );
    let db_path = signer_test.signer_configs[0].db_path.clone();
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();

    info!("----- Starting test -----";
        "db_path" => db_path.clone().to_str(),
    );
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);
    TEST_VALIDATE_DELAY_DURATION_SECS.set(30);

    let signer_db = SignerDb::new(db_path).unwrap();

    let proposals_before = signer_test.get_miner_proposal_messages().len();

    let peer_info = signer_test.get_peer_info();

    // submit a tx so that the miner will attempt to mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    info!("----- Waiting for miner to propose a block -----");

    // Wait for the miner to propose a block
    wait_for(30, || {
        Ok(signer_test.get_miner_proposal_messages().len() > proposals_before)
    })
    .expect("Timed out waiting for miner to propose a block");

    info!("----- Proposing a concurrent block -----");
    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        block_proposal_timeout: Duration::from_secs(100),
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    block.header.timestamp = get_epoch_time_secs();

    let view = SortitionsView::fetch_view(proposal_conf, &signer_test.stacks_client).unwrap();
    block.header.pox_treatment = BitVec::ones(1).unwrap();
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.header.chain_length = peer_info.stacks_tip_height + 1;
    let block_signer_signature_hash = block.header.signer_signature_hash();
    signer_test.propose_block(block.clone(), short_timeout);

    info!(
        "----- Waiting for a pending block proposal in SignerDb -----";
        "signer_signature_hash" => block_signer_signature_hash.to_hex(),
    );
    let mut last_log = Instant::now();
    last_log -= Duration::from_secs(5);
    wait_for(120, || {
        let is_pending = signer_db
            .has_pending_block_validation(&block_signer_signature_hash)
            .expect("Unexpected DBError");
        if last_log.elapsed() > Duration::from_secs(5) && !is_pending {
            let pending_block_validations = signer_db
                .get_all_pending_block_validations()
                .expect("Failed to get pending block validations");
            info!(
                "----- Waiting for pending block proposal in SignerDB -----";
                "proposed_signer_signature_hash" => block_signer_signature_hash.to_hex(),
                "pending_block_validations_len" => pending_block_validations.len(),
                "pending_block_validations" => pending_block_validations.iter()
                    .map(|p| p.signer_signature_hash.to_hex())
                    .collect::<Vec<String>>()
                    .join(", "),
            );
            last_log = Instant::now();
        }
        Ok(is_pending)
    })
    .expect("Timed out waiting for pending block proposal");

    info!("----- Waiting for pending block validation to be submitted -----");

    // Set the delay to 0 so that the block validation finishes quickly
    TEST_VALIDATE_DELAY_DURATION_SECS.set(0);

    wait_for(30, || {
        let proposal_responses = test_observer::get_proposal_responses();
        let found_proposal = proposal_responses
            .iter()
            .any(|p| p.signer_signature_hash() == block_signer_signature_hash);
        Ok(found_proposal)
    })
    .expect("Timed out waiting for pending block validation to be submitted");

    info!("----- Waiting for pending block validation to be removed -----");
    wait_for(60, || {
        let is_pending = signer_db
            .has_pending_block_validation(&block_signer_signature_hash)
            .expect("Unexpected DBError");
        Ok(!is_pending)
    })
    .expect("Timed out waiting for pending block validation to be removed");

    // for test cleanup we need to wait for block rejections
    let signer_keys = signer_test
        .signer_configs
        .iter()
        .map(|c| StacksPublicKey::from_private(&c.stacks_private_key))
        .collect::<Vec<_>>();
    wait_for_block_rejections_from_signers(30, &signer_keys)
        .expect("Timed out waiting for block rejections");

    info!("------------------------- Shutdown -------------------------");
    signer_test.shutdown();
}

/// Test scenario:
///
/// - Miner A proposes a block in tenure A
/// - While that block is pending validation,
///   Miner B proposes a new block in tenure B
/// - After A's block is validated, Miner B's block is
///   rejected (because it's a sister block)
/// - Miner B retries and successfully mines a block
#[test]
#[ignore]
fn new_tenure_while_validating_previous_scenario() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let timeout = Duration::from_secs(30);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |_| {},
        |_| {},
        None,
        None,
    );
    let db_path = signer_test.signer_configs[0].db_path.clone();
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    info!("----- Starting test -----";
        "db_path" => db_path.clone().to_str(),
    );
    signer_test.mine_and_verify_confirmed_naka_block(timeout, num_signers, true);
    TEST_VALIDATE_DELAY_DURATION_SECS.set(30);

    let proposals_before = signer_test.get_miner_proposal_messages().len();

    let peer_info_before_stall = signer_test.get_peer_info();
    let burn_height_before_stall = peer_info_before_stall.burn_block_height;
    let stacks_height_before_stall = peer_info_before_stall.stacks_tip_height;

    // STEP 1: Miner A proposes a block in tenure A

    // submit a tx so that the miner will attempt to mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    info!("----- Waiting for miner to propose a block -----");

    // Wait for the miner to propose a block
    wait_for(30, || {
        Ok(signer_test.get_miner_proposal_messages().len() > proposals_before)
    })
    .expect("Timed out waiting for miner to propose a block");

    let proposals_before = signer_test.get_miner_proposal_messages().len();
    let info_before = signer_test.get_peer_info();

    // STEP 2: Miner B proposes a block in tenure B, while A's block is pending validation

    info!("----- Mining a new BTC block -----");
    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);

    let mut last_log = Instant::now();
    last_log -= Duration::from_secs(5);
    let mut new_block_hash = None;
    wait_for(120, || {
        let proposals = signer_test.get_miner_proposal_messages();
        let new_proposal = proposals.iter().find(|p| {
            p.burn_height > burn_height_before_stall
                && p.block.header.chain_length == info_before.stacks_tip_height + 1
        });

        let has_new_proposal = new_proposal.is_some() && proposals.len() > proposals_before;
        if last_log.elapsed() > Duration::from_secs(5) && !has_new_proposal {
            info!(
                "----- Waiting for a new proposal -----";
                "proposals_len" => proposals.len(),
                "burn_height_before" => info_before.burn_block_height,
            );
            last_log = Instant::now();
        }
        if let Some(proposal) = new_proposal {
            new_block_hash = Some(proposal.block.header.signer_signature_hash());
        }
        Ok(has_new_proposal)
    })
    .expect("Timed out waiting for pending block proposal");

    info!("----- Waiting for pending block validation to be submitted -----");
    let new_block_hash = new_block_hash.unwrap();

    // Set the delay to 0 so that the block validation finishes quickly
    TEST_VALIDATE_DELAY_DURATION_SECS.set(0);

    wait_for(30, || {
        let proposal_responses = test_observer::get_proposal_responses();
        let found_proposal = proposal_responses
            .iter()
            .any(|p| p.signer_signature_hash() == new_block_hash);
        Ok(found_proposal)
    })
    .expect("Timed out waiting for pending block validation to be submitted");

    // STEP 3: Miner B is rejected, retries, and mines a block

    // Now, wait for miner B to propose a new block
    let block_pushed =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before_stall + 2, &miner_pk)
            .expect("Timed out waiting for block N+2 to be mined");
    // Ensure that we didn't tenure extend
    assert_eq!(
        block_pushed.try_get_tenure_change_payload().unwrap().cause,
        TenureChangeCause::BlockFound
    );
    let peer_info = signer_test.get_peer_info();
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before_stall + 2);
    assert_eq!(peer_info.stacks_tip, block_pushed.header.block_hash());

    info!("------------------------- Shutdown -------------------------");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that a miner will extend its tenure after the succeding miner fails to mine a block.
/// - Miner 1 wins a tenure and mines normally
/// - Miner 2 wins a tenure but fails to mine a block
/// - Miner 1 extends its tenure
fn tenure_extend_after_failed_miner() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 2;
    let block_proposal_timeout = Duration::from_secs(30);
    let tenure_extend_wait_timeout = block_proposal_timeout;

    info!("------------------------- Test Setup -------------------------");
    // partition the signer set so that ~half are listening and using node 1 for RPC and events,
    //  and the rest are using node 2

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Wins Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to start Tenure A");

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Miner 1 Mines Another Block -------------------------");
    // submit a tx so that the miner will mine an extra block
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    info!("------------------------- Pause Block Proposals -------------------------");
    TEST_MINE_STALL.set(true);
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Miner 2 Wins Tenure B, Mines No Blocks -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();

    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");

    // assure we have a successful sortition that miner B won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("------------------------- Wait for Block Proposal Timeout -------------------------");
    sleep_ms(block_proposal_timeout.as_millis() as u64 * 2);

    info!("------------------------- Miner 1 Extends Tenure A -------------------------");

    // Re-enable block mining, for both miners.
    // Since miner B has been offline, it won't be able to mine.
    TEST_MINE_STALL.set(false);

    // wait for a tenure extend block from miner 1 to be processed
    wait_for_tenure_change_tx(30, TenureChangeCause::Extended, stacks_height_before + 1)
        .expect("Failed to mine tenure extend tx");

    info!("------------------------- Miner 1 Mines Another Block -------------------------");

    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    miners.shutdown();
}

#[test]
#[ignore]
/// Test that a miner will extend its tenure after the succeding miner commits to the wrong block.
/// - Miner 1 wins a tenure and mines normally
/// - Miner 1 wins another tenure and mines normally, but miner 2 does not see any blocks from this tenure
/// - Miner 2 wins a tenure and is unable to mine a block
/// - Miner 1 extends its tenure and mines an additional block
/// - Miner 2 wins the next tenure and mines normally
fn tenure_extend_after_bad_commit() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 2;

    let first_proposal_burn_block_timing = Duration::from_secs(1);
    let block_proposal_timeout = Duration::from_secs(30);
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
            signer_config.first_proposal_burn_block_timing = first_proposal_burn_block_timing;
        },
        |_| {},
        |_| {},
    );
    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();

    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");

    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Wins Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Miner 1 Mines Another Block -------------------------");

    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    info!("------------------------- Pause Block Proposals -------------------------");
    TEST_MINE_STALL.set(true);
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 1 Wins Tenure B -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");
    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("----------------- Miner 2 Submits Block Commit Before Any Blocks ------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("----------------------------- Resume Block Production -----------------------------");

    let stacks_height_before = miners.get_peer_stacks_tip_height();
    TEST_MINE_STALL.set(false);

    wait_for_tenure_change_tx(30, TenureChangeCause::BlockFound, stacks_height_before + 1)
        .expect("Failed to mine tenure change tx");

    info!("--------------- Miner 2 Wins Tenure C With Old Block Commit ----------------");
    // Sleep enough time to pass the first proposal burn block timing
    let sleep_duration = first_proposal_burn_block_timing.saturating_add(Duration::from_secs(2));
    info!(
        "Sleeping for {} seconds before issuing next burn block.",
        sleep_duration.as_secs()
    );
    thread::sleep(sleep_duration);

    info!("--------------- Miner 1 Extends Tenure B over Tenure C ---------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::Extended, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");

    // assure we have a successful sortition that miner 2
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("------------------------- Miner 1 Mines Another Block -------------------------");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    info!("------------------------- Miner 2 Mines the Next Tenure -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");

    // assure we have a successful sortition that miner 2 won and it had a block found tenure change
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    miners.shutdown();
}

#[test]
#[ignore]
/// Test that a miner will extend its tenure after the succeeding miner commits to the wrong block.
/// - Miner 1 wins a tenure and mines normally
/// - Miner 1 wins another tenure and mines normally, but miner 2 does not see any blocks from this tenure
/// - Miner 2 wins a tenure and is unable to mine a block
/// - Miner 1 extends its tenure and mines an additional block
/// - Miner 2 wins another tenure and is still unable to mine a block
/// - Miner 1 extends its tenure again and mines an additional block
/// - Miner 2 wins the next tenure and mines normally
fn tenure_extend_after_2_bad_commits() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 2;

    let block_proposal_timeout = Duration::from_secs(30);

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
        },
        |_| {},
        |_| {},
    );
    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Wins Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by tenure change tx");

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Miner 1 Mines Another Block -------------------------");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");
    let stacks_height_before = miners.get_peer_stacks_tip_height();

    info!("------------------------- Pause Block Proposals -------------------------");
    TEST_MINE_STALL.set(true);
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 1 Wins Tenure B -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("----------------- Miner 2 Submits Block Commit Before Any Blocks ------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("----------------------------- Resume Block Production -----------------------------");

    TEST_MINE_STALL.set(false);
    wait_for_tenure_change_tx(30, TenureChangeCause::BlockFound, stacks_height_before + 1)
        .expect("Failed to mine tenure change tx");

    info!("--------------- Miner 2 Wins Tenure C With Old Block Commit ----------------");
    // Pause block production again so that we can make sure miner 2 commits
    // to the wrong block again.
    TEST_MINE_STALL.set(true);

    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("---------- Miner 2 Submits Block Commit Before Any Blocks (again) ----------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Miner 1 Extends Tenure B -------------------------");

    TEST_MINE_STALL.set(false);

    // wait for a tenure extend block from miner 1 to be processed
    // (miner 2's proposals will be rejected)
    wait_for_tenure_change_tx(60, TenureChangeCause::Extended, stacks_height_before + 2)
        .expect("Failed to mine tenure extend tx");

    info!("------------------------- Miner 1 Mines Another Block -------------------------");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    info!("------------ Miner 2 Wins Tenure C With Old Block Commit (again) -----------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);
    miners.submit_commit_miner_2(&sortdb);

    info!("---------------------- Miner 1 Extends Tenure B (again) ---------------------");

    TEST_MINE_STALL.set(false);

    // wait for a tenure extend block from miner 1 to be processed
    // (miner 2's proposals will be rejected)
    wait_for_tenure_change_tx(30, TenureChangeCause::Extended, stacks_height_before + 1)
        .expect("Failed to mine tenure extend tx");

    info!("------------------------- Miner 1 Mines Another Block -------------------------");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine tx");

    info!("----------------------- Miner 2 Mines the Next Tenure -----------------------");
    miners.submit_commit_miner_2(&sortdb);

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");

    // assure we have a successful sortition that miner 2 won and it had a block found tenure change
    verify_sortition_winner(&sortdb, &miner_pkh_2);
    miners.shutdown();
}

#[test]
#[ignore]
/// Test the block_proposal_max_age_secs signer configuration option. It should reject blocks that are
/// invalid but within the max age window, otherwise it should simply drop the block without further processing.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
///
/// Test Execution:
/// The stacks node is advanced to epoch 3.0 reward set calculation to ensure the signer set is determined.
/// An invalid block proposal with a recent timestamp is forcibly written to the miner's slot to simulate the miner proposing a block.
/// The signers process the invalid block and broadcast a block response rejection to the respective .signers-XXX-YYY contract.
/// A second block proposal with an outdated timestamp is then submitted to the miner's slot to simulate the miner proposing a very old block.
/// The test confirms no further block rejection response is submitted to the .signers-XXX-YYY contract.
///
/// Test Assertion:
/// - Each signer successfully rejects the recent invalid block proposal.
/// - No signer submits a block proposal response for the outdated block proposal.
/// - The stacks tip does not advance
fn block_proposal_max_age_rejections() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |config| {
            config.block_proposal_max_age_secs = 30;
        },
        |_| {},
        None,
        None,
    );
    signer_test.boot_to_epoch_3();
    let short_timeout = Duration::from_secs(30);

    info!("------------------------- Send Block Proposal To Signers -------------------------");
    let info_before = get_chain_info(&signer_test.running_nodes.conf);
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    // First propose a stale block that is older than the block_proposal_max_age_secs
    block.header.timestamp = get_epoch_time_secs().saturating_sub(
        signer_test.signer_configs[0]
            .block_proposal_max_age_secs
            .saturating_add(1),
    );
    let block_signer_signature_hash_1 = block.header.signer_signature_hash();
    signer_test.propose_block(block.clone(), short_timeout);

    // Next propose a recent invalid block
    block.header.timestamp = get_epoch_time_secs();
    let block_signer_signature_hash_2 = block.header.signer_signature_hash();
    signer_test.propose_block(block, short_timeout);

    info!("------------------------- Test Block Proposal Rejected -------------------------");
    // Verify the signers rejected only the SECOND block proposal. The first was not even processed.
    wait_for(30, || {
        let rejections = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .map(|chunk| {
                let Ok(message) = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                else {
                    return None;
                };
                match message {
                    SignerMessage::BlockResponse(BlockResponse::Rejected(BlockRejection {
                        signer_signature_hash,
                        signature,
                        ..
                    })) => {
                        assert_eq!(
                            signer_signature_hash, block_signer_signature_hash_2,
                            "We should only reject the second block"
                        );
                        Some(signature)
                    }
                    SignerMessage::BlockResponse(BlockResponse::Accepted(BlockAccepted {
                        signer_signature_hash,
                        ..
                    })) => {
                        assert_ne!(
                            signer_signature_hash, block_signer_signature_hash_1,
                            "We should never have accepted block"
                        );
                        None
                    }
                    _ => None,
                }
            });
        Ok(rejections.count() > num_signers * 7 / 10)
    })
    .expect("Timed out waiting for block rejections");

    info!("------------------------- Test Peer Info-------------------------");
    assert_eq!(info_before, get_chain_info(&signer_test.running_nodes.conf));

    info!("------------------------- Test Shutdown-------------------------");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers do not mark a block as globally accepted if it was not announced by the node.
/// This will simulate this case via testing flags, and ensure that a block can be reorged across tenure
/// boundaries now (as it is only marked locally accepted and no longer gets marked globally accepted
/// by simply seeing the threshold number of signatures).
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// 1. The node mines 1 stacks block N (all signers sign it).
/// 2. <30% of signers are configured to auto reject any block proposals, broadcast of new blocks are skipped, and miners are configured to ignore signers responses.
/// 3. The node mines 1 stacks block N+1 (all signers sign it, but one which rejects it) but eventually all mark the block as locally accepted.
/// 4. A new tenure starts and the miner attempts to mine a new sister block N+1' (as it does not see the threshold number of signatures or any block push from signers).
/// 5. The signers accept this sister block as a valid reorg and the node advances to block N+1'.
///
/// Test Assertion:
/// - All signers accepted block N.
/// - Less than 30% of the signers rejected block N+1.
/// - All signers accept block N+1' as a valid reorg.
/// - The node advances to block N+1'
fn global_acceptance_depends_on_block_announcement() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let nmb_txs = 4;

    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, (send_amt + send_fee) * nmb_txs)],
        |config| {
            // Just accept all reorg attempts
            config.tenure_last_block_proposal_timeout = Duration::from_secs(0);
        },
        |config| {
            config.miner.block_commit_delay = Duration::from_secs(0);
        },
        None,
        None,
    );

    let all_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();
    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let short_timeout = 30;
    signer_test.boot_to_epoch_3();

    info!("------------------------- Test Mine Nakamoto Block N -------------------------");
    let info_before = signer_test.get_peer_info();

    test_observer::clear();
    // submit a tx so that the miner will mine a stacks block N
    let mut sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;
    info!("Submitted tx {tx} in to mine block N");

    wait_for(short_timeout, || {
        Ok(signer_test.get_peer_info().stacks_tip_height > info_before.stacks_tip_height)
    })
    .expect("Timed out waiting for N to be mined and processed");

    // Ensure that the block was accepted globally so the stacks tip has advanced to N
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N to be mined");

    let info_after = signer_test.get_peer_info();
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1
    );

    info!("------------------------- Mine Nakamoto Block N+1 -------------------------");
    // Make less than 30% of the signers reject the block and ensure it is accepted by the node, but not announced.
    let rejecting_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(num_signers * 3 / 10)
        .collect();
    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(rejecting_signers);
    TEST_SKIP_BLOCK_ANNOUNCEMENT.set(true);
    TEST_IGNORE_SIGNERS.set(true);
    TEST_SKIP_BLOCK_BROADCAST.set(true);
    test_observer::clear();

    // submit a tx so that the miner will mine a stacks block N+1
    let info_before = signer_test.get_peer_info();
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);
    info!("Submitted tx {tx} in to mine block N+1");

    let block_n_1 = wait_for_block_proposal(30, info_before.stacks_tip_height + 1, &miner_pk)
        .expect("Timed out waiting for block N+1 to be proposed");

    // Even though one of the signers rejected the block, it will eventually accept the block as it sees the 70% threshold of signatures
    wait_for_block_global_acceptance_from_signers(
        30,
        &block_n_1.header.signer_signature_hash(),
        &all_signers,
    )
    .expect("Timed out waiting for block acceptance of N+1 by a majority of signers");

    info!(
        "------------------------- Attempt to Mine Nakamoto Block N+1' -------------------------"
    );

    TEST_REJECT_ALL_BLOCK_PROPOSAL.set(Vec::new());
    TEST_SKIP_BLOCK_ANNOUNCEMENT.set(false);
    TEST_IGNORE_SIGNERS.set(false);
    TEST_SKIP_BLOCK_BROADCAST.set(false);
    test_observer::clear();
    let info_before = signer_test.get_peer_info();
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let info = signer_test
                .stacks_client
                .get_peer_info()
                .expect("Failed to get peer info");
            Ok(info.stacks_tip_height > info_before.stacks_tip_height
                && info_before.stacks_tip_consensus_hash != info.stacks_tip_consensus_hash)
        },
    )
    .expect("Stacks miner failed to produce new blocks during the newest burn block's tenure");

    let sister_block =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk)
            .expect("Timed out waiting for block N+1' to be mined");
    assert_ne!(
        sister_block.header.signer_signature_hash(),
        block_n_1.header.signer_signature_hash()
    );
    assert_eq!(
        sister_block.header.chain_length,
        block_n_1.header.chain_length
    );

    // Assert the block was mined and the tip has changed.
    let info_after = signer_test.get_peer_info();
    assert_eq!(
        info_after.stacks_tip_height,
        sister_block.header.chain_length
    );
    assert_eq!(info_after.stacks_tip, sister_block.header.block_hash());
    assert_eq!(
        info_after.stacks_tip_consensus_hash,
        sister_block.header.consensus_hash
    );
    assert_eq!(
        sister_block.header.chain_length,
        block_n_1.header.chain_length
    );
    assert_ne!(sister_block, block_n_1);
}

/// Test a scenario where:
/// Two miners boot to Nakamoto.
/// Sortition occurs. Miner 1 wins.
/// Miner 1 proposes a block N
/// Signers accept and the stacks tip advances to N
/// Sortition occurs. Miner 2 wins.
/// Miner 2 proposes block N+1
/// Sortition occurs. Miner 1 wins.
/// Miner 1 proposes block N+1'
/// N+1 passes signers initial checks and is submitted to the node for validation.
/// N+1' arrives at the signers and passes inital checks, but BEFORE N+1' can be submitted for validation:
/// N+1 finishes being processed at the node and sits in the signers queue.
/// Signers THEN submit N+1' for node validation.
/// Signers process N+1 validation response ok, followed immediately by the N+1' validation response ok.
/// Signers broadcast N+1 acceptance
/// Signers broadcast N+1' rejection
/// Miner 2 proposes a new N+2 block built upon N+1
/// Asserts:
/// - N+1 is signed and broadcasted
/// - N+1' is rejected as a sortition view mismatch
/// - The tip advances to N+1 (Signed by Miner 1)
/// - The tip advances to N+2 (Signed by Miner 2)
#[test]
#[ignore]
fn no_reorg_due_to_successive_block_validation_ok() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 1;

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            // Lets make sure we never time out since we need to stall some things to force our scenario
            signer_config.block_proposal_validation_timeout = Duration::from_secs(u64::MAX);
            signer_config.tenure_last_block_proposal_timeout = Duration::from_secs(u64::MAX);
            signer_config.first_proposal_burn_block_timing = Duration::from_secs(u64::MAX);
        },
        |_| {},
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let blocks_mined1 = miners
        .signer_test
        .running_nodes
        .counters
        .naka_mined_blocks
        .clone();

    let Counters {
        naka_skip_commit_op: rl2_skip_commit_op,
        naka_mined_blocks: blocks_mined2,
        naka_rejected_blocks: rl2_rejections,
        ..
    } = miners.rl2_counters.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;

    info!("------------------------- Pause Miner 1's Block Commits -------------------------");
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Nakamoto Block N (Globally Accepted) -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine Block N");
    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);
    let block_n = wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_1)
        .expect("Failed to find block N");
    let block_n_signature_hash = block_n.header.signer_signature_hash();

    assert_eq!(miners.get_peer_stacks_tip(), block_n.header.block_hash());
    debug!("Miner 1 mined block N: {block_n_signature_hash}");

    info!("------------------------- Pause Block Validation Response of N+1 -------------------------");
    TEST_VALIDATE_STALL.set(true);
    let rejections_before_2 = rl2_rejections.load(Ordering::SeqCst);
    let blocks_before = test_observer::get_blocks().len();
    let blocks_processed_before_1 = blocks_mined1.load(Ordering::SeqCst);
    let blocks_processed_before_2 = blocks_mined2.load(Ordering::SeqCst);

    let stacks_height_before = miners.get_peer_stacks_tip_height();
    // Force miner 1 to submit a block
    // submit a tx so that the miner will mine an extra block
    miners.send_transfer_tx();

    let block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_1)
        .expect("Failed to find block N+1");
    let block_n_1_signature_hash = block_n_1.header.signer_signature_hash();

    assert_ne!(miners.get_peer_stacks_tip(), block_n_1.header.block_hash());
    assert_eq!(block_n_1.header.parent_block_id, block_n.header.block_id());
    debug!("Miner 1 proposed block N+1: {block_n_1_signature_hash}");

    info!("------------------------- Unpause Miner 2's Block Commits -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Pause Block Validation Submission of N+1'-------------------------");
    TEST_STALL_BLOCK_VALIDATION_SUBMISSION.set(true);

    info!("------------------------- Start Miner 2's Tenure-------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to Start Miner 2's Tenure");
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    let block_n_1_prime = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Failed to find block N+1'");

    let block_n_1_prime_signature_hash = block_n_1_prime.header.signer_signature_hash();

    debug!("Miner 2 proposed N+1': {block_n_1_prime_signature_hash}");

    // Make sure that the tip is still at block N
    assert_eq!(miners.get_peer_stacks_tip(), block_n.header.block_hash());

    // Just a precaution to make sure no stacks blocks has been processed between now and our original pause
    assert_eq!(rejections_before_2, rl2_rejections.load(Ordering::SeqCst));
    assert_eq!(
        blocks_processed_before_1,
        blocks_mined1.load(Ordering::SeqCst)
    );
    assert_eq!(
        blocks_processed_before_2,
        blocks_mined2.load(Ordering::SeqCst)
    );
    assert_eq!(blocks_before, test_observer::get_blocks().len());

    info!("------------------------- Unpause Block Validation Response of N+1 -------------------------");

    TEST_VALIDATE_STALL.set(false);

    // Verify that the node accepted the proposed N+1, sending back a validate ok response
    wait_for(30, || {
        for proposal in test_observer::get_proposal_responses() {
            if let BlockValidateResponse::Ok(response) = proposal {
                if response.signer_signature_hash == block_n_1_signature_hash {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    })
    .expect("Timed out waiting for validation response for N+1");

    debug!(
        "Node finished processing proposal validation request for N+1: {block_n_1_signature_hash}"
    );

    // This is awful but I can't gurantee signers have reached the submission stall and we need to ensure the event order is as expected.
    sleep_ms(5_000);

    info!("------------------------- Unpause Block Validation Submission and Response for N+1' -------------------------");
    TEST_STALL_BLOCK_VALIDATION_SUBMISSION.set(false);

    info!("------------------------- Confirm N+1' is Rejected ------------------------");
    wait_for_block_global_rejection(30, block_n_1_prime_signature_hash, num_signers)
        .expect("Failed to find block N+1'");

    info!("------------------------- Confirm N+1 Accepted -------------------------");
    let mined_block_n_1 = test_observer::get_mined_nakamoto_blocks()
        .into_iter()
        .find(|block| block.signer_signature_hash == block_n_1_signature_hash)
        .expect("Failed to find block N+1");

    // Miner 2 will see block N+1 as a valid block and reattempt to mine N+2 on top.
    info!("------------------------- Confirm N+2 Accepted ------------------------");
    let block_n_2 =
        wait_for_block_pushed_by_miner_key(30, block_n_1.header.chain_length + 1, &miner_pk_2)
            .expect("Failed to find block N+2");
    assert_eq!(miners.get_peer_stacks_tip(), block_n_2.header.block_hash());
    info!("------------------------- Confirm Stacks Chain is As Expected ------------------------");
    let info_after = get_chain_info(&conf_1);
    assert_eq!(info_after.stacks_tip_height, block_n_2.header.chain_length);
    assert_eq!(info_after.stacks_tip_height, starting_peer_height + 3);
    assert_eq!(info_after.stacks_tip, block_n_2.header.block_hash());
    assert_ne!(
        info_after.stacks_tip_consensus_hash,
        block_n_1.header.consensus_hash
    );
    assert_eq!(
        info_after.stacks_tip_consensus_hash,
        block_n_2.header.consensus_hash
    );
    assert_eq!(
        block_n_2.header.parent_block_id.to_string(),
        mined_block_n_1.block_id
    );
    assert_eq!(block_n_1.header.parent_block_id, block_n.header.block_id());

    miners.shutdown();
}

#[test]
#[ignore]
/// Test that signers for an incoming reward cycle, do not sign blocks for the previous reward cycle.
///
/// Test Setup:
/// The test spins up five stacks signers that are stacked for multiple cycles, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines to the middle of the prepare phase of reward cycle N+1.
/// Sends a status request to the signers to ensure both the current and next reward cycle signers are active.
/// A valid Nakamoto block is proposed.
/// Two invalid Nakamoto blocks are proposed.
///
/// Test Assertion:
/// All signers for cycle N sign the valid block.
/// No signers for cycle N+1 emit any messages.
/// All signers for cycle N reject the invalid blocks.
/// No signers for cycle N+1 emit any messages for the invalid blocks.
/// The chain advances to block N.
fn incoming_signers_ignore_block_proposals() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_amt + send_fee)]);
    let timeout = Duration::from_secs(200);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();
    let curr_reward_cycle = signer_test.get_current_reward_cycle();
    // Mine to the middle of the prepare phase of the next reward cycle
    let next_reward_cycle = curr_reward_cycle.saturating_add(1);
    let prepare_phase_len = signer_test
        .running_nodes
        .conf
        .get_burnchain()
        .pox_constants
        .prepare_length as u64;
    let middle_of_prepare_phase = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(next_reward_cycle)
        .saturating_sub(prepare_phase_len / 2);

    info!("------------------------- Test Mine Until Middle of Prepare Phase at Block Height {middle_of_prepare_phase} -------------------------");
    signer_test.run_until_burnchain_height_nakamoto(timeout, middle_of_prepare_phase, num_signers);

    signer_test.wait_for_registered_both_reward_cycles(30);

    let current_burnchain_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height();
    assert_eq!(current_burnchain_height, middle_of_prepare_phase);
    assert_eq!(curr_reward_cycle, signer_test.get_current_reward_cycle());

    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);

    info!("------------------------- Test Mine A Valid Block -------------------------");
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    // a tenure has begun, so wait until we mine a block
    wait_for(30, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .expect("Timed out waiting for a block to be mined");

    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let mut stackerdb = StackerDB::new_normal(
        &signer_test.running_nodes.conf.node.rpc_bind,
        StacksPrivateKey::random(), // We are just reading so don't care what the key is
        false,
        next_reward_cycle,
        SignerSlotID(0), // We are just reading so again, don't care about index.
    );

    let next_signer_slot_ids: Vec<_> = signer_test
        .get_signer_indices(next_reward_cycle)
        .iter()
        .map(|id| id.0)
        .collect();

    let mut no_next_signer_messages = || {
        assert!(wait_for(30, || {
            let latest_msgs = StackerDB::get_messages::<SignerMessage>(
                stackerdb
                    .get_session_mut(&MessageSlotID::BlockResponse)
                    .expect("Failed to get BlockResponse stackerdb session"),
                &next_signer_slot_ids,
            )
            .expect("Failed to get messages from stackerdb");
            assert!(
                latest_msgs.is_empty(),
                "Next signers have messages in their stackerdb"
            );
            Ok(false)
        })
        .is_err());
    };

    no_next_signer_messages();

    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        block_proposal_timeout: Duration::from_secs(100),
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    block.header.timestamp = get_epoch_time_secs();
    let signer_signature_hash_1 = block.header.signer_signature_hash();

    info!("------------------------- Test Attempt to Mine Invalid Block {signer_signature_hash_1} -------------------------");

    let short_timeout = Duration::from_secs(30);
    let all_signers: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();
    test_observer::clear();

    // Propose a block to the signers that passes initial checks but will be rejected by the stacks node
    let view = SortitionsView::fetch_view(proposal_conf, &signer_test.stacks_client).unwrap();
    block.header.pox_treatment = BitVec::ones(1).unwrap();
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.header.chain_length =
        get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height + 1;
    let signer_signature_hash_2 = block.header.signer_signature_hash();

    info!("------------------------- Test Attempt to Mine Invalid Block {signer_signature_hash_2} -------------------------");

    signer_test.propose_block(block, short_timeout);
    // Verify the signers rejected the second block via the endpoint
    signer_test.wait_for_validate_reject_response(short_timeout, signer_signature_hash_2);
    wait_for_block_rejections_from_signers(30, &all_signers)
        .expect("Timed out waiting for block rejections");
    no_next_signer_messages();

    assert_eq!(blocks_before, mined_blocks.load(Ordering::SeqCst));
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers for an outgoing reward cycle, do not sign blocks for the incoming reward cycle.
///
/// Test Setup:
/// The test spins up five stacks signers that are stacked for multiple cycles, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The node mines to the next reward cycle.
/// Sends a status request to the signers to ensure both the current and previous reward cycle signers are active.
/// A valid Nakamoto block is proposed.
/// Two invalid Nakamoto blocks are proposed.
///
/// Test Assertion:
/// All signers for cycle N+1 sign the valid block.
/// No signers for cycle N emit any messages.
/// All signers for cycle N+1 reject the invalid blocks.
/// No signers for cycle N emit any messages for the invalid blocks.
/// The chain advances to block N.
fn outgoing_signers_ignore_block_proposals() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_amt + send_fee)]);
    let timeout = Duration::from_secs(200);
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    signer_test.boot_to_epoch_3();
    // Do not cleanup stale signers
    TEST_SKIP_SIGNER_CLEANUP.set(true);
    let curr_reward_cycle = signer_test.get_current_reward_cycle();
    // Mine to the middle of the prepare phase of the next reward cycle
    let next_reward_cycle = curr_reward_cycle.saturating_add(1);
    let next_reward_cycle_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(next_reward_cycle);

    info!("------------------------- Test Mine Until Next Reward Cycle at Height {next_reward_cycle_height} -------------------------");
    signer_test.run_until_burnchain_height_nakamoto(timeout, next_reward_cycle_height, num_signers);

    signer_test.wait_for_registered_both_reward_cycles(30);

    let current_burnchain_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height();
    assert_eq!(current_burnchain_height, next_reward_cycle_height);
    assert_eq!(next_reward_cycle, signer_test.get_current_reward_cycle());

    let old_reward_cycle = curr_reward_cycle;

    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);

    test_observer::clear();

    info!("------------------------- Test Mine A Valid Block -------------------------");
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    // a tenure has begun, so wait until we mine a block
    wait_for(30, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .expect("Timed out waiting for a block to be mined");

    let new_signature_hash = test_observer::get_mined_nakamoto_blocks()
        .last()
        .unwrap()
        .signer_signature_hash;
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let mut stackerdb = StackerDB::new_normal(
        &signer_test.running_nodes.conf.node.rpc_bind,
        StacksPrivateKey::random(), // We are just reading so don't care what the key is
        false,
        old_reward_cycle,
        SignerSlotID(0), // We are just reading so again, don't care about index.
    );

    let old_signer_slot_ids: Vec<_> = signer_test
        .get_signer_indices(old_reward_cycle)
        .iter()
        .map(|id| id.0)
        .collect();

    let mut old_signers_ignore_block_proposals = |hash| {
        assert!(wait_for(10, || {
            let latest_msgs = StackerDB::get_messages::<SignerMessage>(
                stackerdb
                    .get_session_mut(&MessageSlotID::BlockResponse)
                    .expect("Failed to get BlockResponse stackerdb session"),
                &old_signer_slot_ids,
            )
            .expect("Failed to get messages from stackerdb");
            for msg in latest_msgs.iter() {
                if let SignerMessage::BlockResponse(response) = msg {
                    assert_ne!(response.get_signer_signature_hash(), hash);
                }
            }
            Ok(false)
        })
        .is_err());
    };
    old_signers_ignore_block_proposals(new_signature_hash);

    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        block_proposal_timeout: Duration::from_secs(100),
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut block = NakamotoBlock {
        header: NakamotoBlockHeader::empty(),
        txs: vec![],
    };
    block.header.timestamp = get_epoch_time_secs();

    let short_timeout = Duration::from_secs(30);
    test_observer::clear();

    // Propose a block to the signers that passes initial checks but will be rejected by the stacks node
    let view = SortitionsView::fetch_view(proposal_conf, &signer_test.stacks_client).unwrap();
    block.header.pox_treatment = BitVec::ones(1).unwrap();
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.header.chain_length =
        get_chain_info(&signer_test.running_nodes.conf).stacks_tip_height + 1;
    let signer_signature_hash = block.header.signer_signature_hash();

    info!("------------------------- Test Attempt to Mine Invalid Block {signer_signature_hash} -------------------------");

    signer_test.propose_block(block, short_timeout);
    // Verify the signers rejected the second block via the endpoint
    signer_test.wait_for_validate_reject_response(short_timeout, signer_signature_hash);
    wait_for_block_global_rejection(30, signer_signature_hash, num_signers)
        .expect("Failed to see majority rejections of ivalid block'");
    old_signers_ignore_block_proposals(signer_signature_hash);

    assert_eq!(blocks_before, mined_blocks.load(Ordering::SeqCst));
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers ignore signatures for blocks that do not belong to their own reward cycle.
/// This is a regression test for a signer bug that caused an internal signer instances to
/// broadcast a block corresponding to a different reward cycle with a higher threshold, stalling the network.
///
/// Test Setup:
/// The test spins up four stacks signers that are stacked for one cycle, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// The same four stackers stack for an addiitonal cycle.
/// A new fifth signer is added to the stacker set, stacking for the next reward cycle.
/// The node advances to the next reward cycle.
/// The first two signers are set to ignore block proposals.
/// A valid Nakamoto block N is proposed to the current signers.
/// A signer signature over block N is forcibly written to the outgoing signer's stackerdb instance.
///
/// Test Assertion:
/// All signers for the previous cycle ignore the incoming block N.
/// Outgoing signers ignore the forced signature.
/// The chain does NOT advance to block N.
fn injected_signatures_are_ignored_across_boundaries() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 4;
    let new_num_signers = 5_usize;
    let signer_private_keys: Vec<_> = (0..num_signers)
        .map(|_| StacksPrivateKey::random())
        .collect();
    let new_signer_private_key = StacksPrivateKey::random();
    let mut new_signer_private_keys = signer_private_keys.clone();
    new_signer_private_keys.push(new_signer_private_key);

    let new_signer_public_keys: Vec<_> = new_signer_private_keys
        .iter()
        .map(|sk| Secp256k1PublicKey::from_private(sk).to_bytes_compressed())
        .collect();
    let new_signer_addresses: Vec<_> = new_signer_private_keys.iter().map(tests::to_addr).collect();
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    let mut initial_balances = new_signer_addresses
        .iter()
        .map(|addr| (*addr, POX_4_DEFAULT_STACKER_BALANCE))
        .collect::<Vec<_>>();

    initial_balances.push((sender_addr, (send_amt + send_fee) * 4));

    let run_stamp = rand::random();

    let rpc_port = 51024;
    let rpc_bind = format!("127.0.0.1:{rpc_port}");

    // Setup the new signers that will take over
    let new_signer_config = build_signer_config_tomls(
        &[new_signer_private_key],
        &rpc_bind,
        Some(Duration::from_millis(128)), // Timeout defaults to 5 seconds. Let's override it to 128 milliseconds.
        &Network::Testnet,
        "12345",
        run_stamp,
        3000 + num_signers,
        Some(100_000),
        None,
        Some(9000 + num_signers),
        None,
    )
    .first()
    .unwrap()
    .clone();

    info!("---- spawning signer ----");
    let signer_config = SignerConfig::load_from_str(&new_signer_config).unwrap();
    let new_spawned_signer = SpawnedSigner::new(signer_config.clone());

    // Boot with some initial signer set
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        initial_balances,
        |_| {},
        |naka_conf| {
            info!(
                "---- Adding signer endpoint to naka conf ({}) ----",
                signer_config.endpoint
            );

            naka_conf.events_observers.insert(EventObserverConfig {
                endpoint: format!("{}", signer_config.endpoint),
                events_keys: vec![
                    EventKeyType::StackerDBChunks,
                    EventKeyType::BlockProposal,
                    EventKeyType::BurnchainBlocks,
                ],
                timeout_ms: 1000,
            });
            naka_conf.node.rpc_bind = rpc_bind.clone();
        },
        None,
        Some(signer_private_keys),
    );
    assert_eq!(
        new_spawned_signer.config.node_host,
        signer_test.running_nodes.conf.node.rpc_bind
    );

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let short_timeout = Duration::from_secs(20);

    // Verify that naka_conf has our new signer's event observers
    let endpoint = format!("{}", signer_config.endpoint);
    assert!(signer_test
        .running_nodes
        .conf
        .events_observers
        .iter()
        .any(|observer| observer.endpoint == endpoint));

    info!("---- Booting to epoch 3 -----");
    signer_test.boot_to_epoch_3();
    // Do not cleanup stale signers
    TEST_SKIP_SIGNER_CLEANUP.set(true);

    // verify that the first reward cycle has the old signers in the reward set
    let reward_cycle = signer_test.get_current_reward_cycle();
    let signer_test_public_keys: Vec<_> = signer_test
        .signer_stacks_private_keys
        .iter()
        .map(|sk| Secp256k1PublicKey::from_private(sk).to_bytes_compressed())
        .collect();

    info!("---- Verifying that the current signers are the old signers ----");
    let current_signers = signer_test.get_reward_set_signers(reward_cycle);
    assert_eq!(current_signers.len(), num_signers);
    // Verify that the current signers are the same as the old signers
    for signer in current_signers.iter() {
        assert!(signer_test_public_keys.contains(&signer.signing_key.to_vec()));
    }

    // advance to the next reward cycle, stacking to the new signers beforehand
    let reward_cycle = signer_test.get_current_reward_cycle();

    info!("---- Stacking new signers -----");

    let burn_block_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_headers_height();
    let accounts_to_check: Vec<_> = new_signer_private_keys.iter().map(tests::to_addr).collect();

    // Stack the new signer
    let pox_addr = PoxAddress::from_legacy(
        AddressHashMode::SerializeP2PKH,
        tests::to_addr(&new_signer_private_key).bytes().clone(),
    );
    let pox_addr_tuple: clarity::vm::Value = pox_addr.as_clarity_tuple().unwrap().into();
    let signature = make_pox_4_signer_key_signature(
        &pox_addr,
        &new_signer_private_key,
        reward_cycle.into(),
        &Pox4SignatureTopic::StackStx,
        CHAIN_ID_TESTNET,
        1_u128,
        u128::MAX,
        1,
    )
    .unwrap()
    .to_rsv();

    let signer_pk = Secp256k1PublicKey::from_private(&new_signer_private_key);
    let stacking_tx = tests::make_contract_call(
        &new_signer_private_key,
        0,
        1000,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &StacksAddress::burn_address(false),
        "pox-4",
        "stack-stx",
        &[
            clarity::vm::Value::UInt(POX_4_DEFAULT_STACKER_STX_AMT),
            pox_addr_tuple,
            clarity::vm::Value::UInt(burn_block_height as u128),
            clarity::vm::Value::UInt(1),
            clarity::vm::Value::some(clarity::vm::Value::buff_from(signature).unwrap()).unwrap(),
            clarity::vm::Value::buff_from(signer_pk.to_bytes_compressed()).unwrap(),
            clarity::vm::Value::UInt(u128::MAX),
            clarity::vm::Value::UInt(1),
        ],
    );
    submit_tx(&http_origin, &stacking_tx);

    wait_for(60, || {
        Ok(accounts_to_check
            .iter()
            .all(|acct| get_account(&http_origin, acct).nonce >= 1))
    })
    .expect("Timed out waiting for stacking txs to be mined");

    signer_test.mine_nakamoto_block(short_timeout, true);

    let next_reward_cycle = reward_cycle.saturating_add(1);

    let next_cycle_height = signer_test
        .running_nodes
        .btc_regtest_controller
        .get_burnchain()
        .nakamoto_first_block_of_cycle(next_reward_cycle)
        .saturating_add(1);

    let next_calculation = next_cycle_height.saturating_sub(3);
    info!("---- Mining to next reward set calculation (block {next_calculation}) -----");
    signer_test.run_until_burnchain_height_nakamoto(
        Duration::from_secs(60),
        next_calculation,
        new_num_signers,
    );

    // Verify that the new reward set is the new signers
    let reward_set = signer_test.get_reward_set_signers(next_reward_cycle);
    assert_eq!(reward_set.len(), new_num_signers);
    for signer in reward_set.iter() {
        assert!(new_signer_public_keys.contains(&signer.signing_key.to_vec()));
    }

    info!("---- Manually mine a single burn block to force the signers to update ----");
    next_block_and_wait(
        &mut signer_test.running_nodes.btc_regtest_controller,
        &signer_test.running_nodes.counters.blocks_processed,
    );

    signer_test.wait_for_registered_both_reward_cycles(60);

    info!("---- Mining to the next reward cycle (block {next_cycle_height}) -----",);
    signer_test.run_until_burnchain_height_nakamoto(
        Duration::from_secs(60),
        next_cycle_height,
        new_num_signers,
    );
    let new_reward_cycle = signer_test.get_current_reward_cycle();
    assert_eq!(new_reward_cycle, reward_cycle.saturating_add(1));

    let current_signers = signer_test.get_reward_set_signers(new_reward_cycle);
    assert_eq!(current_signers.len(), new_num_signers);

    let mined_blocks = signer_test.running_nodes.counters.naka_mined_blocks.clone();
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    // Clear the stackerdb chunks
    test_observer::clear();

    let old_reward_cycle = reward_cycle;
    let curr_reward_cycle = new_reward_cycle;

    info!("------------------------- Test Propose A Valid Block -------------------------");
    // Make the last three of the signers ignore the block proposal to ensure it it is not globally accepted/rejected
    let all_signers: Vec<_> = new_signer_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();
    let non_ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .take(new_num_signers * 5 / 10)
        .collect();
    let ignoring_signers: Vec<_> = all_signers
        .iter()
        .cloned()
        .skip(new_num_signers * 5 / 10)
        .collect();
    assert_eq!(ignoring_signers.len(), 3);
    assert_eq!(non_ignoring_signers.len(), 2);
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(ignoring_signers.clone());

    let info_before = signer_test.get_peer_info();
    // submit a tx so that the miner will ATTEMPT to mine a stacks block N
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        0,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    let tx = submit_tx(&http_origin, &transfer_tx);

    info!("Submitted tx {tx} in attempt to mine block N");
    let mut new_signature_hash = None;
    wait_for(30, || {
        let accepted_signers = test_observer::get_stackerdb_chunks()
            .into_iter()
            .flat_map(|chunk| chunk.modified_slots)
            .filter_map(|chunk| {
                let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                    .expect("Failed to deserialize SignerMessage");
                if let SignerMessage::BlockResponse(BlockResponse::Accepted(accepted)) = message {
                    new_signature_hash = Some(accepted.signer_signature_hash);
                    return non_ignoring_signers.iter().find(|key| {
                        key.verify(accepted.signer_signature_hash.bits(), &accepted.signature)
                            .is_ok()
                    });
                }
                None
            });
        Ok(accepted_signers.count() + ignoring_signers.len() == new_num_signers)
    })
    .expect("FAIL: Timed out waiting for block proposal acceptance");
    let new_signature_hash = new_signature_hash.expect("Failed to get new signature hash");

    // The first 50% of the signers are the ones that are ignoring block proposals and thus haven't sent a signature yet
    let forced_signer = &signer_test.signer_stacks_private_keys[ignoring_signers.len()];
    let mut stackerdb = StackerDB::new_normal(
        &signer_test.running_nodes.conf.node.rpc_bind,
        forced_signer.clone(),
        false,
        old_reward_cycle,
        signer_test
            .get_signer_slot_id(old_reward_cycle, &tests::to_addr(forced_signer))
            .expect("Failed to get signer slot id")
            .expect("Signer does not have a slot id"),
    );
    signer_test.verify_no_block_response_found(
        &mut stackerdb,
        next_reward_cycle,
        new_signature_hash,
    );

    // Get the last block proposal
    let block_proposal = test_observer::get_stackerdb_chunks()
        .iter()
        .flat_map(|chunk| chunk.modified_slots.clone())
        .filter_map(|chunk| {
            let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                .expect("Failed to deserialize SignerMessage");
            if let SignerMessage::BlockProposal(proposal) = message {
                assert_eq!(proposal.reward_cycle, curr_reward_cycle);
                assert_eq!(
                    proposal.block.header.signer_signature_hash(),
                    new_signature_hash
                );
                return Some(proposal);
            }
            None
        })
        .next()
        .expect("Failed to find block proposal for reward cycle {curr_reward_cycle}");

    let blocks_after = mined_blocks.load(Ordering::SeqCst);
    let info_after = signer_test.get_peer_info();
    assert_eq!(blocks_after, blocks_before);
    assert_eq!(info_after, info_before);

    // Ensure that the block was NOT accepted globally so the stacks tip has NOT advanced to N
    let nakamoto_blocks = test_observer::get_mined_nakamoto_blocks();
    let block = nakamoto_blocks.last().unwrap();
    assert_ne!(info_after.stacks_tip.to_string(), block.block_hash);

    info!("------------------------- Test Inject Valid Signature To Old Signers -------------------------");
    // Force a signature to force the threshold of the block over the old signers' threshold
    // If the old signers were not fixed, the old signers would stall.
    signer_test.inject_accept_signature(&block_proposal.block, forced_signer, old_reward_cycle);

    assert!(wait_for(10, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .is_err());

    let info_after = signer_test.get_peer_info();
    assert_ne!(info_after.stacks_tip.to_string(), block.block_hash);

    info!("------------------------- Test Inject Valid Signatures to New Signers -------------------------");
    // Force two signatures to force the threshold of the block over the new signers' threshold
    // This signature should be accepted by current signers, but ignored by the old signers.
    signer_test.inject_accept_signature(&block_proposal.block, forced_signer, new_reward_cycle);
    let forced_signer = new_signer_private_keys.last().unwrap();
    signer_test.inject_accept_signature(&block_proposal.block, forced_signer, new_reward_cycle);

    wait_for(30, || {
        Ok(mined_blocks.load(Ordering::SeqCst) > blocks_before)
    })
    .expect("Timed out waiting for block to be mined");

    let info_after = signer_test.get_peer_info();
    assert_eq!(info_after.stacks_tip.to_string(), block.block_hash,);
    // Wait 5 seconds in case there are any lingering block pushes from the signers
    std::thread::sleep(Duration::from_secs(5));
    signer_test.shutdown();

    assert!(new_spawned_signer.stop().is_none());
}

#[test]
#[ignore]
/// Test that signers count a block proposal that was rejected due to a reorg towards miner activity since it showed up BEFORE
/// the reorg_attempts_activity_timeout
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing. The block proposal timeout is set to 20 seconds.
///
/// Test Execution:
/// Test validation endpoint is stalled.
/// The miner proposes a block N.
/// A new tenure is started.
/// The miner proposes a block N'.
/// The test waits for block proposal timeout + 1 second.
/// The validation endpoint is resumed.
/// The signers accept block N.
/// The signers reject block N'.
/// The miner proposes block N+1.
/// The signers accept block N+1.
///
/// Test Assertion:
/// Stacks tip advances to N+1
fn reorg_attempts_count_towards_miner_validity() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let block_proposal_timeout = Duration::from_secs(30);
    let reorg_attempts_activity_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.block_proposal_timeout = block_proposal_timeout;
            config.reorg_attempts_activity_timeout = reorg_attempts_activity_timeout;
        },
        |_| {},
        None,
        None,
    );
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);
    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();

    signer_test.boot_to_epoch_3();

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    info!("------------------------- Test Mine Block N -------------------------");
    let chain_before = get_chain_info(&signer_test.running_nodes.conf);
    // Stall validation so signers will be unable to process the tenure change block for Tenure B.
    TEST_VALIDATE_STALL.set(true);
    test_observer::clear();
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    let block_proposal_n =
        wait_for_block_proposal(30, chain_before.stacks_tip_height + 1, &miner_pk)
            .expect("Failed to get block proposal N");
    let chain_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(chain_after, chain_before);
    test_observer::clear();

    info!("------------------------- Start Tenure B  -------------------------");
    let commits_before = commits_submitted.load(Ordering::SeqCst);

    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || Ok(commits_submitted.load(Ordering::SeqCst) > commits_before),
    )
    .unwrap();

    let block_proposal_n_prime =
        wait_for_block_proposal(30, chain_before.stacks_tip_height + 1, &miner_pk)
            .expect("Failed to get block proposal N'");
    test_observer::clear();
    std::thread::sleep(block_proposal_timeout.add(Duration::from_secs(1)));

    assert_ne!(block_proposal_n, block_proposal_n_prime);
    let chain_before = get_chain_info(&signer_test.running_nodes.conf);
    TEST_VALIDATE_STALL.set(false);

    wait_for(30, || {
        let chain_info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(chain_info.stacks_tip_height > chain_before.stacks_tip_height)
    })
    .expect("Timed out waiting for stacks tip to advance to block N");

    let chain_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(
        chain_after.stacks_tip_height,
        block_proposal_n.header.chain_length
    );

    info!("------------------------- Wait for Block N' Rejection -------------------------");
    wait_for_block_global_rejection(
        30,
        block_proposal_n_prime.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Failed to see majority rejections of block N'");

    info!("------------------------- Test Mine Block N+1 -------------------------");
    // The signer should automatically attempt to mine a new block once the signers eventually tell it to abandon the previous block
    // It will accept it even though block proposal timeout is exceeded because the miner did manage to propose block N' BEFORE the timeout.
    let block_n_1 =
        wait_for_block_pushed_by_miner_key(30, block_proposal_n.header.chain_length + 1, &miner_pk)
            .expect("Failed to get mined block N+1");
    assert_eq!(
        block_n_1.get_tenure_tx_payload().unwrap().cause,
        TenureChangeCause::BlockFound
    );
    let chain_after = get_chain_info(&signer_test.running_nodes.conf);

    assert_eq!(chain_after.stacks_tip, block_n_1.header.block_hash());
    assert_eq!(
        block_n_1.header.chain_length,
        block_proposal_n_prime.header.chain_length + 1
    );
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers do not count a block proposal that was rejected due to a reorg towards miner activity since it showed up AFTER
/// the reorg_attempts_activity_timeout
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing. The block proposal timeout is set to 20 seconds.
///
/// Test Execution:
/// Test validation endpoint is stalled.
/// The miner proposes a block N.
/// Block proposals are stalled.
/// A new tenure is started.
/// The test waits for reorg_attempts_activity_timeout + 1 second.
/// The miner proposes a block N'.
/// The test waits for block proposal timeout + 1 second.
/// The validation endpoint is resumed.
/// The signers accept block N.
/// The signers reject block N'.
/// The miner proposes block N+1.
/// The signers reject block N+1.
///
/// Test Assertion:
/// Stacks tip advances to N.
fn reorg_attempts_activity_timeout_exceeded() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let block_proposal_timeout = Duration::from_secs(30);
    let reorg_attempts_activity_timeout = Duration::from_secs(20);
    let tenure_extend_wait_timeout = Duration::from_secs(1000);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(sender_addr, send_amt + send_fee)],
        |config| {
            config.block_proposal_timeout = block_proposal_timeout;
            config.reorg_attempts_activity_timeout = reorg_attempts_activity_timeout;
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        None,
        None,
    );
    let commits_submitted = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    signer_test.boot_to_epoch_3();

    info!("------------------------- Test Mine Block N -------------------------");
    let chain_before = get_chain_info(&signer_test.running_nodes.conf);
    // Stall validation so signers will be unable to process the tenure change block for Tenure B.
    // And so the incoming miner proposes a block N' (the reorging block).
    TEST_VALIDATE_STALL.set(true);
    test_observer::clear();
    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    let block_proposal_n =
        wait_for_block_proposal(30, chain_before.stacks_tip_height + 1, &miner_pk)
            .expect("Failed to get block proposal N");
    let chain_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(chain_after, chain_before);
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);

    info!("------------------------- Start Tenure B  -------------------------");
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let chain_before = get_chain_info(&signer_test.running_nodes.conf);
    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let chain_info = get_chain_info(&signer_test.running_nodes.conf);
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before
                && chain_info.burn_block_height > chain_before.burn_block_height)
        },
    )
    .unwrap();

    info!("------------------------- Wait for block N' to arrive late  -------------------------");
    test_observer::clear();
    // Allow block N validation to finish.
    TEST_VALIDATE_STALL.set(false);
    wait_for(30, || {
        let chain_info = get_chain_info(&signer_test.running_nodes.conf);
        Ok(chain_info.stacks_tip_height > chain_before.stacks_tip_height)
    })
    .expect("Timed out waiting for stacks tip to advance to block N");
    let chain_after = get_chain_info(&signer_test.running_nodes.conf);
    TEST_VALIDATE_STALL.set(true);
    // Allow incoming mine to propose block N'
    // Make sure to wait the reorg_attempts_activity_timeout AFTER the block is globally signed over
    // as this is the point where signers start considering from.
    std::thread::sleep(reorg_attempts_activity_timeout.add(Duration::from_secs(1)));
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);
    let block_proposal_n_prime =
        wait_for_block_proposal(30, chain_after.stacks_tip_height, &miner_pk)
            .expect("Failed to get block proposal N'");
    // Make sure that no subsequent proposal arrives before the block_proposal_timeout is exceeded
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);
    TEST_VALIDATE_STALL.set(false);
    // We only need to wait the difference between the two timeouts now since we already slept for a min of reorg_attempts_activity_timeout + 1
    std::thread::sleep(block_proposal_timeout.saturating_sub(reorg_attempts_activity_timeout));
    assert_ne!(block_proposal_n, block_proposal_n_prime);
    let chain_before = chain_after;

    info!("------------------------- Wait for Block N' Rejection -------------------------");
    wait_for_block_global_rejection(
        30,
        block_proposal_n_prime.header.signer_signature_hash(),
        num_signers,
    )
    .expect("FAIL: Timed out waiting for block proposal rejections of N'");

    info!("------------------------- Wait for Block N+1 Proposal -------------------------");
    test_observer::clear();
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);
    // The miner will automatically reattempt to mine a block N+1 once it sees the stacks tip advance to block N.
    // N+1 will still be rejected however as the signers will have already marked the miner as invalid since the reorg
    // block N' arrived AFTER the reorg_attempts_activity_timeout and the subsequent block N+1 arrived AFTER the
    // block_proposal_timeout.
    let block_proposal_n_1 =
        wait_for_block_proposal(30, chain_before.stacks_tip_height + 1, &miner_pk)
            .expect("Failed to get block proposal N+1");

    info!("------------------------- Wait for Block N+1 Rejection -------------------------");
    wait_for_block_global_rejection(
        30,
        block_proposal_n_1.header.signer_signature_hash(),
        num_signers,
    )
    .expect("FAIL: Timed out waiting for block proposal rejections of N+1");

    info!("------------------------- Ensure chain halts -------------------------");
    // Just in case, wait again and ensure that the chain is still halted (once marked invalid, the miner can do nothing to satisfy the signers)
    assert!(wait_for(reorg_attempts_activity_timeout.as_secs(), || {
        let chain_info = get_chain_info(&signer_test.running_nodes.conf);
        assert_eq!(chain_info.stacks_tip_height, chain_before.stacks_tip_height);
        Ok(false)
    })
    .is_err());
    signer_test.shutdown();
}

#[test]
#[ignore]
fn fast_sortition() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);

    let mut sender_nonce = 0;
    let send_amt = 100;
    let send_fee = 400;
    let num_transfers = 3;
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(
        num_signers,
        vec![(sender_addr, num_transfers * (send_amt + send_fee))],
    );

    let http_origin = format!("http://{}", &signer_test.running_nodes.conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    info!("------------------------- Mine a Block -------------------------");
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;

    wait_for(60, || {
        Ok(get_account(&http_origin, &sender_addr).nonce == sender_nonce)
    })
    .expect("Timed out waiting for call tx to be mined");

    info!("------------------------- Cause a missed sortition -------------------------");

    signer_test
        .running_nodes
        .btc_regtest_controller
        .build_next_block(1);
    next_block_and_process_new_stacks_block(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        &signer_test.running_nodes.coord_channel,
    )
    .expect("Failed to mine a block");

    info!("------------------------- Mine a Block -------------------------");
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        signer_test.running_nodes.conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);
    sender_nonce += 1;

    wait_for(60, || {
        Ok(get_account(&http_origin, &sender_addr).nonce == sender_nonce)
    })
    .expect("Timed out waiting for call tx to be mined");

    info!("------------------------- Shutdown -------------------------");
    signer_test.shutdown();
}

#[test]
#[ignore]
/// This test spins up two nakamoto nodes, both configured to mine.
/// After Nakamoto blocks are mined, it waits for a normal tenure, then issues
///  two bitcoin blocks in quick succession -- the first will contain block commits,
///  and the second "flash block" will contain no block commits.
/// The test checks if the winner of the first block is different than the previous tenure.
/// If so, it performs the actual test: asserting that the miner wakes up and produces valid blocks.
/// This test uses the burn-block-height to ensure consistent calculation of the burn view between
///   the miner thread and the block processor
fn multiple_miners_empty_sortition() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let num_signers = 5;

    let mut miners = MultipleMinerTest::new(num_signers, 60);

    let (conf_1, conf_2) = miners.get_node_configs();

    let rl1_commits = miners
        .signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let rl1_counters = miners.signer_test.running_nodes.counters.clone();

    let rl2_commits = miners.rl2_counters.naka_submitted_commits.clone();
    let rl2_counters = miners.rl2_counters.clone();

    let sender_addr = tests::to_addr(&miners.sender_sk);

    miners.boot_to_epoch_3();

    let burn_height_contract = "
       (define-data-var local-burn-block-ht uint u0)
       (define-public (run-update)
          (ok (var-set local-burn-block-ht burn-block-height)))
    ";

    let contract_tx = make_contract_publish(
        &miners.sender_sk,
        miners.sender_nonce,
        1000,
        conf_1.burnchain.chain_id,
        "burn-height-local",
        burn_height_contract,
    );
    submit_tx(&conf_1.node.data_url, &contract_tx);
    miners.sender_nonce += 1;

    let last_sender_nonce = loop {
        // Mine 1 nakamoto tenures
        info!("Mining tenure...");

        miners.signer_test.mine_block_wait_on_processing(
            &[&conf_1, &conf_2],
            &[&rl1_counters, &rl2_counters],
            Duration::from_secs(30),
        );

        // mine the interim blocks
        for _ in 0..2 {
            let sender_nonce = get_account(&conf_1.node.data_url, &sender_addr).nonce;
            // check if the burn contract is already produced, if not wait for it to be included in
            //  an interim block
            if sender_nonce >= 1 {
                let contract_call_tx = make_contract_call(
                    &miners.sender_sk,
                    sender_nonce,
                    miners.send_fee,
                    conf_1.burnchain.chain_id,
                    &sender_addr,
                    "burn-height-local",
                    "run-update",
                    &[],
                );
                submit_tx(&conf_1.node.data_url, &contract_call_tx);
            }

            // make sure the sender's tx gets included (whether it was the contract publish or call)
            wait_for(60, || {
                let next_sender_nonce = get_account(&conf_1.node.data_url, &sender_addr).nonce;
                Ok(next_sender_nonce > sender_nonce)
            })
            .unwrap();
        }

        let last_active_sortition = get_sortition_info(&conf_1);
        assert!(last_active_sortition.was_sortition);

        // check if we're about to cross a reward cycle boundary -- if so, we can't
        //  perform this test, because we can't tenure extend across the boundary
        let pox_info = get_pox_info(&conf_1.node.data_url).unwrap();
        let blocks_until_next_cycle = pox_info.next_cycle.blocks_until_reward_phase;
        if blocks_until_next_cycle == 1 {
            info!("We're about to cross a reward cycle boundary, cannot perform a tenure extend here!");
            continue;
        }

        // lets mine a btc flash block
        let rl2_commits_before = rl2_commits.load(Ordering::SeqCst);
        let rl1_commits_before = rl1_commits.load(Ordering::SeqCst);
        let info_before = get_chain_info(&conf_1);

        miners.btc_regtest_controller_mut().build_next_block(2);

        wait_for(60, || {
            let info = get_chain_info(&conf_1);
            Ok(info.burn_block_height >= 2 + info_before.burn_block_height
                && rl2_commits.load(Ordering::SeqCst) > rl2_commits_before
                && rl1_commits.load(Ordering::SeqCst) > rl1_commits_before)
        })
        .unwrap();

        let cur_empty_sortition = get_sortition_info(&conf_1);
        assert!(!cur_empty_sortition.was_sortition);
        let inactive_sortition = get_sortition_info_ch(
            &conf_1,
            cur_empty_sortition.last_sortition_ch.as_ref().unwrap(),
        );
        assert!(inactive_sortition.was_sortition);
        assert_eq!(
            inactive_sortition.burn_block_height,
            last_active_sortition.burn_block_height + 1
        );

        info!("==================== Mined a flash block ====================");
        info!("Flash block sortition info";
              "last_active_winner" => ?last_active_sortition.miner_pk_hash160,
              "last_winner" => ?inactive_sortition.miner_pk_hash160,
              "last_active_ch" => %last_active_sortition.consensus_hash,
              "last_winner_ch" => %inactive_sortition.consensus_hash,
              "cur_empty_sortition" => %cur_empty_sortition.consensus_hash,
        );

        if last_active_sortition.miner_pk_hash160 != inactive_sortition.miner_pk_hash160 {
            info!(
                "==================== Mined a flash block with changed miners ===================="
            );
            break get_account(&conf_1.node.data_url, &sender_addr).nonce;
        }
    };

    // after the flash block, make sure we get block processing without a new bitcoin block
    //   being mined.

    for _ in 0..2 {
        let sender_nonce = get_account(&conf_1.node.data_url, &sender_addr).nonce;
        let contract_call_tx = make_contract_call(
            &miners.sender_sk,
            sender_nonce,
            miners.send_fee,
            conf_1.burnchain.chain_id,
            &sender_addr,
            "burn-height-local",
            "run-update",
            &[],
        );
        submit_tx(&conf_1.node.data_url, &contract_call_tx);

        wait_for(60, || {
            let next_sender_nonce = get_account(&conf_1.node.data_url, &sender_addr).nonce;
            Ok(next_sender_nonce > sender_nonce)
        })
        .unwrap();
    }

    assert_eq!(
        get_account(&conf_1.node.data_url, &sender_addr).nonce,
        last_sender_nonce + 2,
        "The last two transactions after the flash block must be included in a block"
    );
    miners.shutdown();
}

#[test]
#[ignore]
/// This test spins up a single nakamoto node configured to mine.
/// After Nakamoto blocks are mined, it waits for a normal tenure, then issues
///  two bitcoin blocks in quick succession -- the first will contain block commits,
///  and the second "flash block" will contain no block commits.
/// The test then tries to continue producing a normal tenure: issuing a bitcoin block
///   with a sortition in it.
/// The test does 3 rounds of this to make sure that the network continues producing blocks throughout.
fn single_miner_empty_sortition() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let num_signers = 5;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let send_fee = 180;

    // partition the signer set so that ~half are listening and using node 1 for RPC and events,
    //  and the rest are using node 2

    let mut signer_test: SignerTest<SpawnedSigner> =
        SignerTest::new(num_signers, vec![(sender_addr, send_fee * 2 * 60 + 1000)]);
    let conf = signer_test.running_nodes.conf.clone();

    signer_test.boot_to_epoch_3();

    info!("------------------------- Reached Epoch 3.0 -------------------------");

    let burn_height_contract = "
       (define-data-var local-burn-block-ht uint u0)
       (define-public (run-update)
          (ok (var-set local-burn-block-ht burn-block-height)))
    ";

    let contract_tx = make_contract_publish(
        &sender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        "burn-height-local",
        burn_height_contract,
    );
    submit_tx(&conf.node.data_url, &contract_tx);

    let rl1_commits = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .clone();
    let rl1_counters = signer_test.running_nodes.counters.clone();
    let rl1_conf = signer_test.running_nodes.conf.clone();

    for _i in 0..3 {
        // Mine 1 nakamoto tenures
        info!("Mining tenure...");

        signer_test.mine_block_wait_on_processing(
            &[&rl1_conf],
            &[&rl1_counters],
            Duration::from_secs(30),
        );

        // mine the interim blocks
        for _ in 0..2 {
            let sender_nonce = get_account(&conf.node.data_url, &sender_addr).nonce;
            // check if the burn contract is already produced, if not wait for it to be included in
            //  an interim block
            if sender_nonce >= 1 {
                let contract_call_tx = make_contract_call(
                    &sender_sk,
                    sender_nonce,
                    send_fee,
                    conf.burnchain.chain_id,
                    &sender_addr,
                    "burn-height-local",
                    "run-update",
                    &[],
                );
                submit_tx(&conf.node.data_url, &contract_call_tx);
            }

            // make sure the sender's tx gets included (whether it was the contract publish or call)
            wait_for(60, || {
                let next_sender_nonce = get_account(&conf.node.data_url, &sender_addr).nonce;
                Ok(next_sender_nonce > sender_nonce)
            })
            .unwrap();
        }

        let last_active_sortition = get_sortition_info(&conf);
        assert!(last_active_sortition.was_sortition);

        // lets mine a btc flash block
        let rl1_commits_before = rl1_commits.load(Ordering::SeqCst);
        let info_before = get_chain_info(&conf);
        signer_test
            .running_nodes
            .btc_regtest_controller
            .build_next_block(2);

        wait_for(60, || {
            let info = get_chain_info(&conf);
            Ok(info.burn_block_height >= 2 + info_before.burn_block_height
                && rl1_commits.load(Ordering::SeqCst) > rl1_commits_before)
        })
        .unwrap();

        let cur_empty_sortition = get_sortition_info(&conf);
        assert!(!cur_empty_sortition.was_sortition);
        let inactive_sortition = get_sortition_info_ch(
            &conf,
            cur_empty_sortition.last_sortition_ch.as_ref().unwrap(),
        );
        assert!(inactive_sortition.was_sortition);
        assert_eq!(
            inactive_sortition.burn_block_height,
            last_active_sortition.burn_block_height + 1
        );

        info!("==================== Mined a flash block ====================");
        info!("Flash block sortition info";
              "last_active_winner" => ?last_active_sortition.miner_pk_hash160,
              "last_winner" => ?inactive_sortition.miner_pk_hash160,
              "last_active_ch" => %last_active_sortition.consensus_hash,
              "last_winner_ch" => %inactive_sortition.consensus_hash,
              "cur_empty_sortition" => %cur_empty_sortition.consensus_hash,
        );
    }
    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that signers mark a miner malicious if it doesn't propose any blocks before the block proposal timeout
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing. The block proposal timeout is set to 20 seconds.
///
/// Test Execution:
/// Block proposals are paused for the miner.
/// Tenure A starts.
/// The test waits for the block proposal timeout + 1 second.
/// Block proposals are unpaused for the miner.
/// Miner propose a block N.
/// Signers reject the block and mark the miner as malicious.
///
///
/// Test Assertion:
/// Stacks tip does not advance to block N.
fn block_proposal_timeout() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let block_proposal_timeout = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |config| {
            config.block_proposal_timeout = block_proposal_timeout;
        },
        |_| {},
        None,
        None,
    );

    let miner_sk = signer_test.running_nodes.conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

    signer_test.boot_to_epoch_3();

    // Pause the miner's block proposals
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);

    info!("------------------------- Start Tenure A -------------------------");
    let commits_before = signer_test
        .running_nodes
        .counters
        .naka_submitted_commits
        .load(Ordering::SeqCst);

    next_block_and(
        &mut signer_test.running_nodes.btc_regtest_controller,
        60,
        || {
            let commits_count = signer_test
                .running_nodes
                .counters
                .naka_submitted_commits
                .load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        },
    )
    .unwrap();

    let chain_before = get_chain_info(&signer_test.running_nodes.conf);
    std::thread::sleep(block_proposal_timeout.add(Duration::from_secs(1)));
    test_observer::clear();

    info!("------------------------- Attempt Mine Block N  -------------------------");
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    let block_proposal_n =
        wait_for_block_proposal(30, chain_before.stacks_tip_height + 1, &miner_pk)
            .expect("Failed to get block proposal N");
    wait_for_block_global_rejection(
        30,
        block_proposal_n.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Failed to get block rejections for N");

    let chain_after = get_chain_info(&signer_test.running_nodes.conf);
    assert_eq!(chain_after, chain_before);
    signer_test.shutdown();
}

/// Test a scenario where:
/// Two miners boot to Nakamoto.
/// Sortition occurs. Miner 1 wins.
/// Miner 1 proposes a block N
/// Signers accept and the stacks tip advances to N
/// Miner 1's block commits are paused so it cannot confirm the next tenure.
/// Sortition occurs. Miner 2 wins.
/// Miner 2 successfully mines blocks N+1, N+2, and N+3
/// Sortition occurs quickly, within first_proposal_burn_block_timing_secs. Miner 1 wins.
/// Miner 1 proposes block N+1'
/// Signers approve N+1', saying "Miner is not building off of most recent tenure. A tenure they
///   reorg has already mined blocks, but the block was poorly timed, allowing the reorg."
/// Miner 1 proposes N+2' and it is accepted.
/// Miner 1 wins the next tenure and mines N+4, off of miner 2's tip.
#[test]
#[ignore]
fn allow_reorg_within_first_proposal_burn_block_timing_secs() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 3;

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            // Lets make sure we never time out since we need to stall some things to force our scenario
            signer_config.block_proposal_validation_timeout = Duration::from_secs(1800);
            signer_config.tenure_last_block_proposal_timeout = Duration::from_secs(1800);
            signer_config.first_proposal_burn_block_timing = Duration::from_secs(1800);
        },
        |_| {},
        |_| {},
    );
    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    info!("------------------------- Pause Miner 1's Block Commits -------------------------");
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Nakamoto Block N -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by Block N");

    let miner_1_block_n =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_1)
            .expect("Failed to get block N");

    let block_n_height = miner_1_block_n.header.chain_length;
    info!("Block N: {block_n_height}");
    let info_after = get_chain_info(&conf_1);
    assert_eq!(info_after.stacks_tip, miner_1_block_n.header.block_hash());
    assert_eq!(info_after.stacks_tip_height, block_n_height);
    assert_eq!(block_n_height, stacks_height_before + 1);

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Miner 2 Submits a Block Commit -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Pause Miner 2's Block Mining -------------------------");
    TEST_MINE_STALL.set(true);

    info!("------------------------- Mine Tenure -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 60)
        .expect("Failed to mine BTC block");

    info!("------------------------- Miner 1 Submits a Block Commit -------------------------");
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 2 Mines Block N+1 -------------------------");

    TEST_MINE_STALL.set(false);
    let miner_2_block_n_1 = wait_for_block_pushed_by_miner_key(30, block_n_height + 1, &miner_pk_2)
        .expect("Failed to get block N+1");

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    assert_eq!(
        get_chain_info(&conf_1).stacks_tip_height,
        block_n_height + 1
    );

    info!("------------------------- Miner 2 Mines N+2 and N+3 -------------------------");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to send and mine transfer tx");
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to send and mine transfer tx");
    assert_eq!(
        get_chain_info(&conf_1).stacks_tip_height,
        block_n_height + 3
    );

    info!("------------------------- Miner 1 Wins the Next Tenure, Mines N+1' -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");

    let miner_1_block_n_1_prime =
        wait_for_block_pushed_by_miner_key(30, block_n_height + 1, &miner_pk_1)
            .expect("Failed to get block N+1'");
    assert_ne!(miner_1_block_n_1_prime, miner_2_block_n_1);

    info!("------------------------- Miner 1 Submits a Block Commit -------------------------");
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 1 Mines N+2' -------------------------");

    // Cannot use send_and_mine_transfer_tx as this relies on the peer's height
    miners.send_transfer_tx();
    let _ = wait_for_block_pushed_by_miner_key(30, block_n_height + 2, &miner_pk_1)
        .expect("Failed to get block N+2'");

    info!("------------------------- Miner 1 Mines N+4 in Next Tenure -------------------------");

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by Block N+3");
    let miner_1_block_n_4 = wait_for_block_pushed_by_miner_key(30, block_n_height + 4, &miner_pk_1)
        .expect("Failed to get block N+3");

    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip_height, block_n_height + 4);
    assert_eq!(peer_info.stacks_tip, miner_1_block_n_4.header.block_hash());

    miners.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner will produce a TenureExtend transaction
/// only after it has reached the cost threshold.
fn tenure_extend_cost_threshold() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let deployer_sk = Secp256k1PrivateKey::random();
    let deployer_addr = tests::to_addr(&deployer_sk);
    let num_txs = 10;
    let tx_fee = 10000;
    let deploy_fee = 190200;

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let idle_timeout = Duration::from_secs(10);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![(deployer_addr, deploy_fee + tx_fee * num_txs)],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
        },
        |config| {
            config.miner.tenure_extend_cost_threshold = 5;
        },
        None,
        None,
    );
    let naka_conf = signer_test.running_nodes.conf.clone();
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    info!("---- Waiting for a tenure extend ----");

    // Now, wait for a block with a tenure extend
    wait_for(idle_timeout.as_secs() + 10, || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect_err("Received a tenure extend before cost threshold was reached");

    // Now deploy a contract and call it in order to cross the threshold.
    let contract_src = format!(
        r#"
(define-data-var my-var uint u0)
(define-public (f) (begin {} (ok 1))) (begin (f))
        "#,
        ["(var-get my-var)"; 250].join(" ")
    );

    // First, lets deploy the contract
    let mut nonce = 0;
    let contract_tx = make_contract_publish(
        &deployer_sk,
        nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        "small-contract",
        &contract_src,
    );
    submit_tx(&http_origin, &contract_tx);
    nonce += 1;

    // Wait for the contract to be included in a block
    wait_for(60, || {
        let account = get_account(&http_origin, &deployer_addr);
        Ok(account.nonce == nonce)
    })
    .expect("Contract not included in block");

    // Ensure the tenure was not extended in that block
    assert!(!last_block_contains_tenure_change_tx(
        TenureChangeCause::Extended
    ));

    // Now, lets call the contract a bunch of times to increase the tenure cost
    for _ in 0..num_txs {
        let call_tx = make_contract_call(
            &deployer_sk,
            nonce,
            tx_fee,
            naka_conf.burnchain.chain_id,
            &deployer_addr,
            "small-contract",
            "f",
            &[],
        );
        submit_tx(&http_origin, &call_tx);
        nonce += 1;
    }

    // Now, wait for a block with a tenure extend
    wait_for(idle_timeout.as_secs() + 10, || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect("Timed out waiting for a block with a tenure extend");

    signer_test.shutdown();
}

#[test]
#[ignore]
/// Test that a miner that begins mining before seeing the last block of the
/// previous tenure can be interrupted when its tip advances to the last block,
/// then successfully mine a block on top of that block.
///
/// Test Setup:
/// The test spins up five stacks signers, one miner Nakamoto node, and a corresponding bitcoind.
/// The stacks node is then advanced to Epoch 3.0 boundary to allow block signing.
///
/// Test Execution:
/// Miner 1 mines a tenure change block, then mines a second block, block N,
/// but the signers will not broadcast it, and the miner will stall before
/// broadcasting. Miner 2 wins the next sortition and proposes a block N',
/// since it has not seen N, but signers are ignoring proposals so that it is
/// not rejected. Miner 1 then announces N. Miner 2 sees N, stops waiting
/// for signatures on N' and submits a new proposal, N+1, which is accepted.
/// Finally a new tenure arrives and N+2 is mined.
///
/// Test Assertion:
/// Stacks tip advances to N+1'
fn interrupt_miner_on_new_stacks_tip() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let num_signers = 5;
    let num_txs = 2;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            // we're deliberately stalling proposals: don't punish this in this test!
            signer_config.block_proposal_timeout = Duration::from_secs(240);
            // make sure that we don't allow forking due to burn block timing
            signer_config.first_proposal_burn_block_timing = Duration::from_secs(60);
        },
        |config| {
            config.miner.block_rejection_timeout_steps = [(0, Duration::from_secs(1200))].into()
        },
        |_| {},
    );

    let skip_commit_op_rl1 = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let skip_commit_op_rl2 = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, conf_2) = miners.get_node_configs();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    let all_signers: Vec<_> = miners
        .signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect();

    // Pause Miner 2's commits to ensure Miner 1 wins the first sortition.
    skip_commit_op_rl2.set(true);
    miners.boot_to_epoch_3();

    let sortdb = conf_1.get_burnchain().open_sortition_db(true).unwrap();

    info!("Pausing miner 1's block commit submissions");
    skip_commit_op_rl1.set(true);

    info!("------------------------- RL1 Wins Sortition -------------------------");
    info!("Mine RL1 Tenure");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    // Make the miner stall before broadcasting the block once it has been approved
    TEST_P2P_BROADCAST_STALL.set(true);
    // Make the signers not broadcast the block once it has been approved
    TEST_SKIP_BLOCK_BROADCAST.set(true);

    // submit a tx so that the miner will mine a stacks block
    let tx = miners.send_transfer_tx();
    // Wait for the block with this transfer to be accepted
    wait_for(30, || {
        Ok(test_observer::get_mined_nakamoto_blocks()
            .last()
            .unwrap()
            .tx_events
            .iter()
            .any(|t| {
                let TransactionEvent::Success(TransactionSuccessEvent { txid, .. }) = t else {
                    return false;
                };
                txid.to_hex() == tx
            }))
    })
    .expect("Timed out waiting for the transfer tx to be mined");

    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_n = blocks.last().expect("No blocks mined");
    wait_for_block_global_acceptance_from_signers(30, &block_n.signer_signature_hash, &all_signers)
        .expect("Timed out waiting for block acceptance of N");
    info!("Block N is {}", block_n.stacks_height);

    info!("------------------------- RL2 Wins Sortition -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("Make signers ignore all block proposals, so that they don't reject it quickly");
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(all_signers.clone());

    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");
    // make sure the tenure was won by RL2
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("------------------------- RL2 Proposes Block N' -------------------------");

    let miner_2_block_n_prime = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Failed to propose block N'");
    assert_eq!(
        miner_2_block_n_prime.header.chain_length,
        block_n.stacks_height
    );

    info!("------------------------- Block N is Announced -------------------------");

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_1, miner_pk_2]);
    TEST_P2P_BROADCAST_STALL.set(false);

    // Wait for RL2's tip to advance to the last block
    wait_for(30, || {
        let Some(chain_info_2) = get_chain_info_opt(&conf_2) else {
            return Ok(false);
        };
        Ok(chain_info_2.stacks_tip_height == block_n.stacks_height)
    })
    .expect("Timed out waiting for RL2 to advance to block N");

    info!("------------------------- RL2 Proposes Block N+1 -------------------------");
    // Miner 2 should be interrupted from waiting for N' to be accepted when it sees N
    info!("Stop signers from ignoring proposals");
    TEST_IGNORE_ALL_BLOCK_PROPOSALS.set(Vec::new());
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    let miner_2_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 2, &miner_pk_2)
        .expect("Failed to propose block N+1");
    assert_eq!(
        miner_2_block_n_1.header.chain_length,
        block_n.stacks_height + 1
    );

    info!("------------------------- Signers Accept Block N+1 -------------------------");
    let miner_2_block_n_1 =
        wait_for_block_pushed(30, miner_2_block_n_1.header.signer_signature_hash())
            .expect("Failed to see block acceptance of Miner 2's Block N+1");
    assert_eq!(
        miner_2_block_n_1.header.block_hash(),
        miners.get_peer_stacks_tip()
    );

    info!("------------------------- Next Tenure Builds on N+1 -------------------------");
    miners.submit_commit_miner_1(&sortdb);
    miners.submit_commit_miner_2(&sortdb);

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by tenure change tx");

    wait_for(30, || {
        let Some(chain_info) = get_chain_info_opt(&conf_1) else {
            return Ok(false);
        };
        Ok(chain_info.stacks_tip_height == block_n.stacks_height + 2)
    })
    .expect("Timed out waiting for height to advance to block N+2");

    miners.wait_for_chains(120);
    miners.shutdown();
}

#[test]
#[ignore]
/// This test verifies that a miner will produce a TenureExtend transaction
/// after the signers' idle timeout, plus buffer, is reached.
fn tenure_extend_after_idle_signers_with_buffer() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();

    info!("------------------------- Test Setup -------------------------");
    let num_signers = 5;
    let idle_timeout = Duration::from_secs(1);
    let buffer = Duration::from_secs(20);
    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        num_signers,
        vec![],
        |config| {
            config.tenure_idle_timeout = idle_timeout;
            config.tenure_idle_timeout_buffer = buffer;
        },
        |config| {
            config.miner.tenure_extend_cost_threshold = 0;
        },
        None,
        None,
    );

    signer_test.boot_to_epoch_3();

    info!("---- Nakamoto booted, starting test ----");
    // Get the unix timestamp before the block is mined
    let before_timestamp = get_epoch_time_secs();
    signer_test.mine_nakamoto_block(Duration::from_secs(30), true);

    // Check the tenure extend timestamps to verify that they have factored in the buffer
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let last_block = blocks.last().expect("No blocks mined");
    let timestamps: HashSet<_> = test_observer::get_stackerdb_chunks()
        .into_iter()
        .flat_map(|chunk| chunk.modified_slots)
        .filter_map(|chunk| {
            let message = SignerMessage::consensus_deserialize(&mut chunk.data.as_slice())
                .expect("Failed to deserialize SignerMessage");

            match message {
                SignerMessage::BlockResponse(BlockResponse::Accepted(accepted))
                    if accepted.signer_signature_hash == last_block.signer_signature_hash =>
                {
                    Some(accepted.response_data.tenure_extend_timestamp)
                }
                _ => None,
            }
        })
        .collect();
    for timestamp in timestamps {
        assert!(
            timestamp >= before_timestamp + buffer.as_secs(),
            "Timestamp {} is not greater than or equal to {}",
            timestamp,
            before_timestamp + buffer.as_secs()
        );
    }

    info!("---- Waiting for a tenure extend ----");

    // Now, wait for a block with a tenure extend, to make sure it eventually does extend
    wait_for((idle_timeout + buffer * 2).as_secs(), || {
        Ok(last_block_contains_tenure_change_tx(
            TenureChangeCause::Extended,
        ))
    })
    .expect("Timed out waiting for a block with a tenure extend");

    signer_test.shutdown();
}

/// Test a scenario where a previous miner can extend a tenure when it is favoured by signers over the incoming miner.
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure.
/// Miner 1 proposes a block N with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B.
/// Miner 2 proposes block N+1' AFTER signers' block proposal timeout.
/// Signers reject block N+1' and mark miner 2 as malicious
/// Miner 1 proposes block N+1 with a TenureChangeCause::Extended
/// Signers accept and the stacks tip advances to N+1
/// Miner 2 wins the third tenure C and proposes a block N+2 with a TenureChangeCause::BlockFound
/// Signers accept block N+2.
///
/// Asserts:
/// - Block N contains the TenureChangeCause::BlockFound
/// - Block N+1 contains the TenureChangeCause::Extended
/// - Block N+2 contains the TenureChangeCause::BlockFound
/// - The stacks tip advances to N+2
#[test]
#[ignore]
fn prev_miner_extends_if_incoming_miner_fails_to_mine_success() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;

    let block_proposal_timeout = Duration::from_secs(30);
    let tenure_extend_wait_timeout = block_proposal_timeout;
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        0,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Timed out mining BTC block followed by tenure change tx");
    btc_blocks_mined += 1;

    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    // Pause the block proposal broadcast so that miner 2 will be unable to broadcast its
    // tenure change proposal BEFORE the block_proposal_timeout and will be marked invalid.
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_2]);

    info!("------------------------- Miner 2 Mines an Empty Tenure B -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 60)
        .expect("Timed out waiting for BTC block");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);
    info!(
        "------------------------- Wait for Miner 2 to be Marked Invalid -------------------------"
    );
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    // Make sure that miner 2 gets marked invalid by not proposing a block BEFORE block_proposal_timeout
    std::thread::sleep(block_proposal_timeout.add(Duration::from_secs(1)));

    info!("------------------------- Wait for Miner 1's Block N+1 to be Mined ------------------------";
        "stacks_height_before" => %stacks_height_before);

    let miner_1_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_1)
        .expect("Timed out waiting for block proposal N+1 from miner 1");
    // Unpause miner 2's block proposal broadcast
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    let miner_2_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Timed out waiting for block proposal N+1' from miner 2");
    info!("------------------------- Verify Miner 2's N+1' was Rejected and Miner 1's N+1 Accepted-------------------------");

    let miner_1_block_n_1 =
        wait_for_block_pushed(30, miner_1_block_n_1.header.signer_signature_hash())
            .expect("Timed out waiting for Miner 1's block N+1 to be approved pushed");
    wait_for_block_global_rejection(
        30,
        miner_2_block_n_1.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Timed out waiting for global rejection of Miner 2's block N+1'");

    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_1_block_n_1.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!(
        "------------------------- Verify Tenure Change Extend Tx in Miner 1's Block N+1 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::Extended);

    info!("------------------------- Unpause Miner 2's Block Commits -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Miner 2 Mines a Normal Tenure C -------------------------");

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by a tenure change tx");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(
        miners.get_peer_stacks_tip_height(),
        starting_peer_height + 3
    );
    miners.shutdown();
}

/// Test a scenario where a previous miner is unable to extend its tenure if the signers are configured to favour the incoming miner.
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure A.
/// Miner 1 proposes a block N with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B.
/// Miner 2 is paused and cannot propose block N+1.
/// Miner 1 attempts to extend tenure A with block N+1' containg a TenureChangeCause::Extended
/// Signers reject block N+1' and the stacks tip remains at N
/// Miner 2 is unpaused
/// Miner 2 proposes block N+1 with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N+1
/// Miner 2 wins the third tenure C
/// Miner 2 proposes block N+2 with a TenureChangeCause::BlockFound
///
/// Asserts:
/// - Block N contains the TenureChangeCause::BlockFound
/// - Block N+1' contains a TenureChangeCause::Extended and is rejected
/// - Block N+1 contains the TenureChangeCause::BlockFound
/// - Block N+2 contains the TenureChangeCause::BlockFound
/// - The stacks tip advances to N+2
#[test]
#[ignore]
fn prev_miner_extends_if_incoming_miner_fails_to_mine_failure() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;

    // Ensure Miner 1 will attempt to extend BEFORE signers are willing to consider it.
    let block_proposal_timeout = Duration::from_secs(500); // make it way in the future so miner 1 is rejected
    let tenure_extend_wait_timeout = Duration::from_secs(30);

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        0,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by a tenure change tx");
    btc_blocks_mined += 1;

    // Confirm that Miner 1 won the tenure.
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners.submit_commit_miner_2(&sortdb);

    let burn_height_before = get_burn_height();

    // Pause the block proposal broadcast so that miner 2 will be unable to broadcast its
    // tenure change proposal BEFORE miner 1 attempts to extend.
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_2]);

    info!("------------------------- Miner 2 Wins Tenure B -------------------------";
        "burn_height_before" => burn_height_before,
        "stacks_height_before" => %stacks_height_before
    );
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 60)
        .expect("Failed to mine BTC block");
    btc_blocks_mined += 1;

    assert_eq!(stacks_height_before, miners.get_peer_stacks_tip_height());

    // Confirm that Miner 2 won the tenure.
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!(
        "------------------------- Wait for Miner 1 to think Miner 2 is Invalid -------------------------"
    );
    // Make sure that miner 1 thinks miner 2 is invalid.
    std::thread::sleep(tenure_extend_wait_timeout.add(Duration::from_secs(1)));

    info!("------------------------- Wait for Miner 1's Block N+1' to be Proposed ------------------------";
        "stacks_height_before" => %stacks_height_before);

    let miner_1_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_1)
        .expect("Timed out waiting for N+1' block proposal from miner 1");
    assert_eq!(
        miner_1_block_n_1
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::Extended
    );

    info!("------------------------- Verify that Miner 1's Block N+1' was Rejected ------------------------");
    // Miner 1's proposed block should get rejected by the signers
    wait_for_block_global_rejection(
        30,
        miner_1_block_n_1.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Timed out waiting for Block N+1' to be globally rejected");

    assert_eq!(stacks_height_before, miners.get_peer_stacks_tip_height());

    info!("------------------------- Wait for Miner 2's Block N+1 BlockFound to be Proposed ------------------------";
        "stacks_height_before" => %stacks_height_before
    );

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Get miner 2's N+1 block proposal
    let miner_2_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Timed out waiting for N+1 block proposal from miner 2");

    info!("------------------------- Wait for Miner 2's Block N+1 to be Approved ------------------------";
        "stacks_height_before" => %stacks_height_before
    );

    // Miner 2's proposed block should get approved and pushed
    let miner_2_block_n_1 =
        wait_for_block_pushed(30, miner_2_block_n_1.header.signer_signature_hash())
            .expect("Timed out waiting for Block N+1 to be pushed");

    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_2_block_n_1.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!(
        "------------------------- Verify BlockFound in Miner 2's Block N+1 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::BlockFound);

    info!("------------------------- Unpause Miner 2's Block Commits -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Miner 2 Mines a Normal Tenure C -------------------------");

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by a tenure change tx");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);
    info!(
        "------------------------- Verify Tenure Change Tx in Miner 2's Block N+2 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::BlockFound);

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(
        miners.get_peer_stacks_tip_height(),
        starting_peer_height + 3
    );

    miners.shutdown();
}

/// Test a scenario where:
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure A.
/// Miner 1 proposes a block N with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B.
/// Miner 2 proposes block N+1 with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N+1
/// Miner 1 never issues a TenureExtend transaction
/// Miner 2 wins the third tenure C
/// Miner 2 proposes block N+2 with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N+2
///
/// Asserts:
/// - Block N contains the TenureChangeCause::BlockFound
/// - Block N+1 contains the TenureChangeCause::BlockFound
/// - Block N+2 contains the TenureChangeCause::BlockFound
/// - The stacks tip advances to N+2
/// - Miner 1 does not produce a tenure extend block at all
#[test]
#[ignore]
fn prev_miner_will_not_attempt_to_extend_if_incoming_miner_produces_a_block() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;

    let block_proposal_timeout = Duration::from_secs(100);
    let tenure_extend_wait_timeout = Duration::from_secs(20);
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        0,
        |signer_config| {
            signer_config.block_proposal_timeout = block_proposal_timeout;
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block followed by a tenure change tx");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner A won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners.submit_commit_miner_2(&sortdb);

    let burn_height_before = get_burn_height();

    info!("------------------------- Miner 2 Mines Tenure B -------------------------";
        "burn_height_before" => burn_height_before,
        "stacks_height_before" => stacks_height_before
    );
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 60)
        .expect("Failed to mine BTC block");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("------------------------- Get Miner 2's N+1 block -------------------------");

    let miner_2_block_n_1 = wait_for_block_proposal(60, stacks_height_before + 1, &miner_pk_2)
        .expect("Timed out waiting for N+1 block proposal from miner 2");
    let miner_2_block_n_1 =
        wait_for_block_pushed(30, miner_2_block_n_1.header.signer_signature_hash())
            .expect("Timed out waiting for N+1 block to be approved");

    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_2_block_n_1.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    let stacks_height_before = peer_info.stacks_tip_height;

    info!("------------------------- Ensure Miner 1 Never Isues a Tenure Extend -------------------------";
        "stacks_height_before" => %stacks_height_before);

    // Ensure the tenure extend wait timeout is passed so if a miner was going to extend, it would be now.
    std::thread::sleep(tenure_extend_wait_timeout.add(Duration::from_secs(1)));

    assert!(
        wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_1).is_err(),
        "Miner 1 should not have proposed a block N+1'"
    );

    assert_eq!(stacks_height_before, miners.get_peer_stacks_tip_height());

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(stacks_height_before, starting_peer_height + 2);
    miners.shutdown();
}

/// Test a scenario where a non-blocking minority of signers are configured to favour the incoming miner.
/// The previous miner should extend its tenure and succeed as a majority are configured to favour it
/// and its subsequent blocks should be be approved.
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure A.
/// Miner 1 proposes a block N with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B.
/// A majority of signers mark miner 2 as invalid.
/// Miner 2 proposes block N+1' with a TenureChangeCause::BlockFound
/// A majority fo signers reject block N+1'.
/// Miner 1 proposes block N+1 with a TenureChangeCause::Extended
/// A majority of signers accept and the stacks tip advances to N+1
/// Miner 1 proposes block N+2 with a transfer tx
/// ALL signers should accept block N+2.
/// Miner 2 wins the third tenure C.
/// Miner 2 proposes block N+3 with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N+3
///
/// Asserts:
/// - Block N contains the TenureChangeCause::BlockFound
/// - Block N+1' contains a TenureChangeCause::BlockFound and is rejected
/// - Block N+1 contains the TenureChangeCause::Extended
/// - Block N+2 is accepted.
/// - Block N+3 contains the TenureChangeCause::BlockFound.
/// - The stacks tip advances to N+3
#[test]
#[ignore]
fn non_blocking_minority_configured_to_favour_incoming_miner() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let num_txs = 1;
    let non_block_minority = num_signers * 2 / 10;

    let favour_prev_miner_block_proposal_timeout = Duration::from_secs(20);
    let favour_incoming_miner_block_proposal_timeout = Duration::from_secs(500);
    // Make sure the miner attempts to extend after the minority mark the incoming as invalid
    let tenure_extend_wait_timeout = favour_prev_miner_block_proposal_timeout;

    info!("------------------------- Test Setup -------------------------");
    // partition the signer set so that ~half are listening and using node 1 for RPC and events,
    //  and the rest are using node 2
    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            let port = signer_config.endpoint.port();
            // Note signer ports are based on the number of them, the first being 3000, the last being 3000 + num_signers - 1
            if port < 3000 + non_block_minority as u16 {
                signer_config.block_proposal_timeout = favour_incoming_miner_block_proposal_timeout;
            } else {
                signer_config.block_proposal_timeout = favour_prev_miner_block_proposal_timeout;
            }
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to start Tenure A");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners.submit_commit_miner_2(&sortdb);
    let burn_height_before = get_burn_height();
    // Pause the block proposal broadcast so that miner 2 AND miner 1 are unable to propose
    // a block BEFORE block_proposal_timeout
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_2, miner_pk_1]);

    info!("------------------------- Miner 2 Wins Tenure B -------------------------";
        "burn_height_before" => burn_height_before,
        "stacks_height_before" => %stacks_height_before
    );
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to start Tenure B");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!(
        "------------------------- Wait for Miner 2 to be Marked Invalid by a Majority of Signers -------------------------"
    );
    // Make sure that miner 1 and a majority of signers thinks miner 2 is invalid.
    std::thread::sleep(tenure_extend_wait_timeout.add(Duration::from_secs(1)));

    // Allow miner 2 to attempt to start their tenure.
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_1]);

    info!("------------------------- Wait for Miner 2's Block N+1' to be Proposed ------------------------";
        "stacks_height_before" => %stacks_height_before);

    let miner_2_block_n_1 = wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_2)
        .expect("Miner 2 did not propose Block N+1'");

    assert_eq!(
        miner_2_block_n_1
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::BlockFound
    );

    info!("------------------------- Verify that Miner 2's Block N+1' was Rejected ------------------------");

    // Miner 2's proposed block should get rejected by the signers
    wait_for_block_global_rejection(
        30,
        miner_2_block_n_1.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Timed out waiting for Block N+1' to be globally rejected");

    assert_eq!(miners.get_peer_stacks_tip_height(), stacks_height_before,);

    info!("------------------------- Wait for Miner 1's Block N+1 Extended to be Mined ------------------------";
        "stacks_height_before" => %stacks_height_before
    );

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Get miner 1's N+1 block proposal
    let miner_1_block_n_1 =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_1)
            .expect("Timed out waiting for Miner 1 to mine N+1");
    let peer_info = miners.get_peer_info();

    assert_eq!(peer_info.stacks_tip, miner_1_block_n_1.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!(
        "------------------------- Verify BlockFound in Miner 1's Block N+1 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::Extended);

    info!("------------------------- Miner 1 Mines Block N+2 with Transfer Tx -------------------------");
    let stacks_height_before = peer_info.stacks_tip_height;
    // submit a tx so that the miner will mine an extra block
    let _ = miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to mine transfer tx");

    // Get miner 1's N+2 block proposal
    let miner_1_block_n_2 =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_1)
            .expect("Timed out waiting for miner 1 to mine N+2");

    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_1_block_n_2.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!("------------------------- Unpause Miner 2's Block Commits -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    let burn_height_before = get_burn_height();

    info!("------------------------- Miner 2 Mines a Normal Tenure C -------------------------";
    "burn_height_before" => burn_height_before);

    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by a tenure change tx");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!(
        "------------------------- Verify Tenure Change Tx in Miner 2's Block N+3 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::BlockFound);

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(
        miners.get_peer_stacks_tip_height(),
        starting_peer_height + 4
    );
    miners.shutdown();
}

/// Test a scenario where a non-blocking majority of signers are configured to favour the previous miner
/// extending their tenure when the incoming miner is slow to propose a block. The incoming miner should succeed
/// and its subsequent blocks should be be approved.
/// Two miners boot to Nakamoto.
/// Miner 1 wins the first tenure A.
/// Miner 1 proposes a block N with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N
/// Miner 2 wins the second tenure B.
/// A minority of signers mark miner 2 as invalid.
/// Miner 1 proposes block N+1' with a TenureChangeCause::Extended
/// A majority of signers reject block N+1'
/// Miner 2 proposes block N+1 with a TenureChangeCause::BlockFound
/// A majority fo signers accept block N+1.
/// Miner 2 proposes block N+2 with a transfer tx
/// A majority of signers should accept block N+2.
/// Miner 1 wins the third tenure C.
/// Miner 1 proposes block N+3 with a TenureChangeCause::BlockFound
/// Signers accept and the stacks tip advances to N+3
///
/// Asserts:
/// - Block N contains the TenureChangeCause::BlockFound
/// - Block N+1' contains a TenureChangeCause::Extended and is rejected
/// - Block N+1 contains the TenureChangeCause::BlockFound
/// - Block N+2 is accepted.
/// - Block N+3 contains the TenureChangeCause::BlockFound.
/// - The stacks tip advances to N+3
#[test]
#[ignore]
fn non_blocking_minority_configured_to_favour_prev_miner() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_signers = 5;
    let non_block_minority = num_signers * 2 / 10;
    let num_txs = 1;

    let favour_prev_miner_block_proposal_timeout = Duration::from_secs(20);
    let favour_incoming_miner_block_proposal_timeout = Duration::from_secs(500);
    // Make sure the miner attempts to extend after the minority mark the incoming as invalid
    let tenure_extend_wait_timeout = favour_prev_miner_block_proposal_timeout;

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            let port = signer_config.endpoint.port();
            // Note signer ports are based on the number of them, the first being 3000, the last being 3000 + num_signers - 1
            if port < 3000 + non_block_minority as u16 {
                signer_config.block_proposal_timeout = favour_prev_miner_block_proposal_timeout;
            } else {
                signer_config.block_proposal_timeout = favour_incoming_miner_block_proposal_timeout;
            }
        },
        |config| {
            config.miner.tenure_extend_wait_timeout = tenure_extend_wait_timeout;
        },
        |_| {},
    );

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let get_burn_height = || {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height
    };
    let starting_peer_height = get_chain_info(&conf_1).stacks_tip_height;
    let starting_burn_height = get_burn_height();
    let mut btc_blocks_mined = 0;

    info!("------------------------- Pause Miner 1's Block Commit -------------------------");
    // Make sure miner 1 doesn't submit any further block commits for the next tenure BEFORE mining the bitcoin block
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Normal Tenure A -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block and Tenure Change Tx Block");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!("------------------------- Submit Miner 2 Block Commit -------------------------");
    miners.submit_commit_miner_2(&sortdb);
    // Pause the block proposal broadcast so that miner 2 will be unable to broadcast its
    // tenure change proposal BEFORE miner 1 attempts to extend.
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_2]);

    let stacks_height_before = miners.get_peer_stacks_tip_height();
    info!("------------------------- Miner 2 Wins Tenure B -------------------------";
        "stacks_height_before" => %stacks_height_before);
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to start Tenure B");
    btc_blocks_mined += 1;

    assert_eq!(stacks_height_before, miners.get_peer_stacks_tip_height());

    // assure we have a successful sortition that miner 2 won
    verify_sortition_winner(&sortdb, &miner_pkh_2);
    info!(
        "------------------------- Wait for Miner 1 to think Miner 2 is Invalid -------------------------"
    );
    // Make sure that miner 1 thinks miner 2 is invalid.
    std::thread::sleep(tenure_extend_wait_timeout.add(Duration::from_secs(1)));

    info!("------------------------- Wait for Miner 1's Block N+1' to be Proposed ------------------------";
        "stacks_height_before" => %stacks_height_before);

    let miner_1_block_n_1_prime =
        wait_for_block_proposal(30, stacks_height_before + 1, &miner_pk_1)
            .expect("Miner 1 failed to propose block N+1'");
    assert_eq!(
        miner_1_block_n_1_prime
            .try_get_tenure_change_payload()
            .unwrap()
            .cause,
        TenureChangeCause::Extended
    );

    info!("------------------------- Verify that Miner 1's Block N+1' was Rejected ------------------------");
    wait_for_block_global_rejection(
        30,
        miner_1_block_n_1_prime.header.signer_signature_hash(),
        num_signers,
    )
    .expect("Failed to reach rejection consensus for Miner 1's Block N+1'");

    assert_eq!(stacks_height_before, miners.get_peer_stacks_tip_height());

    info!("------------------------- Wait for Miner 2's Block N+1 BlockFound to be Proposed and Approved------------------------";
        "stacks_height_before" => %stacks_height_before
    );

    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    let miner_2_block_n_1 =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_2)
            .expect("Miner 2's block N+1 was not mined");
    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_2_block_n_1.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!("------------------------- Verify Minority of Signer's Rejected Miner 2's Block N+1 -------------------------");
    wait_for_block_rejections(
        30,
        miner_2_block_n_1.header.signer_signature_hash(),
        non_block_minority,
    )
    .expect("Failed to get expected rejections for Miner 2's block N+1.");
    info!(
        "------------------------- Verify BlockFound in Miner 2's Block N+1 -------------------------"
    );
    verify_last_block_contains_tenure_change_tx(TenureChangeCause::BlockFound);

    info!("------------------------- Miner 2 Mines Block N+2 with Transfer Tx -------------------------");
    let stacks_height_before = miners.get_peer_stacks_tip_height();
    miners
        .send_and_mine_transfer_tx(30)
        .expect("Failed to Mine Block N+2");

    let miner_2_block_n_2 =
        wait_for_block_pushed_by_miner_key(30, stacks_height_before + 1, &miner_pk_2)
            .expect("Miner 2's block N+1 was not mined");
    let peer_info = miners.get_peer_info();
    assert_eq!(peer_info.stacks_tip, miner_2_block_n_2.header.block_hash());
    assert_eq!(peer_info.stacks_tip_height, stacks_height_before + 1);

    info!(
        "------------------------- Verify Miner 2's Block N+2 is still Rejected by Minority Signers -------------------------"
    );
    wait_for_block_rejections(
        30,
        miner_2_block_n_2.header.signer_signature_hash(),
        non_block_minority,
    )
    .expect("Failed to get expected rejections for Miner 2's block N+1.");

    info!("------------------------- Unpause Miner 1's Block Commits -------------------------");
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 1 Mines a Normal Tenure C -------------------------");
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to start Tenure C and mine block N+3");
    btc_blocks_mined += 1;

    // assure we have a successful sortition that miner 1 won
    verify_sortition_winner(&sortdb, &miner_pkh_1);

    info!(
        "------------------------- Confirm Burn and Stacks Block Heights -------------------------"
    );
    assert_eq!(get_burn_height(), starting_burn_height + btc_blocks_mined);
    assert_eq!(
        miners.get_peer_stacks_tip_height(),
        starting_peer_height + 4
    );
    miners.shutdown();
}

/// Test a scenario where:
/// Two miners boot to Nakamoto.
/// Sortition occurs. Miner 1 wins.
/// Miner 1 proposes a block N
/// Signers accept and the stacks tip advances to N
/// Miner 1's block commits are paused so it cannot confirm the next tenure.
/// Sortition occurs. Miner 2 wins.
/// Miner 2 successfully mines blocks N+1
/// Miner 1 wins the next sortition, with its block commit not confirming the last tenure.
/// Miner 1 proposes block N+1'
/// 3 signers approve N+1', saying "Miner is not building off of most recent tenure. A tenure they
///   reorg has already mined blocks, but the block was poorly timed, allowing the reorg."
/// The other 3 signers reject N+1', because their `first_proposal_burn_block_timing_secs` is
///   shorter and has been exceeded.
/// Miner 1 proposes N+1' again, and all signers reject it this time.
/// Miner 2 proposes N+2, a tenure extend block and it is accepted by all signers.
#[test]
#[ignore]
fn mark_miner_as_invalid_if_reorg_is_rejected() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    info!("------------------------- Test Setup -------------------------");

    let num_signers = 5;
    let num_txs = 3;

    let mut miners = MultipleMinerTest::new_with_config_modifications(
        num_signers,
        num_txs,
        |signer_config| {
            // Lets make sure we never time out since we need to stall some things to force our scenario
            signer_config.block_proposal_validation_timeout = Duration::from_secs(1800);
            signer_config.tenure_last_block_proposal_timeout = Duration::from_secs(1800);
            if signer_config.endpoint.port() % 2 == 0 {
                // Even signers will allow a reorg for a long time
                signer_config.first_proposal_burn_block_timing = Duration::from_secs(1800);
            } else {
                // Odd signers will not allow a reorg at all
                signer_config.first_proposal_burn_block_timing = Duration::from_secs(0);
            }
        },
        |_| {},
        |_| {},
    );
    let all_signers = miners
        .signer_test
        .signer_stacks_private_keys
        .iter()
        .map(StacksPublicKey::from_private)
        .collect::<Vec<_>>();
    let mut approving_signers = vec![];
    let mut rejecting_signers = vec![];
    for (i, signer_config) in miners.signer_test.signer_configs.iter().enumerate() {
        let public_key = all_signers[i].clone();
        if signer_config.endpoint.port() % 2 == 0 {
            // Even signers will allow a reorg for a long time
            approving_signers.push(public_key);
        } else {
            // Odd signers will not allow a reorg at all
            rejecting_signers.push(public_key);
        }
    }
    let rl1_skip_commit_op = miners
        .signer_test
        .running_nodes
        .counters
        .naka_skip_commit_op
        .clone();
    let rl2_skip_commit_op = miners.rl2_counters.naka_skip_commit_op.clone();

    let (conf_1, _) = miners.get_node_configs();
    let (miner_pk_1, miner_pk_2) = miners.get_miner_public_keys();
    let (miner_pkh_1, miner_pkh_2) = miners.get_miner_public_key_hashes();

    info!("------------------------- Pause Miner 2's Block Commits -------------------------");

    // Make sure Miner 2 cannot win a sortition at first.
    rl2_skip_commit_op.set(true);

    miners.boot_to_epoch_3();

    let burnchain = conf_1.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    info!("------------------------- Pause Miner 1's Block Commits -------------------------");
    rl1_skip_commit_op.set(true);

    info!("------------------------- Miner 1 Mines a Nakamoto Block N -------------------------");
    let info_before = get_chain_info(&conf_1);
    miners
        .mine_bitcoin_block_and_tenure_change_tx(&sortdb, TenureChangeCause::BlockFound, 30)
        .expect("Failed to mine BTC block followed by Block N");
    verify_sortition_winner(&sortdb, &miner_pkh_1);
    let block_n =
        wait_for_block_pushed_by_miner_key(30, info_before.stacks_tip_height + 1, &miner_pk_1)
            .expect("Failed to get block N");
    let block_n_height = block_n.header.chain_length;
    info!("Block N: {block_n_height}");

    let info_after = get_chain_info(&conf_1);
    assert_eq!(info_after.stacks_tip, block_n.header.block_hash());
    assert_eq!(
        info_after.stacks_tip_height,
        info_before.stacks_tip_height + 1
    );
    assert_eq!(info_after.stacks_tip_height, block_n_height);

    info!("------------------------- Miner 2 Submits a Block Commit -------------------------");
    miners.submit_commit_miner_2(&sortdb);

    info!("------------------------- Pause Miner 2's Block Mining -------------------------");
    TEST_MINE_STALL.set(true);

    info!("------------------------- Mine 2 wins the Next Tenure -------------------------");
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");
    verify_sortition_winner(&sortdb, &miner_pkh_2);

    info!("------------------------- Miner 1 Submits a Block Commit -------------------------");
    miners.submit_commit_miner_1(&sortdb);

    info!("------------------------- Miner 2 Mines Block N+1 -------------------------");
    TEST_MINE_STALL.set(false);

    let block_n_1 = wait_for_block_pushed_by_miner_key(30, block_n_height + 1, &miner_pk_2)
        .expect("Failed to get block N+1");

    let info_after = get_chain_info(&conf_1);
    assert_eq!(info_after.stacks_tip_height, block_n_height + 1);
    assert_eq!(info_after.stacks_tip, block_n_1.header.block_hash());

    info!("------------------------- Miner 1 Wins the Next Tenure, Mines N+1' -------------------------");
    test_observer::clear();
    miners
        .mine_bitcoin_blocks_and_confirm(&sortdb, 1, 30)
        .expect("Failed to mine BTC block");
    let block_n_1_prime = wait_for_block_proposal(30, block_n_height + 1, &miner_pk_1)
        .expect("Failed to get block proposal N+1'");
    // Stall the miner from proposing again until we're ready
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk_1]);

    info!("------------------------- Wait for 3 acceptances and 2 rejections -------------------------");
    let signer_signature_hash = block_n_1_prime.header.signer_signature_hash();
    wait_for_block_acceptance_from_signers(30, &signer_signature_hash, &approving_signers)
        .expect("Timed out waiting for block acceptance from approving signers");
    let rejections = wait_for_block_rejections_from_signers(30, &rejecting_signers)
        .expect("Timed out waiting for block rejection from rejecting signers");
    for rejection in rejections {
        assert_eq!(rejection.signer_signature_hash, signer_signature_hash);
        assert_eq!(
            rejection.response_data.reject_reason,
            RejectReason::ReorgNotAllowed,
            "Reject reason is not ReorgNotAllowed"
        );
    }

    info!("------------------------- Miner 1 Proposes N+1' Again -------------------------");
    test_observer::clear();
    // Allow the miner to propose again
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);
    let block_n_1_prime = wait_for_block_proposal(30, block_n_height + 1, &miner_pk_1)
        .expect("Failed to propose block N+1' again");

    info!("------------------------- Wait for 5 rejections -------------------------");

    let signer_signature_hash = block_n_1_prime.header.signer_signature_hash();
    let rejections = wait_for_block_rejections_from_signers(30, &all_signers)
        .expect("Timed out waiting for block rejection from all signers");
    for rejection in rejections {
        assert_eq!(rejection.signer_signature_hash, signer_signature_hash);
        assert!(
            rejection.response_data.reject_reason == RejectReason::ReorgNotAllowed
                || rejection.response_data.reject_reason == RejectReason::InvalidMiner
        );
    }
    miners.shutdown();
}
