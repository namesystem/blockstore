use std::cell::LazyCell;
// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2023 Stacks Open Internet Foundation
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
use std::collections::{BTreeMap, HashMap, HashSet};
use std::net::ToSocketAddrs;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};
use std::{env, thread};

use clarity::vm::ast::ASTRules;
use clarity::vm::costs::ExecutionCost;
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier};
use clarity::vm::{ClarityName, ClarityVersion, Value};
use http_types::headers::AUTHORIZATION;
use libsigner::v0::messages::SignerMessage as SignerMessageV0;
use libsigner::v1::messages::SignerMessage as SignerMessageV1;
use libsigner::{BlockProposal, SignerSession, StackerDBSession};
use rand::RngCore;
use stacks::burnchains::{MagicBytes, Txid};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::operations::{
    BlockstackOperationType, PreStxOp, StackStxOp, VoteForAggregateKeyOp,
};
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::chainstate::coordinator::OnChainRewardSetProvider;
use stacks::chainstate::nakamoto::coordinator::load_nakamoto_reward_set;
use stacks::chainstate::nakamoto::miner::NakamotoBlockBuilder;
use stacks::chainstate::nakamoto::test_signers::TestSigners;
use stacks::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader, NakamotoChainState};
use stacks::chainstate::stacks::address::{PoxAddress, StacksAddressExtensions};
use stacks::chainstate::stacks::boot::{
    MINERS_NAME, SIGNERS_VOTING_FUNCTION_NAME, SIGNERS_VOTING_NAME,
};
use stacks::chainstate::stacks::db::StacksChainState;
use stacks::chainstate::stacks::miner::{
    BlockBuilder, BlockLimitFunction, TransactionEvent, TransactionResult, TransactionSuccessEvent,
};
use stacks::chainstate::stacks::{
    SinglesigHashMode, SinglesigSpendingCondition, StacksTransaction, TenureChangeCause,
    TenureChangePayload, TransactionAnchorMode, TransactionAuth, TransactionPayload,
    TransactionPostConditionMode, TransactionPublicKeyEncoding, TransactionSpendingCondition,
    TransactionVersion, MAX_BLOCK_LEN,
};
use stacks::core::mempool::MAXIMUM_MEMPOOL_TX_CHAINING;
use stacks::core::{
    StacksEpoch, StacksEpochId, BLOCK_LIMIT_MAINNET_10, HELIUM_BLOCK_LIMIT_20,
    PEER_VERSION_EPOCH_1_0, PEER_VERSION_EPOCH_2_0, PEER_VERSION_EPOCH_2_05,
    PEER_VERSION_EPOCH_2_1, PEER_VERSION_EPOCH_2_2, PEER_VERSION_EPOCH_2_3, PEER_VERSION_EPOCH_2_4,
    PEER_VERSION_EPOCH_2_5, PEER_VERSION_EPOCH_3_0, PEER_VERSION_TESTNET,
};
use stacks::libstackerdb::SlotMetadata;
use stacks::net::api::callreadonly::CallReadOnlyRequestBody;
use stacks::net::api::get_tenures_fork_info::TenureForkingInfo;
use stacks::net::api::getstackers::GetStackersResponse;
use stacks::net::api::postblock_proposal::{
    BlockValidateReject, BlockValidateResponse, NakamotoBlockProposal, ValidateRejectCode,
};
use stacks::util::hash::hex_bytes;
use stacks::util_lib::boot::boot_code_id;
use stacks::util_lib::signed_structured_data::pox4::{
    make_pox_4_signer_key_signature, Pox4SignatureTopic,
};
use stacks_common::address::AddressHashMode;
use stacks_common::bitvec::BitVec;
use stacks_common::codec::StacksMessageCodec;
use stacks_common::consts::{CHAIN_ID_TESTNET, STACKS_EPOCH_MAX};
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksAddress, StacksPrivateKey, StacksPublicKey,
    TrieHash,
};
use stacks_common::types::StacksPublicKeyBuffer;
use stacks_common::util::hash::{to_hex, Hash160, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{MessageSignature, Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks_common::util::{get_epoch_time_secs, sleep_ms};
use stacks_signer::chainstate::{ProposalEvalConfig, SortitionsView};
use stacks_signer::signerdb::{BlockInfo, ExtraBlockInfo, SignerDb};
use wsts::net::Message;

use super::bitcoin_regtest::BitcoinCoreController;
use crate::config::{EventKeyType, EventObserverConfig, InitialBalance};
use crate::nakamoto_node::miner::TEST_BROADCAST_STALL;
use crate::neon::{Counters, RunLoopCounter};
use crate::operations::BurnchainOpSigner;
use crate::run_loop::boot_nakamoto;
use crate::tests::neon_integrations::{
    call_read_only, get_account, get_account_result, get_chain_info_result, get_neighbors,
    get_pox_info, next_block_and_wait, run_until_burnchain_height, submit_tx, test_observer,
    wait_for_runloop,
};
use crate::tests::{
    get_chain_info, make_contract_publish, make_contract_publish_versioned, make_stacks_transfer,
    to_addr,
};
use crate::{tests, BitcoinRegtestController, BurnchainController, Config, ConfigFile, Keychain};

pub const POX_4_DEFAULT_STACKER_BALANCE: u64 = 100_000_000_000_000;
pub const POX_4_DEFAULT_STACKER_STX_AMT: u128 = 99_000_000_000_000;

pub const NAKAMOTO_INTEGRATION_EPOCHS: LazyCell<[StacksEpoch; 9]> = LazyCell::new(|| {
    [
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: BLOCK_LIMIT_MAINNET_10,
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2,
            end_height: 3,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch22,
            start_height: 3,
            end_height: 4,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_2,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch23,
            start_height: 4,
            end_height: 5,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_3,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch24,
            start_height: 5,
            end_height: 201,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_4,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch25,
            start_height: 201,
            end_height: 231,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_2_5,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch30,
            start_height: 231,
            end_height: STACKS_EPOCH_MAX,
            block_limit: HELIUM_BLOCK_LIMIT_20,
            network_epoch: PEER_VERSION_EPOCH_3_0,
        },
    ]
});

pub static TEST_SIGNING: Mutex<Option<TestSigningChannel>> = Mutex::new(None);

pub struct TestSigningChannel {
    // pub recv: Option<Receiver<ThresholdSignature>>,
    pub recv: Option<Receiver<Vec<MessageSignature>>>,
    // pub send: Sender<ThresholdSignature>,
    pub send: Sender<Vec<MessageSignature>>,
}

impl TestSigningChannel {
    /// If the integration test has instantiated the singleton TEST_SIGNING channel,
    ///  wait for a signature from the blind-signer.
    /// Returns None if the singleton isn't instantiated and the miner should coordinate
    ///  a real signer set signature.
    /// Panics if the blind-signer times out.
    ///
    /// TODO: update to use signatures vec
    pub fn get_signature() -> Option<Vec<MessageSignature>> {
        let mut signer = TEST_SIGNING.lock().unwrap();
        let Some(sign_channels) = signer.as_mut() else {
            return None;
        };
        let recv = sign_channels.recv.take().unwrap();
        drop(signer); // drop signer so we don't hold the lock while receiving.
        let signatures = recv.recv_timeout(Duration::from_secs(30)).unwrap();
        let overwritten = TEST_SIGNING
            .lock()
            .unwrap()
            .as_mut()
            .unwrap()
            .recv
            .replace(recv);
        assert!(overwritten.is_none());
        Some(signatures)
    }

    /// Setup the TestSigningChannel as a singleton using TEST_SIGNING,
    ///  returning an owned Sender to the channel.
    pub fn instantiate() -> Sender<Vec<MessageSignature>> {
        let (send, recv) = channel();
        let existed = TEST_SIGNING.lock().unwrap().replace(Self {
            recv: Some(recv),
            send: send.clone(),
        });
        assert!(existed.is_none());
        send
    }
}

pub fn get_stacker_set(http_origin: &str, cycle: u64) -> GetStackersResponse {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/stacker_set/{cycle}");
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<serde_json::Value>()
        .unwrap();
    info!("Stacker set response: {res}");
    let res = serde_json::from_value(res).unwrap();
    res
}

pub fn get_stackerdb_slot_version(
    http_origin: &str,
    contract: &QualifiedContractIdentifier,
    slot_id: u64,
) -> Option<u32> {
    let client = reqwest::blocking::Client::new();
    let path = format!(
        "{http_origin}/v2/stackerdb/{}/{}",
        &contract.issuer, &contract.name
    );
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<Vec<SlotMetadata>>()
        .unwrap();
    debug!("StackerDB metadata response: {res:?}");
    res.iter().find_map(|slot| {
        if u64::from(slot.slot_id) == slot_id {
            Some(slot.slot_version)
        } else {
            None
        }
    })
}

pub fn add_initial_balances(
    conf: &mut Config,
    accounts: usize,
    amount: u64,
) -> Vec<StacksPrivateKey> {
    (0..accounts)
        .map(|i| {
            let privk = StacksPrivateKey::from_seed(&[5, 5, 5, i as u8]);
            let address = to_addr(&privk).into();

            conf.initial_balances
                .push(InitialBalance { address, amount });
            privk
        })
        .collect()
}

/// Spawn a blind signing thread. `signer` is the private key
///  of the individual signer who broadcasts the response to the StackerDB
pub fn blind_signer(
    conf: &Config,
    signers: &TestSigners,
    proposals_count: RunLoopCounter,
) -> JoinHandle<()> {
    blind_signer_multinode(signers, &[conf], vec![proposals_count])
}

/// Spawn a blind signing thread listening to potentially multiple stacks nodes.
/// `signer` is the private key  of the individual signer who broadcasts the response to the StackerDB.
/// The thread will check each node's proposal counter in order to wake up, but will only read from the first
///  node's StackerDB (it will read all of the StackerDBs to provide logging information, though).
pub fn blind_signer_multinode(
    signers: &TestSigners,
    configs: &[&Config],
    proposals_count: Vec<RunLoopCounter>,
) -> JoinHandle<()> {
    assert_eq!(
        configs.len(),
        proposals_count.len(),
        "Expect the same number of node configs as proposals counters"
    );
    let sender = TestSigningChannel::instantiate();
    let mut signed_blocks = HashSet::new();
    let configs: Vec<_> = configs.iter().map(|x| Clone::clone(*x)).collect();
    let signers = signers.clone();
    let mut last_count: Vec<_> = proposals_count
        .iter()
        .map(|x| x.load(Ordering::SeqCst))
        .collect();
    thread::Builder::new()
        .name("blind-signer".into())
        .spawn(move || loop {
            thread::sleep(Duration::from_millis(100));
            let cur_count: Vec<_> = proposals_count
                .iter()
                .map(|x| x.load(Ordering::SeqCst))
                .collect();
            if cur_count
                .iter()
                .zip(last_count.iter())
                .all(|(cur_count, last_count)| cur_count <= last_count)
            {
                continue;
            }
            thread::sleep(Duration::from_secs(2));
            info!("Checking for a block proposal to sign...");
            last_count = cur_count;
            let configs: Vec<&Config> = configs.iter().map(|x| x).collect();
            match read_and_sign_block_proposal(configs.as_slice(), &signers, &signed_blocks, &sender) {
                Ok(signed_block) => {
                    if signed_blocks.contains(&signed_block) {
                        info!("Already signed block, will sleep and try again"; "signer_sig_hash" => signed_block.to_hex());
                        thread::sleep(Duration::from_secs(5));
                        match read_and_sign_block_proposal(configs.as_slice(), &signers, &signed_blocks, &sender) {
                            Ok(signed_block) => {
                                if signed_blocks.contains(&signed_block) {
                                    info!("Already signed block, ignoring"; "signer_sig_hash" => signed_block.to_hex());
                                    continue;
                                }
                                info!("Signed block"; "signer_sig_hash" => signed_block.to_hex());
                                signed_blocks.insert(signed_block);
                            }
                            Err(e) => {
                                warn!("Error reading and signing block proposal: {e}");
                            }
                        };
                        continue;
                    }
                    info!("Signed block"; "signer_sig_hash" => signed_block.to_hex());
                    signed_blocks.insert(signed_block);
                }
                Err(e) => {
                    warn!("Error reading and signing block proposal: {e}");
                }
            }
        })
        .unwrap()
}

pub fn get_latest_block_proposal(
    conf: &Config,
    sortdb: &SortitionDB,
) -> Result<(NakamotoBlock, StacksPublicKey), String> {
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    let (stackerdb_conf, miner_info) =
        NakamotoChainState::make_miners_stackerdb_config(sortdb, &tip)
            .map_err(|e| e.to_string())?;
    let miner_ranges = stackerdb_conf.signer_ranges();
    let latest_miner = usize::from(miner_info.get_latest_winner_index());
    let miner_contract_id = boot_code_id(MINERS_NAME, false);
    let mut miners_stackerdb = StackerDBSession::new(&conf.node.rpc_bind, miner_contract_id);

    let mut proposed_blocks: Vec<_> = stackerdb_conf
        .signers
        .iter()
        .enumerate()
        .zip(miner_ranges)
        .filter_map(|((miner_ix, (miner_addr, _)), miner_slot_id)| {
            let proposed_block = {
                let message: SignerMessageV0 =
                    miners_stackerdb.get_latest(miner_slot_id.start).ok()??;
                let SignerMessageV0::BlockProposal(block_proposal) = message else {
                    panic!("Expected a signer message block proposal. Got {message:?}");
                };
                block_proposal.block
            };
            Some((proposed_block, miner_addr, miner_ix == latest_miner))
        })
        .collect();

    proposed_blocks.sort_by(|(block_a, _, is_latest_a), (block_b, _, is_latest_b)| {
        if block_a.header.chain_length > block_b.header.chain_length {
            return std::cmp::Ordering::Greater;
        } else if block_a.header.chain_length < block_b.header.chain_length {
            return std::cmp::Ordering::Less;
        }
        // the heights are tied, tie break with the latest miner
        if *is_latest_a {
            return std::cmp::Ordering::Greater;
        }
        if *is_latest_b {
            return std::cmp::Ordering::Less;
        }
        return std::cmp::Ordering::Equal;
    });

    for (b, _, is_latest) in proposed_blocks.iter() {
        info!("Consider block"; "signer_sighash" => %b.header.signer_signature_hash(), "is_latest_sortition" => is_latest, "chain_height" => b.header.chain_length);
    }

    let (proposed_block, miner_addr, _) = proposed_blocks.pop().unwrap();

    let pubkey = StacksPublicKey::recover_to_pubkey(
        proposed_block.header.miner_signature_hash().as_bytes(),
        &proposed_block.header.miner_signature,
    )
    .map_err(|e| e.to_string())?;
    let miner_signed_addr = StacksAddress::p2pkh(false, &pubkey);
    if miner_signed_addr.bytes != miner_addr.bytes {
        return Err(format!(
            "Invalid miner signature on proposal. Found {}, expected {}",
            miner_signed_addr.bytes, miner_addr.bytes
        ));
    }

    Ok((proposed_block, pubkey))
}

#[allow(dead_code)]
fn get_block_proposal_msg_v1(
    miners_stackerdb: &mut StackerDBSession,
    slot_id: u32,
) -> NakamotoBlock {
    let message: SignerMessageV1 = miners_stackerdb
        .get_latest(slot_id)
        .expect("Failed to get latest chunk from the miner slot ID")
        .expect("No chunk found");
    let SignerMessageV1::Packet(packet) = message else {
        panic!("Expected a signer message packet. Got {message:?}");
    };
    let Message::NonceRequest(nonce_request) = packet.msg else {
        panic!("Expected a nonce request. Got {:?}", packet.msg);
    };
    let block_proposal =
        BlockProposal::consensus_deserialize(&mut nonce_request.message.as_slice())
            .expect("Failed to deserialize block proposal");
    block_proposal.block
}

pub fn read_and_sign_block_proposal(
    configs: &[&Config],
    signers: &TestSigners,
    signed_blocks: &HashSet<Sha512Trunc256Sum>,
    channel: &Sender<Vec<MessageSignature>>,
) -> Result<Sha512Trunc256Sum, String> {
    let conf = configs.first().unwrap();
    let burnchain = conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (mut chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

    let mut proposed_block = get_latest_block_proposal(conf, &sortdb)?.0;
    let other_views_result: Result<Vec<_>, _> = configs
        .get(1..)
        .unwrap()
        .iter()
        .map(|other_conf| {
            get_latest_block_proposal(other_conf, &sortdb).map(|proposal| {
                (
                    proposal.0.header.signer_signature_hash(),
                    proposal.0.header.chain_length,
                )
            })
        })
        .collect();
    let proposed_block_hash = format!("0x{}", proposed_block.header.block_hash());
    let signer_sig_hash = proposed_block.header.signer_signature_hash();
    let other_views = other_views_result?;
    if !other_views.is_empty() {
        info!(
            "Fetched block proposals";
            "primary_latest_signer_sighash" => %signer_sig_hash,
            "primary_latest_block_height" => proposed_block.header.chain_length,
            "other_views" => ?other_views,
        );
    }

    if signed_blocks.contains(&signer_sig_hash) {
        // already signed off on this block, don't sign again.
        return Ok(signer_sig_hash);
    }

    let reward_set = load_nakamoto_reward_set(
        burnchain
            .pox_reward_cycle(tip.block_height.saturating_add(1))
            .unwrap(),
        &tip.sortition_id,
        &burnchain,
        &mut chainstate,
        &proposed_block.header.parent_block_id,
        &sortdb,
        &OnChainRewardSetProvider::new(),
    )
    .expect("Failed to query reward set")
    .expect("No reward set calculated")
    .0
    .known_selected_anchor_block_owned()
    .expect("Expected a reward set");

    info!(
        "Fetched proposed block from .miners StackerDB";
        "proposed_block_hash" => &proposed_block_hash,
        "signer_sig_hash" => &signer_sig_hash.to_hex(),
    );

    signers.sign_block_with_reward_set(&mut proposed_block, &reward_set);

    channel
        .send(proposed_block.header.signer_signature)
        .unwrap();
    return Ok(signer_sig_hash);
}

/// Return a working nakamoto-neon config and the miner's bitcoin address to fund
pub fn naka_neon_integration_conf(seed: Option<&[u8]>) -> (Config, StacksAddress) {
    let mut conf = super::new_test_conf();

    conf.burnchain.mode = "nakamoto-neon".into();

    // tests can override this, but these tests run with epoch 2.05 by default
    conf.burnchain.epochs = Some(NAKAMOTO_INTEGRATION_EPOCHS.to_vec());

    if let Some(seed) = seed {
        conf.node.seed = seed.to_vec();
    }

    // instantiate the keychain so we can fund the bitcoin op signer
    let keychain = Keychain::default(conf.node.seed.clone());

    let mining_key = Secp256k1PrivateKey::from_seed(&[1]);
    conf.miner.mining_key = Some(mining_key);

    conf.node.miner = true;
    conf.node.wait_time_for_microblocks = 500;
    conf.burnchain.burn_fee_cap = 20000;

    conf.burnchain.username = Some("neon-tester".into());
    conf.burnchain.password = Some("neon-tester-pass".into());
    conf.burnchain.peer_host = "127.0.0.1".into();
    conf.burnchain.local_mining_public_key =
        Some(keychain.generate_op_signer().get_public_key().to_hex());
    conf.burnchain.commit_anchor_block_within = 0;
    conf.node.add_signers_stackerdbs(false);
    conf.node.add_miner_stackerdb(false);

    // test to make sure config file parsing is correct
    let mut cfile = ConfigFile::xenon();
    cfile.node.as_mut().map(|node| node.bootstrap_node.take());

    if let Some(burnchain) = cfile.burnchain.as_mut() {
        burnchain.peer_host = Some("127.0.0.1".to_string());
    }

    conf.burnchain.magic_bytes = MagicBytes::from(['T' as u8, '3' as u8].as_ref());
    conf.burnchain.poll_time_secs = 1;
    conf.node.pox_sync_sample_secs = 0;

    conf.miner.first_attempt_time_ms = i64::max_value() as u64;
    conf.miner.subsequent_attempt_time_ms = i64::max_value() as u64;

    // if there's just one node, then this must be true for tests to pass
    conf.miner.wait_for_block_download = false;

    conf.node.mine_microblocks = false;
    conf.miner.microblock_attempt_time_ms = 10;
    conf.node.microblock_frequency = 0;
    conf.node.wait_time_for_blocks = 200;

    let miner_account = keychain.origin_address(conf.is_mainnet()).unwrap();

    conf.burnchain.pox_prepare_length = Some(5);
    conf.burnchain.pox_reward_length = Some(20);

    conf.connection_options.inv_sync_interval = 1;

    (conf, miner_account)
}

pub fn next_block_and<F>(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    mut check: F,
) -> Result<(), String>
where
    F: FnMut() -> Result<bool, String>,
{
    eprintln!("Issuing bitcoin block");
    btc_controller.build_next_block(1);
    let start = Instant::now();
    while !check()? {
        if start.elapsed() > Duration::from_secs(timeout_secs) {
            error!("Timed out waiting for block to process, trying to continue test");
            return Err("Timed out".into());
        }
        thread::sleep(Duration::from_millis(100));
    }
    Ok(())
}

pub fn wait_for<F>(timeout_secs: u64, mut check: F) -> Result<(), String>
where
    F: FnMut() -> Result<bool, String>,
{
    let start = Instant::now();
    while !check()? {
        if start.elapsed() > Duration::from_secs(timeout_secs) {
            error!("Timed out waiting for check to process");
            return Err("Timed out".into());
        }
        thread::sleep(Duration::from_millis(100));
    }
    Ok(())
}

/// Mine a bitcoin block, and wait until:
///  (1) a new block has been processed by the coordinator
pub fn next_block_and_process_new_stacks_block(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    coord_channels: &Arc<Mutex<CoordinatorChannels>>,
) -> Result<(), String> {
    let blocks_processed_before = coord_channels
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    next_block_and(btc_controller, timeout_secs, || {
        let blocks_processed = coord_channels
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            return Ok(true);
        }
        Ok(false)
    })
}

/// Mine a bitcoin block, and wait until:
///  (1) a new block has been processed by the coordinator
///  (2) 2 block commits have been issued ** or ** more than 10 seconds have
///      passed since (1) occurred
pub fn next_block_and_mine_commit(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    coord_channels: &Arc<Mutex<CoordinatorChannels>>,
    commits_submitted: &Arc<AtomicU64>,
) -> Result<(), String> {
    next_block_and_wait_for_commits(
        btc_controller,
        timeout_secs,
        &[coord_channels],
        &[commits_submitted],
    )
}

/// Mine a bitcoin block, and wait until:
///  (1) a new block has been processed by the coordinator
///  (2) 2 block commits have been issued ** or ** more than 10 seconds have
///      passed since (1) occurred
/// This waits for this check to pass on *all* supplied channels
pub fn next_block_and_wait_for_commits(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    coord_channels: &[&Arc<Mutex<CoordinatorChannels>>],
    commits_submitted: &[&Arc<AtomicU64>],
) -> Result<(), String> {
    let commits_submitted: Vec<_> = commits_submitted.iter().cloned().collect();
    let blocks_processed_before: Vec<_> = coord_channels
        .iter()
        .map(|x| {
            x.lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed()
        })
        .collect();
    let commits_before: Vec<_> = commits_submitted
        .iter()
        .map(|x| x.load(Ordering::SeqCst))
        .collect();

    let mut block_processed_time: Vec<Option<Instant>> =
        (0..commits_before.len()).map(|_| None).collect();
    let mut commit_sent_time: Vec<Option<Instant>> =
        (0..commits_before.len()).map(|_| None).collect();
    next_block_and(btc_controller, timeout_secs, || {
        for i in 0..commits_submitted.len() {
            let commits_sent = commits_submitted[i].load(Ordering::SeqCst);
            let blocks_processed = coord_channels[i]
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            let now = Instant::now();
            if blocks_processed > blocks_processed_before[i] && block_processed_time[i].is_none() {
                block_processed_time[i].replace(now);
            }
            if commits_sent > commits_before[i] && commit_sent_time[i].is_none() {
                commit_sent_time[i].replace(now);
            }
        }

        for i in 0..commits_submitted.len() {
            let blocks_processed = coord_channels[i]
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            let commits_sent = commits_submitted[i].load(Ordering::SeqCst);

            if blocks_processed > blocks_processed_before[i] {
                let block_processed_time = block_processed_time[i]
                    .as_ref()
                    .ok_or("TEST-ERROR: Processed time wasn't set")?;
                if commits_sent <= commits_before[i] {
                    return Ok(false);
                }
                let commit_sent_time = commit_sent_time[i]
                    .as_ref()
                    .ok_or("TEST-ERROR: Processed time wasn't set")?;
                // try to ensure the commit was sent after the block was processed
                if commit_sent_time > block_processed_time {
                    continue;
                }
                // if two commits have been sent, one of them must have been after
                if commits_sent >= commits_before[i] + 2 {
                    continue;
                }
                // otherwise, just timeout if the commit was sent and its been long enough
                //  for a new commit pass to have occurred
                if block_processed_time.elapsed() > Duration::from_secs(10) {
                    continue;
                }
                return Ok(false);
            } else {
                return Ok(false);
            }
        }
        Ok(true)
    })
}

pub fn setup_stacker(naka_conf: &mut Config) -> Secp256k1PrivateKey {
    let stacker_sk = Secp256k1PrivateKey::new();
    let stacker_address = tests::to_addr(&stacker_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(stacker_address.clone()).to_string(),
        POX_4_DEFAULT_STACKER_BALANCE,
    );
    stacker_sk
}

///
/// * `stacker_sks` - must be a private key for sending a large `stack-stx` transaction in order
///   for pox-4 to activate
pub fn boot_to_epoch_3(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    stacker_sks: &[StacksPrivateKey],
    signer_sks: &[StacksPrivateKey],
    self_signing: &mut Option<&mut TestSigners>,
    btc_regtest_controller: &mut BitcoinRegtestController,
) {
    assert_eq!(stacker_sks.len(), signer_sks.len());

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30).unwrap()];
    let current_height = btc_regtest_controller.get_headers_height();
    info!(
        "Chain bootstrapped to bitcoin block {current_height:?}, starting Epoch 2x miner";
        "Epoch 3.0 Boundary" => (epoch_3.start_height - 1),
    );
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    next_block_and_wait(btc_regtest_controller, &blocks_processed);
    next_block_and_wait(btc_regtest_controller, &blocks_processed);
    // first mined stacks block
    next_block_and_wait(btc_regtest_controller, &blocks_processed);

    let start_time = Instant::now();
    loop {
        if start_time.elapsed() > Duration::from_secs(20) {
            panic!("Timed out waiting for the stacks height to increment")
        }
        let stacks_height = get_chain_info(&naka_conf).stacks_tip_height;
        if stacks_height >= 1 {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }
    // stack enough to activate pox-4

    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    for (stacker_sk, signer_sk) in stacker_sks.iter().zip(signer_sks.iter()) {
        let pox_addr = PoxAddress::from_legacy(
            AddressHashMode::SerializeP2PKH,
            tests::to_addr(&stacker_sk).bytes,
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            &signer_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            CHAIN_ID_TESTNET,
            12_u128,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = StacksPublicKey::from_private(signer_sk);

        let stacking_tx = tests::make_contract_call(
            &stacker_sk,
            0,
            1000,
            &StacksAddress::burn_address(false),
            "pox-4",
            "stack-stx",
            &[
                clarity::vm::Value::UInt(POX_4_DEFAULT_STACKER_STX_AMT),
                pox_addr_tuple.clone(),
                clarity::vm::Value::UInt(block_height as u128),
                clarity::vm::Value::UInt(12),
                clarity::vm::Value::some(clarity::vm::Value::buff_from(signature).unwrap())
                    .unwrap(),
                clarity::vm::Value::buff_from(signer_pk.to_bytes_compressed()).unwrap(),
                clarity::vm::Value::UInt(u128::MAX),
                clarity::vm::Value::UInt(1),
            ],
        );
        submit_tx(&http_origin, &stacking_tx);
    }

    // Update TestSigner with `signer_sks` if self-signing
    if let Some(ref mut signers) = self_signing {
        signers.signer_keys = signer_sks.to_vec();
    }

    let prepare_phase_start = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        );

    // Run until the prepare phase
    run_until_burnchain_height(
        btc_regtest_controller,
        &blocks_processed,
        prepare_phase_start,
        &naka_conf,
    );

    // We need to vote on the aggregate public key if this test is self signing
    if let Some(signers) = self_signing {
        // Get the aggregate key
        let aggregate_key = signers.clone().generate_aggregate_key(reward_cycle + 1);
        let aggregate_public_key =
            clarity::vm::Value::buff_from(aggregate_key.compress().data.to_vec())
                .expect("Failed to serialize aggregate public key");
        let signer_sks_unique: HashMap<_, _> = signer_sks.iter().map(|x| (x.to_hex(), x)).collect();
        let signer_set = get_stacker_set(&http_origin, reward_cycle + 1);
        // Vote on the aggregate public key
        for signer_sk in signer_sks_unique.values() {
            let signer_index =
                get_signer_index(&signer_set, &Secp256k1PublicKey::from_private(signer_sk))
                    .unwrap();
            let voting_tx = tests::make_contract_call(
                signer_sk,
                0,
                300,
                &StacksAddress::burn_address(false),
                SIGNERS_VOTING_NAME,
                SIGNERS_VOTING_FUNCTION_NAME,
                &[
                    clarity::vm::Value::UInt(u128::try_from(signer_index).unwrap()),
                    aggregate_public_key.clone(),
                    clarity::vm::Value::UInt(0),
                    clarity::vm::Value::UInt(reward_cycle as u128 + 1),
                ],
            );
            submit_tx(&http_origin, &voting_tx);
        }
    }

    run_until_burnchain_height(
        btc_regtest_controller,
        &blocks_processed,
        epoch_3.start_height - 1,
        &naka_conf,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, Epoch2x miner should stop");
}

fn get_signer_index(
    stacker_set: &GetStackersResponse,
    signer_key: &Secp256k1PublicKey,
) -> Result<usize, String> {
    let Some(ref signer_set) = stacker_set.stacker_set.signers else {
        return Err("Empty signer set for reward cycle".into());
    };
    let signer_key_bytes = signer_key.to_bytes_compressed();
    signer_set
        .iter()
        .enumerate()
        .find_map(|(ix, entry)| {
            if entry.signing_key.as_slice() == signer_key_bytes.as_slice() {
                Some(ix)
            } else {
                None
            }
        })
        .ok_or_else(|| {
            format!(
                "Signing key not found. {} not found.",
                to_hex(&signer_key_bytes)
            )
        })
}

/// Use the read-only API to get the aggregate key for a given reward cycle
pub fn get_key_for_cycle(
    reward_cycle: u64,
    is_mainnet: bool,
    http_origin: &str,
) -> Result<Option<Vec<u8>>, String> {
    let client = reqwest::blocking::Client::new();
    let boot_address = StacksAddress::burn_address(is_mainnet);
    let path = format!("http://{http_origin}/v2/contracts/call-read/{boot_address}/signers-voting/get-approved-aggregate-key");
    let body = CallReadOnlyRequestBody {
        sender: boot_address.to_string(),
        sponsor: None,
        arguments: vec![clarity::vm::Value::UInt(reward_cycle as u128)
            .serialize_to_hex()
            .map_err(|_| "Failed to serialize reward cycle")?],
    };
    let res = client
        .post(&path)
        .json(&body)
        .send()
        .map_err(|_| "Failed to send request")?
        .json::<serde_json::Value>()
        .map_err(|_| "Failed to extract json Value")?;
    let result_value = clarity::vm::Value::try_deserialize_hex_untyped(
        &res.get("result")
            .ok_or("No result in response")?
            .as_str()
            .ok_or("Result is not a string")?[2..],
    )
    .map_err(|_| "Failed to deserialize Clarity value")?;

    let buff_opt = result_value
        .expect_optional()
        .expect("Expected optional type");

    match buff_opt {
        Some(buff_val) => {
            let buff = buff_val
                .expect_buff(33)
                .map_err(|_| "Failed to get buffer value")?;
            Ok(Some(buff))
        }
        None => Ok(None),
    }
}

/// Use the read-only to check if the aggregate key is set for a given reward cycle
pub fn is_key_set_for_cycle(
    reward_cycle: u64,
    is_mainnet: bool,
    http_origin: &str,
) -> Result<bool, String> {
    let key = get_key_for_cycle(reward_cycle, is_mainnet, &http_origin)?;
    Ok(key.is_some())
}

fn signer_vote_if_needed(
    btc_regtest_controller: &BitcoinRegtestController,
    naka_conf: &Config,
    signer_sks: &[StacksPrivateKey], // TODO: Is there some way to get this from the TestSigners?
    signers: &TestSigners,
) {
    // When we reach the next prepare phase, submit new voting transactions
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    let prepare_phase_start = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        );

    if block_height >= prepare_phase_start {
        // If the key is already set, do nothing.
        if is_key_set_for_cycle(
            reward_cycle + 1,
            naka_conf.is_mainnet(),
            &naka_conf.node.rpc_bind,
        )
        .unwrap_or(false)
        {
            return;
        }

        // If we are self-signing, then we need to vote on the aggregate public key
        let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

        // Get the aggregate key
        let aggregate_key = signers.clone().generate_aggregate_key(reward_cycle + 1);
        let aggregate_public_key =
            clarity::vm::Value::buff_from(aggregate_key.compress().data.to_vec())
                .expect("Failed to serialize aggregate public key");

        for (i, signer_sk) in signer_sks.iter().enumerate() {
            let signer_nonce = get_account(&http_origin, &to_addr(signer_sk)).nonce;

            // Vote on the aggregate public key
            let voting_tx = tests::make_contract_call(
                &signer_sk,
                signer_nonce,
                300,
                &StacksAddress::burn_address(false),
                SIGNERS_VOTING_NAME,
                "vote-for-aggregate-public-key",
                &[
                    clarity::vm::Value::UInt(i as u128),
                    aggregate_public_key.clone(),
                    clarity::vm::Value::UInt(0),
                    clarity::vm::Value::UInt(reward_cycle as u128 + 1),
                ],
            );
            submit_tx(&http_origin, &voting_tx);
        }
    }
}

pub fn setup_epoch_3_reward_set(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    stacker_sks: &[StacksPrivateKey],
    signer_sks: &[StacksPrivateKey],
    btc_regtest_controller: &mut BitcoinRegtestController,
    num_stacking_cycles: Option<u64>,
) {
    assert_eq!(stacker_sks.len(), signer_sks.len());

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30).unwrap()];
    let reward_cycle_len = naka_conf.get_burnchain().pox_constants.reward_cycle_length as u64;
    let prepare_phase_len = naka_conf.get_burnchain().pox_constants.prepare_length as u64;

    let epoch_3_start_height = epoch_3.start_height;
    assert!(
        epoch_3_start_height > 0,
        "Epoch 3.0 start height must be greater than 0"
    );
    let epoch_3_reward_cycle_boundary =
        epoch_3_start_height.saturating_sub(epoch_3_start_height % reward_cycle_len);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    next_block_and_wait(btc_regtest_controller, &blocks_processed);
    next_block_and_wait(btc_regtest_controller, &blocks_processed);
    // first mined stacks block
    next_block_and_wait(btc_regtest_controller, &blocks_processed);

    // stack enough to activate pox-4
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    let lock_period: u128 = num_stacking_cycles.unwrap_or(12_u64).into();
    info!("Test Cycle Info";
          "prepare_phase_len" => {prepare_phase_len},
          "reward_cycle_len" => {reward_cycle_len},
          "block_height" => {block_height},
          "reward_cycle" => {reward_cycle},
          "epoch_3_reward_cycle_boundary" => {epoch_3_reward_cycle_boundary},
          "epoch_3_start_height" => {epoch_3_start_height},
    );
    for (stacker_sk, signer_sk) in stacker_sks.iter().zip(signer_sks.iter()) {
        let pox_addr = PoxAddress::from_legacy(
            AddressHashMode::SerializeP2PKH,
            tests::to_addr(&stacker_sk).bytes,
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            &signer_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            CHAIN_ID_TESTNET,
            lock_period,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = StacksPublicKey::from_private(signer_sk);
        let stacking_tx = tests::make_contract_call(
            &stacker_sk,
            0,
            1000,
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
}

///
/// * `stacker_sks` - must be a private key for sending a large `stack-stx` transaction in order
///   for pox-4 to activate
/// * `signer_pks` - must be the same size as `stacker_sks`
pub fn boot_to_epoch_3_reward_set_calculation_boundary(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    stacker_sks: &[StacksPrivateKey],
    signer_sks: &[StacksPrivateKey],
    btc_regtest_controller: &mut BitcoinRegtestController,
    num_stacking_cycles: Option<u64>,
) {
    setup_epoch_3_reward_set(
        naka_conf,
        blocks_processed,
        stacker_sks,
        signer_sks,
        btc_regtest_controller,
        num_stacking_cycles,
    );

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30).unwrap()];
    let reward_cycle_len = naka_conf.get_burnchain().pox_constants.reward_cycle_length as u64;
    let prepare_phase_len = naka_conf.get_burnchain().pox_constants.prepare_length as u64;

    let epoch_3_start_height = epoch_3.start_height;
    assert!(
        epoch_3_start_height > 0,
        "Epoch 3.0 start height must be greater than 0"
    );
    let epoch_3_reward_cycle_boundary =
        epoch_3_start_height.saturating_sub(epoch_3_start_height % reward_cycle_len);
    let epoch_3_reward_set_calculation_boundary = epoch_3_reward_cycle_boundary
        .saturating_sub(prepare_phase_len)
        .saturating_add(1);

    run_until_burnchain_height(
        btc_regtest_controller,
        &blocks_processed,
        epoch_3_reward_set_calculation_boundary,
        &naka_conf,
    );

    info!("Bootstrapped to Epoch 3.0 reward set calculation boundary height: {epoch_3_reward_set_calculation_boundary}.");
}

///
/// * `stacker_sks` - must be a private key for sending a large `stack-stx` transaction in order
///   for pox-4 to activate
/// * `signer_pks` - must be the same size as `stacker_sks`
pub fn boot_to_epoch_25(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    btc_regtest_controller: &mut BitcoinRegtestController,
) {
    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_25 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch25).unwrap()];
    let reward_cycle_len = naka_conf.get_burnchain().pox_constants.reward_cycle_length as u64;
    let prepare_phase_len = naka_conf.get_burnchain().pox_constants.prepare_length as u64;

    let epoch_25_start_height = epoch_25.start_height;
    assert!(
        epoch_25_start_height > 0,
        "Epoch 2.5 start height must be greater than 0"
    );
    // stack enough to activate pox-4
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    debug!("Test Cycle Info";
     "prepare_phase_len" => {prepare_phase_len},
     "reward_cycle_len" => {reward_cycle_len},
     "block_height" => {block_height},
     "reward_cycle" => {reward_cycle},
     "epoch_25_start_height" => {epoch_25_start_height},
    );
    run_until_burnchain_height(
        btc_regtest_controller,
        &blocks_processed,
        epoch_25_start_height,
        &naka_conf,
    );
    info!("Bootstrapped to Epoch 2.5: {epoch_25_start_height}.");
}

///
/// * `stacker_sks` - must be a private key for sending a large `stack-stx` transaction in order
///   for pox-4 to activate
/// * `signer_pks` - must be the same size as `stacker_sks`
pub fn boot_to_epoch_3_reward_set(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    stacker_sks: &[StacksPrivateKey],
    signer_sks: &[StacksPrivateKey],
    btc_regtest_controller: &mut BitcoinRegtestController,
    num_stacking_cycles: Option<u64>,
) {
    boot_to_epoch_3_reward_set_calculation_boundary(
        naka_conf,
        blocks_processed,
        stacker_sks,
        signer_sks,
        btc_regtest_controller,
        num_stacking_cycles,
    );
    next_block_and_wait(btc_regtest_controller, &blocks_processed);
    info!(
        "Bootstrapped to Epoch 3.0 reward set calculation height: {}",
        get_chain_info(naka_conf).burn_block_height
    );
}

/// Wait for a block commit, without producing a block
fn wait_for_first_naka_block_commit(timeout_secs: u64, naka_commits_submitted: &Arc<AtomicU64>) {
    let start = Instant::now();
    while naka_commits_submitted.load(Ordering::SeqCst) < 1 {
        if start.elapsed() > Duration::from_secs(timeout_secs) {
            error!("Timed out waiting for block commit");
            panic!();
        }
        thread::sleep(Duration::from_millis(100));
    }
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes three assertions:
///  * 30 blocks are mined after 3.0 starts. This is enough to mine across 2 reward cycles
///  * A transaction submitted to the mempool in 3.0 will be mined in 3.0
///  * The final chain tip is a nakamoto block
fn simple_neon_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = format!("{}:{}", "127.0.0.1", 6000);
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);
    let sender_sk = Secp256k1PrivateKey::new();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        send_amt * 2 + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (mut chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    // query for prometheus metrics
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
        assert!(res.contains(&expected_result));
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 15 nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();

        signer_vote_if_needed(
            &btc_regtest_controller,
            &naka_conf,
            &[sender_signer_sk],
            &signers,
        );
    }

    // Submit a TX
    let transfer_tx = make_stacks_transfer(&sender_sk, 0, send_fee, &recipient, send_amt);
    let transfer_tx_hex = format!("0x{}", to_hex(&transfer_tx));

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let mut mempool = naka_conf
        .connect_mempool_db()
        .expect("Database failure opening mempool");

    mempool
        .submit_raw(
            &mut chainstate,
            &sortdb,
            &tip.consensus_hash,
            &tip.anchored_header.block_hash(),
            transfer_tx.clone(),
            &ExecutionCost::max_value(),
            &StacksEpochId::Epoch30,
        )
        .unwrap();

    // Mine 15 more nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();

        signer_vote_if_needed(
            &btc_regtest_controller,
            &naka_conf,
            &[sender_signer_sk],
            &signers,
        );
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    // assert that the transfer tx was observed
    let transfer_tx_included = test_observer::get_blocks()
        .into_iter()
        .find(|block_json| {
            block_json["transactions"]
                .as_array()
                .unwrap()
                .iter()
                .find(|tx_json| tx_json["raw_tx"].as_str() == Some(&transfer_tx_hex))
                .is_some()
        })
        .is_some();

    assert!(
        transfer_tx_included,
        "Nakamoto node failed to include the transfer tx"
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert!(tip.stacks_block_height >= block_height_pre_3_0 + 30);

    // Check that we aren't missing burn blocks
    let bhh = u64::from(tip.burn_header_height);
    test_observer::contains_burn_block_range(220..=bhh).unwrap();

    // make sure prometheus returns an updated height
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        let expected_result = format!("stacks_node_stacks_tip_height {}", tip.stacks_block_height);
        assert!(res.contains(&expected_result));
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes three assertions:
///  * 5 tenures are mined after 3.0 starts
///  * Each tenure has 10 blocks (the coinbase block and 9 interim blocks)
fn mine_multiple_per_tenure_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        debug!("Mining tenure {}", tenure_ix);
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_tip_height = 0;

        // mine the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            // submit a tx so that the miner will mine an extra block
            let sender_nonce = tenure_ix * inter_blocks_per_tenure + interim_block_ix;
            let transfer_tx =
                make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
            submit_tx(&http_origin, &transfer_tx);

            loop {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                if blocks_processed > blocks_processed_before {
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }

            let info = get_chain_info_result(&naka_conf).unwrap();
            assert_ne!(info.stacks_tip, last_tip);
            assert_ne!(info.stacks_tip_height, last_tip_height);

            last_tip = info.stacks_tip;
            last_tip_height = info.stacks_tip_height;
        }

        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert_eq!(
        tip.stacks_block_height,
        block_height_pre_3_0 + ((inter_blocks_per_tenure + 1) * tenure_count),
        "Should have mined (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up two nakamoto nodes, both configured to mine.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes three assertions:
///  * 15 tenures are mined after 3.0 starts
///  * Each tenure has 6 blocks (the coinbase block and 5 interim blocks)
///  * Both nodes see the same chainstate at the end of the test
fn multiple_miners() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.node.local_peer_seed = vec![1, 1, 1, 1];
    naka_conf.miner.mining_key = Some(Secp256k1PrivateKey::from_seed(&[1]));

    let node_2_rpc = 51026;
    let node_2_p2p = 51025;
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 15;
    let inter_blocks_per_tenure = 6;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    let mut conf_node_2 = naka_conf.clone();
    let localhost = "127.0.0.1";
    conf_node_2.node.rpc_bind = format!("{}:{}", localhost, node_2_rpc);
    conf_node_2.node.p2p_bind = format!("{}:{}", localhost, node_2_p2p);
    conf_node_2.node.data_url = format!("http://{}:{}", localhost, node_2_rpc);
    conf_node_2.node.p2p_address = format!("{}:{}", localhost, node_2_p2p);
    conf_node_2.node.seed = vec![2, 2, 2, 2];
    conf_node_2.burnchain.local_mining_public_key = Some(
        Keychain::default(conf_node_2.node.seed.clone())
            .get_pub_key()
            .to_hex(),
    );
    conf_node_2.node.local_peer_seed = vec![2, 2, 2, 2];
    conf_node_2.node.miner = true;
    conf_node_2.miner.mining_key = Some(Secp256k1PrivateKey::from_seed(&[2]));
    conf_node_2.events_observers.clear();

    let node_1_sk = Secp256k1PrivateKey::from_seed(&naka_conf.node.local_peer_seed);
    let node_1_pk = StacksPublicKey::from_private(&node_1_sk);

    conf_node_2.node.working_dir = format!("{}-{}", conf_node_2.node.working_dir, "1");

    conf_node_2.node.set_bootstrap_nodes(
        format!("{}@{}", &node_1_pk.to_hex(), naka_conf.node.p2p_bind),
        naka_conf.burnchain.chain_id,
        naka_conf.burnchain.peer_version,
    );

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain_to_pks(
        201,
        &[
            Secp256k1PublicKey::from_hex(
                naka_conf
                    .burnchain
                    .local_mining_public_key
                    .as_ref()
                    .unwrap(),
            )
            .unwrap(),
            Secp256k1PublicKey::from_hex(
                conf_node_2
                    .burnchain
                    .local_mining_public_key
                    .as_ref()
                    .unwrap(),
            )
            .unwrap(),
        ],
    );

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let mut run_loop_2 = boot_nakamoto::BootRunLoop::new(conf_node_2.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let run_loop_2_stopper = run_loop.get_termination_switch();
    let Counters {
        naka_proposed_blocks: proposals_submitted_2,
        ..
    } = run_loop_2.counters();

    let coord_channel = run_loop.coordinator_channels();
    let coord_channel_2 = run_loop_2.coordinator_channels();

    let _run_loop_2_thread = thread::Builder::new()
        .name("run_loop_2".into())
        .spawn(move || run_loop_2.start(None, 0))
        .unwrap();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer_multinode(
        &signers,
        &[&naka_conf, &conf_node_2],
        vec![proposals_submitted, proposals_submitted_2],
    );

    info!("Neighbors 1"; "neighbors" => ?get_neighbors(&naka_conf));
    info!("Neighbors 2"; "neighbors" => ?get_neighbors(&conf_node_2));

    // Wait one block to confirm the VRF register, wait until a block commit is submitted
    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {}", tenure_ix);
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_tip_height = 0;

        // mine the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            // submit a tx so that the miner will mine an extra block
            let sender_nonce = tenure_ix * inter_blocks_per_tenure + interim_block_ix;
            let transfer_tx =
                make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
            submit_tx(&http_origin, &transfer_tx);

            wait_for(20, || {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                Ok(blocks_processed > blocks_processed_before)
            })
            .unwrap();

            let info = get_chain_info_result(&naka_conf).unwrap();
            assert_ne!(info.stacks_tip, last_tip);
            assert_ne!(info.stacks_tip_height, last_tip_height);

            last_tip = info.stacks_tip;
            last_tip_height = info.stacks_tip_height;
        }

        wait_for(20, || {
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap();
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    let peer_1_height = get_chain_info(&naka_conf).stacks_tip_height;
    let peer_2_height = get_chain_info(&conf_node_2).stacks_tip_height;
    info!("Peer height information"; "peer_1" => peer_1_height, "peer_2" => peer_2_height);
    assert_eq!(peer_1_height, peer_2_height);

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert_eq!(
        tip.stacks_block_height,
        block_height_pre_3_0 + ((inter_blocks_per_tenure + 1) * tenure_count),
        "Should have mined (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    coord_channel_2
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);
    run_loop_2_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
fn correct_burn_outs() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.burnchain.pox_reward_length = Some(10);
    naka_conf.burnchain.pox_prepare_length = Some(3);

    {
        let epochs = naka_conf.burnchain.epochs.as_mut().unwrap();
        let epoch_24_ix = StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch24).unwrap();
        let epoch_25_ix = StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch25).unwrap();
        let epoch_30_ix = StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30).unwrap();
        epochs[epoch_24_ix].end_height = 208;
        epochs[epoch_25_ix].start_height = 208;
        epochs[epoch_25_ix].end_height = 225;
        epochs[epoch_30_ix].start_height = 225;
    }

    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);
    naka_conf.initial_balances.clear();
    let accounts: Vec<_> = (0..8)
        .map(|ix| {
            let sk = Secp256k1PrivateKey::from_seed(&[ix, ix, ix, ix]);
            let address = PrincipalData::from(tests::to_addr(&sk));
            (sk, address)
        })
        .collect();
    for (_, ref addr) in accounts.iter() {
        naka_conf.add_initial_balance(addr.to_string(), 10000000000000000);
    }

    let stacker_accounts = accounts[0..3].to_vec();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );

    let signers = TestSigners::new(vec![sender_signer_sk]);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30).unwrap()];
    let epoch_25 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch25).unwrap()];
    let current_height = btc_regtest_controller.get_headers_height();
    info!(
        "Chain bootstrapped to bitcoin block {current_height:?}, starting Epoch 2x miner";
        "Epoch 3.0 Boundary" => (epoch_3.start_height - 1),
    );

    run_until_burnchain_height(
        &mut btc_regtest_controller,
        &blocks_processed,
        epoch_25.start_height + 1,
        &naka_conf,
    );

    info!("Chain bootstrapped to Epoch 2.5, submitting stacker transaction");

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let stacker_accounts_copy = stacker_accounts.clone();
    let _stacker_thread = thread::Builder::new()
        .name("stacker".into())
        .spawn(move || loop {
            thread::sleep(Duration::from_secs(2));
            debug!("Checking for stacker-necessity");
            let Some(pox_info) = get_pox_info(&http_origin) else {
                warn!("Failed to get pox_info, waiting.");
                continue;
            };
            if !pox_info.contract_id.ends_with(".pox-4") {
                continue;
            }
            let next_cycle_stx = pox_info.next_cycle.stacked_ustx;
            let min_stx = pox_info.next_cycle.min_threshold_ustx;
            let min_stx = (min_stx * 3) / 2;
            if next_cycle_stx >= min_stx {
                debug!(
                    "Next cycle has enough stacked, skipping stacking";
                    "stacked" => next_cycle_stx,
                    "min" => min_stx,
                );
                continue;
            }
            let Some(account) = stacker_accounts_copy.iter().find_map(|(sk, addr)| {
                let account = get_account(&http_origin, &addr);
                if account.locked == 0 {
                    Some((sk, addr, account))
                } else {
                    None
                }
            }) else {
                continue;
            };

            let pox_addr = PoxAddress::from_legacy(
                AddressHashMode::SerializeP2PKH,
                tests::to_addr(&account.0).bytes,
            );
            let pox_addr_tuple: clarity::vm::Value =
                pox_addr.clone().as_clarity_tuple().unwrap().into();
            let pk_bytes = StacksPublicKey::from_private(&sender_signer_sk).to_bytes_compressed();

            let reward_cycle = pox_info.current_cycle.id;
            let signature = make_pox_4_signer_key_signature(
                &pox_addr,
                &sender_signer_sk,
                reward_cycle.into(),
                &Pox4SignatureTopic::StackStx,
                CHAIN_ID_TESTNET,
                1_u128,
                u128::MAX,
                1,
            )
            .unwrap()
            .to_rsv();

            let stacking_tx = tests::make_contract_call(
                &account.0,
                account.2.nonce,
                1000,
                &StacksAddress::burn_address(false),
                "pox-4",
                "stack-stx",
                &[
                    clarity::vm::Value::UInt(min_stx.into()),
                    pox_addr_tuple,
                    clarity::vm::Value::UInt(pox_info.current_burnchain_block_height.into()),
                    clarity::vm::Value::UInt(1),
                    clarity::vm::Value::some(clarity::vm::Value::buff_from(signature).unwrap())
                        .unwrap(),
                    clarity::vm::Value::buff_from(pk_bytes).unwrap(),
                    clarity::vm::Value::UInt(u128::MAX),
                    clarity::vm::Value::UInt(1),
                ],
            );
            let txid = submit_tx(&http_origin, &stacking_tx);
            info!("Submitted stacking transaction: {txid}");
            thread::sleep(Duration::from_secs(10));
        })
        .unwrap();

    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    let prepare_phase_start = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        );

    // Run until the prepare phase
    run_until_burnchain_height(
        &mut btc_regtest_controller,
        &blocks_processed,
        prepare_phase_start,
        &naka_conf,
    );

    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    run_until_burnchain_height(
        &mut btc_regtest_controller,
        &blocks_processed,
        epoch_3.start_height - 1,
        &naka_conf,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, Epoch2x miner should stop");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    // we should already be able to query the stacker set via RPC
    let burnchain = naka_conf.get_burnchain();
    let first_epoch_3_cycle = burnchain
        .block_height_to_reward_cycle(epoch_3.start_height)
        .unwrap();

    info!("first_epoch_3_cycle: {:?}", first_epoch_3_cycle);

    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let stacker_response = get_stacker_set(&http_origin, first_epoch_3_cycle);
    assert!(stacker_response.stacker_set.signers.is_some());
    assert_eq!(
        stacker_response.stacker_set.signers.as_ref().unwrap().len(),
        1
    );
    assert_eq!(stacker_response.stacker_set.rewarded_addresses.len(), 1);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    info!("Bootstrapped to Epoch-3.0 boundary, mining nakamoto blocks");

    let sortdb = burnchain.open_sortition_db(true).unwrap();

    // Mine nakamoto tenures
    for _i in 0..30 {
        let prior_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;
        if let Err(e) = next_block_and_mine_commit(
            &mut btc_regtest_controller,
            30,
            &coord_channel,
            &commits_submitted,
        ) {
            warn!(
                "Error while minting a bitcoin block and waiting for stacks-node activity: {e:?}"
            );
            panic!();
        }

        let tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        assert!(
            tip_sn.sortition,
            "The new chain tip must have had a sortition"
        );
        assert!(
            tip_sn.block_height > prior_tip,
            "The new burnchain tip must have been processed"
        );

        signer_vote_if_needed(
            &btc_regtest_controller,
            &naka_conf,
            &[sender_signer_sk],
            &signers,
        );
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    let new_blocks_with_reward_set: Vec<serde_json::Value> = test_observer::get_blocks()
        .into_iter()
        .filter(|block| {
            block.get("reward_set").map_or(false, |v| !v.is_null())
                && block.get("cycle_number").map_or(false, |v| !v.is_null())
        })
        .collect();
    info!(
        "Announced blocks that include reward sets: {:#?}",
        new_blocks_with_reward_set
    );

    assert_eq!(
        new_blocks_with_reward_set.len(),
        5,
        "There should be exactly 5 blocks including reward cycles"
    );

    let cycle_numbers: Vec<u64> = new_blocks_with_reward_set
        .iter()
        .filter_map(|block| block.get("cycle_number").and_then(|cn| cn.as_u64()))
        .collect();

    let expected_cycles: Vec<u64> = (21..=25).collect();
    assert_eq!(
        cycle_numbers, expected_cycles,
        "Cycle numbers should be 21 to 25 inclusive"
    );

    let mut sorted_new_blocks = new_blocks_with_reward_set.clone();
    sorted_new_blocks.sort_by_key(|block| block["cycle_number"].as_u64().unwrap());
    assert_eq!(
        sorted_new_blocks, new_blocks_with_reward_set,
        "Blocks should be sorted by cycle number already"
    );

    for block in new_blocks_with_reward_set.iter() {
        let cycle_number = block["cycle_number"].as_u64().unwrap();
        let reward_set = block["reward_set"].as_object().unwrap();

        if cycle_number < first_epoch_3_cycle {
            assert!(
                reward_set.get("signers").is_none()
                    || reward_set["signers"].as_array().unwrap().is_empty(),
                "Signers should not be set before the first epoch 3 cycle"
            );
            continue;
        }

        // For cycles in or after first_epoch_3_cycle, ensure signers are present
        let signers = reward_set["signers"].as_array().unwrap();
        assert!(!signers.is_empty(), "Signers should be set in any epoch-3 cycles. First epoch-3 cycle: {first_epoch_3_cycle}. Checked cycle number: {cycle_number}");

        assert_eq!(
            reward_set["rewarded_addresses"].as_array().unwrap().len(),
            1,
            "There should be exactly 1 rewarded address"
        );
        assert_eq!(signers.len(), 1, "There should be exactly 1 signer");

        // the signer should have 1 "slot", because they stacked the minimum stacking amount
        let signer_weight = signers[0]["weight"].as_u64().unwrap();
        assert_eq!(signer_weight, 1, "The signer should have a weight of 1, indicating they stacked the minimum stacking amount");
    }

    run_loop_thread.join().unwrap();
}

/// Test `/v2/block_proposal` API endpoint
///
/// This endpoint allows miners to propose Nakamoto blocks to a node,
/// and test if they would be accepted or rejected
#[test]
#[ignore]
fn block_proposal_api_endpoint() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    conf.connection_options.block_proposal_token = Some(password.clone());
    let account_keys = add_initial_balances(&mut conf, 10, 1_000_000);
    let stacker_sk = setup_stacker(&mut conf);
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );

    // only subscribe to the block proposal events
    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::BlockProposal],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");
    blind_signer(&conf, &signers, proposals_submitted);

    let burnchain = conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (mut chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let _block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 3 nakamoto tenures
    for _ in 0..3 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    // TODO (hack) instantiate the sortdb in the burnchain
    _ = btc_regtest_controller.sortdb_mut();

    // ----- Setup boilerplate finished, test block proposal API endpoint -----

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let privk = conf.miner.mining_key.unwrap().clone();
    let sort_tip = SortitionDB::get_canonical_sortition_tip(sortdb.conn())
        .expect("Failed to get sortition tip");
    let db_handle = sortdb.index_handle(&sort_tip);
    let snapshot = db_handle
        .get_block_snapshot(&tip.burn_header_hash)
        .expect("Failed to get block snapshot")
        .expect("No snapshot");
    // Double check we got the right sortition
    assert_eq!(
        snapshot.consensus_hash, tip.consensus_hash,
        "Found incorrect block snapshot"
    );
    let total_burn = snapshot.total_burn;
    let tenure_change = None;
    let coinbase = None;

    let tenure_cause = tenure_change.and_then(|tx: &StacksTransaction| match &tx.payload {
        TransactionPayload::TenureChange(tc) => Some(tc.cause),
        _ => None,
    });

    // Apply miner signature
    let sign = |p: &NakamotoBlockProposal| {
        let mut p = p.clone();
        p.block
            .header
            .sign_miner(&privk)
            .expect("Miner failed to sign");
        p
    };

    let block = {
        let mut builder = NakamotoBlockBuilder::new(
            &tip,
            &tip.consensus_hash,
            total_burn,
            tenure_change,
            coinbase,
            1,
        )
        .expect("Failed to build Nakamoto block");

        let burn_dbconn = btc_regtest_controller.sortdb_ref().index_handle_at_tip();
        let mut miner_tenure_info = builder
            .load_tenure_info(&mut chainstate, &burn_dbconn, tenure_cause)
            .unwrap();
        let mut tenure_tx = builder
            .tenure_begin(&burn_dbconn, &mut miner_tenure_info)
            .unwrap();

        let tx = make_stacks_transfer(
            &account_keys[0],
            0,
            100,
            &to_addr(&account_keys[1]).into(),
            10000,
        );
        let tx = StacksTransaction::consensus_deserialize(&mut &tx[..])
            .expect("Failed to deserialize transaction");
        let tx_len = tx.tx_len();

        let res = builder.try_mine_tx_with_len(
            &mut tenure_tx,
            &tx,
            tx_len,
            &BlockLimitFunction::NO_LIMIT_HIT,
            ASTRules::PrecheckSize,
        );
        assert!(
            matches!(res, TransactionResult::Success(..)),
            "Transaction failed"
        );
        builder.mine_nakamoto_block(&mut tenure_tx)
    };

    // Construct a valid proposal. Make alterations to this to test failure cases
    let proposal = NakamotoBlockProposal {
        block,
        chain_id: chainstate.chain_id,
    };

    const HTTP_ACCEPTED: u16 = 202;
    const HTTP_TOO_MANY: u16 = 429;
    const HTTP_NOT_AUTHORIZED: u16 = 401;
    let test_cases = [
        (
            "Valid Nakamoto block proposal",
            sign(&proposal),
            HTTP_ACCEPTED,
            Some(Ok(())),
        ),
        ("Must wait", sign(&proposal), HTTP_TOO_MANY, None),
        (
            "Corrupted (bit flipped after signing)",
            (|| {
                let mut sp = sign(&proposal);
                sp.block.header.consensus_hash.0[3] ^= 0x07;
                sp
            })(),
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::ChainstateError)),
        ),
        (
            "Invalid `chain_id`",
            (|| {
                let mut p = proposal.clone();
                p.chain_id ^= 0xFFFFFFFF;
                sign(&p)
            })(),
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::InvalidBlock)),
        ),
        (
            "Invalid `miner_signature`",
            (|| {
                let mut sp = sign(&proposal);
                sp.block.header.miner_signature.0[1] ^= 0x80;
                sp
            })(),
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::ChainstateError)),
        ),
        ("Not authorized", sign(&proposal), HTTP_NOT_AUTHORIZED, None),
    ];

    // Build HTTP client
    let client = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(60))
        .build()
        .expect("Failed to build `reqwest::Client`");
    // Build URL
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let path = format!("{http_origin}/v2/block_proposal");

    let mut hold_proposal_mutex = Some(test_observer::PROPOSAL_RESPONSES.lock().unwrap());
    for (ix, (test_description, block_proposal, expected_http_code, _)) in
        test_cases.iter().enumerate()
    {
        // Send POST request
        let request_builder = client
            .post(&path)
            .header("Content-Type", "application/json")
            .json(block_proposal);
        let mut response = if expected_http_code == &HTTP_NOT_AUTHORIZED {
            request_builder.send().expect("Failed to POST")
        } else {
            request_builder
                .header(AUTHORIZATION.to_string(), password.to_string())
                .send()
                .expect("Failed to POST")
        };
        let start_time = Instant::now();
        while ix != 1 && response.status().as_u16() == HTTP_TOO_MANY {
            if start_time.elapsed() > Duration::from_secs(30) {
                error!("Took over 30 seconds to process pending proposal, panicking test");
                panic!();
            }
            info!("Waiting for prior request to finish processing, and then resubmitting");
            thread::sleep(Duration::from_secs(5));
            let request_builder = client
                .post(&path)
                .header("Content-Type", "application/json")
                .json(block_proposal);
            response = if expected_http_code == &HTTP_NOT_AUTHORIZED {
                request_builder.send().expect("Failed to POST")
            } else {
                request_builder
                    .header(AUTHORIZATION.to_string(), password.to_string())
                    .send()
                    .expect("Failed to POST")
            };
        }

        let response_code = response.status().as_u16();
        let response_json = if expected_http_code != &HTTP_NOT_AUTHORIZED {
            response.json::<serde_json::Value>().unwrap().to_string()
        } else {
            "No json response".to_string()
        };
        info!(
            "Block proposal submitted and checked for HTTP response";
            "response_json" => response_json,
            "request_json" => serde_json::to_string(block_proposal).unwrap(),
            "response_code" => response_code,
            "test_description" => test_description,
        );

        assert_eq!(response_code, *expected_http_code);

        if ix == 1 {
            // release the test observer mutex so that the handler from 0 can finish!
            hold_proposal_mutex.take();
        }
    }

    let expected_proposal_responses: Vec<_> = test_cases
        .iter()
        .filter_map(|(_, _, _, expected_response)| expected_response.as_ref())
        .collect();

    let mut proposal_responses = test_observer::get_proposal_responses();
    let start_time = Instant::now();
    while proposal_responses.len() < expected_proposal_responses.len() {
        if start_time.elapsed() > Duration::from_secs(30) {
            error!("Took over 30 seconds to process pending proposal, panicking test");
            panic!();
        }
        info!("Waiting for prior request to finish processing");
        thread::sleep(Duration::from_secs(5));
        proposal_responses = test_observer::get_proposal_responses();
    }

    for (expected_response, response) in expected_proposal_responses
        .iter()
        .zip(proposal_responses.iter())
    {
        match expected_response {
            Ok(_) => {
                assert!(matches!(response, BlockValidateResponse::Ok(_)));
            }
            Err(expected_reject_code) => {
                assert!(matches!(
                    response,
                    BlockValidateResponse::Reject(
                        BlockValidateReject { reason_code, .. })
                        if reason_code == expected_reject_code
                ));
            }
        }
        info!("Proposal response {response:?}");
    }

    // Clean up
    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node and attempts to mine a single Nakamoto block.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes the following assertions:
///  * The proposed Nakamoto block is written to the .miners stackerdb
fn miner_writes_proposed_block_to_stackerdb() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);
    let sender_sk = Secp256k1PrivateKey::new();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        send_amt + send_fee,
    );
    let stacker_sk = setup_stacker(&mut naka_conf);

    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );

    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent, EventKeyType::MinedBlocks],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 1 nakamoto tenure
    next_block_and_mine_commit(
        &mut btc_regtest_controller,
        60,
        &coord_channel,
        &commits_submitted,
    )
    .unwrap();

    let sortdb = naka_conf.get_burnchain().open_sortition_db(true).unwrap();

    let proposed_block = get_latest_block_proposal(&naka_conf, &sortdb)
        .expect("Expected to find a proposed block in the StackerDB")
        .0;
    let proposed_block_hash = format!("0x{}", proposed_block.header.block_hash());

    let mut proposed_zero_block = proposed_block.clone();
    proposed_zero_block.header.signer_signature = vec![];
    let proposed_zero_block_hash = format!("0x{}", proposed_zero_block.header.block_hash());

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();

    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();

    let observed_blocks = test_observer::get_mined_nakamoto_blocks();
    assert_eq!(observed_blocks.len(), 1);

    let observed_block = observed_blocks.first().unwrap();
    info!(
        "Checking observed and proposed miner block";
        "observed_block" => ?observed_block,
        "proposed_block" => ?proposed_block,
        "observed_block_hash" => format!("0x{}", observed_block.block_hash),
        "proposed_zero_block_hash" => &proposed_zero_block_hash,
        "proposed_block_hash" => &proposed_block_hash,
    );

    let signer_bitvec_str = observed_block.signer_bitvec.clone();
    let signer_bitvec_bytes = hex_bytes(&signer_bitvec_str).unwrap();
    let signer_bitvec = BitVec::<4000>::consensus_deserialize(&mut signer_bitvec_bytes.as_slice())
        .expect("Failed to deserialize signer bitvec");

    assert_eq!(signer_bitvec.len(), 30);

    assert_eq!(
        format!("0x{}", observed_block.block_hash),
        proposed_zero_block_hash,
        "Observed miner hash should match the proposed block read from StackerDB (after zeroing signatures)"
    );
}

#[test]
#[ignore]
fn vote_for_aggregate_key_burn_op() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let _http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let signer_sk = Secp256k1PrivateKey::new();
    let signer_addr = tests::to_addr(&signer_sk);

    let mut signers = TestSigners::new(vec![signer_sk.clone()]);

    naka_conf.add_initial_balance(PrincipalData::from(signer_addr.clone()).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let _sortdb = burnchain.open_sortition_db(true).unwrap();
    let (_chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // submit a pre-stx op
    let mut miner_signer = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();
    info!("Submitting pre-stx op");
    let pre_stx_op = PreStxOp {
        output: signer_addr.clone(),
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::PreStx(pre_stx_op),
                &mut miner_signer,
                1
            )
            .is_some(),
        "Pre-stx operation should submit successfully"
    );

    // Mine until the next prepare phase
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    let prepare_phase_start = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        );

    let blocks_until_prepare = prepare_phase_start + 1 - block_height;

    info!(
        "Mining until prepare phase start.";
        "prepare_phase_start" => prepare_phase_start,
        "block_height" => block_height,
        "blocks_until_prepare" => blocks_until_prepare,
    );

    for _i in 0..(blocks_until_prepare) {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    let reward_cycle = reward_cycle + 1;

    let signer_index = 0;

    info!(
        "Submitting vote for aggregate key op";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
        "signer_index" => %signer_index,
    );

    let stacker_pk = StacksPublicKey::from_private(&stacker_sk);
    let signer_key: StacksPublicKeyBuffer = stacker_pk.to_bytes_compressed().as_slice().into();
    let aggregate_key = signer_key.clone();

    let vote_for_aggregate_key_op =
        BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
            signer_key,
            signer_index,
            sender: signer_addr.clone(),
            round: 0,
            reward_cycle,
            aggregate_key,
            // to be filled in
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        });

    let mut signer_burnop_signer = BurnchainOpSigner::new(signer_sk.clone(), false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                vote_for_aggregate_key_op,
                &mut signer_burnop_signer,
                1
            )
            .is_some(),
        "Vote for aggregate key operation should submit successfully"
    );

    info!("Submitted vote for aggregate key op at height {block_height}, mining a few blocks...");

    // the second block should process the vote, after which the vote should be set
    for _i in 0..2 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    let mut vote_for_aggregate_key_found = false;
    let blocks = test_observer::get_blocks();
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                info!("Found a burn op: {:?}", tx);
                let burnchain_op = tx.get("burnchain_op").unwrap().as_object().unwrap();
                if !burnchain_op.contains_key("vote_for_aggregate_key") {
                    warn!("Got unexpected burnchain op: {:?}", burnchain_op);
                    panic!("unexpected btc transaction type");
                }
                let vote_obj = burnchain_op.get("vote_for_aggregate_key").unwrap();
                let agg_key = vote_obj
                    .get("aggregate_key")
                    .expect("Expected aggregate_key key in burn op")
                    .as_str()
                    .unwrap();
                assert_eq!(agg_key, aggregate_key.to_hex());

                vote_for_aggregate_key_found = true;
            }
        }
    }
    assert!(
        vote_for_aggregate_key_found,
        "Expected vote for aggregate key op"
    );

    // Check that the correct key was set
    let saved_key = get_key_for_cycle(reward_cycle, false, &naka_conf.node.rpc_bind)
        .expect("Expected to be able to check key is set after voting")
        .expect("Expected aggregate key to be set");

    assert_eq!(saved_key, aggregate_key.as_bytes().to_vec());

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// This test boots a follower node using the block downloader
#[test]
#[ignore]
fn follower_bootup() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let mut follower_conf = naka_conf.clone();
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    let mut rng = rand::thread_rng();
    let mut buf = [0u8; 8];
    rng.fill_bytes(&mut buf);

    let rpc_port = u16::from_be_bytes(buf[0..2].try_into().unwrap()).saturating_add(1025) - 1; // use a non-privileged port between 1024 and 65534
    let p2p_port = u16::from_be_bytes(buf[2..4].try_into().unwrap()).saturating_add(1025) - 1; // use a non-privileged port between 1024 and 65534

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{}:{}", &localhost, rpc_port);
    follower_conf.node.p2p_bind = format!("{}:{}", &localhost, p2p_port);
    follower_conf.node.data_url = format!("http://{}:{}", &localhost, rpc_port);
    follower_conf.node.p2p_address = format!("{}:{}", &localhost, p2p_port);
    follower_conf.node.pox_sync_sample_secs = 30;

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        CHAIN_ID_TESTNET,
        PEER_VERSION_TESTNET,
    );

    let mut follower_run_loop = boot_nakamoto::BootRunLoop::new(follower_conf.clone()).unwrap();
    let follower_run_loop_stopper = follower_run_loop.get_termination_switch();
    let follower_coord_channel = follower_run_loop.coordinator_channels();

    debug!(
        "Booting follower-thread ({},{})",
        &follower_conf.node.p2p_bind, &follower_conf.node.rpc_bind
    );
    debug!(
        "Booting follower-thread: neighbors = {:?}",
        &follower_conf.node.bootstrap_node
    );

    // spawn a follower thread
    let follower_thread = thread::Builder::new()
        .name("follower-thread".into())
        .spawn(move || follower_run_loop.start(None, 0))
        .unwrap();

    debug!("Booted follower-thread");

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        debug!("follower_bootup: Miner runs tenure {}", tenure_ix);
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_nonce = None;

        debug!(
            "follower_bootup: Miner mines interum blocks for tenure {}",
            tenure_ix
        );

        // mine the interim blocks
        for _ in 0..inter_blocks_per_tenure {
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();

            let account = loop {
                // submit a tx so that the miner will mine an extra block
                let Ok(account) = get_account_result(&http_origin, &sender_addr) else {
                    debug!("follower_bootup: Failed to load miner account");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };
                break account;
            };

            let sender_nonce = account
                .nonce
                .max(last_nonce.as_ref().map(|ln| *ln + 1).unwrap_or(0));
            let transfer_tx =
                make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
            submit_tx(&http_origin, &transfer_tx);

            last_nonce = Some(sender_nonce);

            let tx = StacksTransaction::consensus_deserialize(&mut &transfer_tx[..]).unwrap();

            debug!("follower_bootup: Miner account: {:?}", &account);
            debug!("follower_bootup: Miner sent {}: {:?}", &tx.txid(), &tx);

            let now = get_epoch_time_secs();
            while get_epoch_time_secs() < now + 10 {
                let Ok(info) = get_chain_info_result(&naka_conf) else {
                    debug!("follower_bootup: Could not get miner chain info");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };

                let Ok(follower_info) = get_chain_info_result(&follower_conf) else {
                    debug!("follower_bootup: Could not get follower chain info");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };

                if follower_info.burn_block_height < info.burn_block_height {
                    debug!("follower_bootup: Follower is behind miner's burnchain view");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                }

                if info.stacks_tip == last_tip {
                    debug!(
                        "follower_bootup: Miner stacks tip hasn't changed ({})",
                        &info.stacks_tip
                    );
                    thread::sleep(Duration::from_millis(100));
                    continue;
                }

                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();

                if blocks_processed > blocks_processed_before {
                    break;
                }

                debug!("follower_bootup: No blocks processed yet");
                thread::sleep(Duration::from_millis(100));
            }

            // compare chain tips
            loop {
                let Ok(info) = get_chain_info_result(&naka_conf) else {
                    debug!("follower_bootup: failed to load tip info");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };

                let Ok(follower_info) = get_chain_info_result(&follower_conf) else {
                    debug!("follower_bootup: Could not get follower chain info");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };
                if info.stacks_tip == follower_info.stacks_tip {
                    debug!(
                        "follower_bootup: Follower has advanced to miner's tip {}",
                        &info.stacks_tip
                    );
                } else {
                    debug!(
                        "follower_bootup: Follower has NOT advanced to miner's tip: {} != {}",
                        &info.stacks_tip, follower_info.stacks_tip
                    );
                }

                last_tip = info.stacks_tip;
                break;
            }
        }

        debug!("follower_bootup: Wait for next block-commit");
        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
        debug!("follower_bootup: Block commit submitted");
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert_eq!(
        tip.stacks_block_height,
        block_height_pre_3_0 + ((inter_blocks_per_tenure + 1) * tenure_count),
        "Should have mined (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    // wait for follower to reach the chain tip
    loop {
        sleep_ms(1000);
        let follower_node_info = get_chain_info(&follower_conf);

        info!(
            "Follower tip is now {}/{}",
            &follower_node_info.stacks_tip_consensus_hash, &follower_node_info.stacks_tip
        );
        if follower_node_info.stacks_tip_consensus_hash == tip.consensus_hash
            && follower_node_info.stacks_tip == tip.anchored_header.block_hash()
        {
            break;
        }
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    follower_coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    follower_run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
    follower_thread.join().unwrap();
}

#[test]
#[ignore]
fn stack_stx_burn_op_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.burnchain.satoshis_per_byte = 2;
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);

    let signer_sk_1 = setup_stacker(&mut naka_conf);
    let signer_addr_1 = tests::to_addr(&signer_sk_1);

    let signer_sk_2 = Secp256k1PrivateKey::new();
    let signer_addr_2 = tests::to_addr(&signer_sk_2);

    let mut signers = TestSigners::new(vec![signer_sk_1.clone()]);

    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk_1],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let block_height = btc_regtest_controller.get_headers_height();

    // submit a pre-stx op
    let mut miner_signer_1 = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();

    info!("Submitting first pre-stx op");
    let pre_stx_op = PreStxOp {
        output: signer_addr_1.clone(),
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::PreStx(pre_stx_op),
                &mut miner_signer_1,
                1
            )
            .is_some(),
        "Pre-stx operation should submit successfully"
    );

    next_block_and_mine_commit(
        &mut btc_regtest_controller,
        60,
        &coord_channel,
        &commits_submitted,
    )
    .unwrap();

    let mut miner_signer_2 = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();
    info!("Submitting second pre-stx op");
    let pre_stx_op_2 = PreStxOp {
        output: signer_addr_2.clone(),
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::PreStx(pre_stx_op_2),
                &mut miner_signer_2,
                1
            )
            .is_some(),
        "Pre-stx operation should submit successfully"
    );
    info!("Submitted 2 pre-stx ops at block {block_height}, mining a few blocks...");

    // Mine until the next prepare phase
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();
    let prepare_phase_start = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        );

    let blocks_until_prepare = prepare_phase_start + 1 - block_height;

    let lock_period: u8 = 6;
    let topic = Pox4SignatureTopic::StackStx;
    let auth_id: u32 = 1;
    let pox_addr = PoxAddress::Standard(signer_addr_1, Some(AddressHashMode::SerializeP2PKH));

    info!(
        "Submitting set-signer-key-authorization";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
    );

    let signer_pk_1 = StacksPublicKey::from_private(&signer_sk_1);
    let signer_key_arg_1: StacksPublicKeyBuffer =
        signer_pk_1.to_bytes_compressed().as_slice().into();

    let set_signer_key_auth_tx = tests::make_contract_call(
        &signer_sk_1,
        1,
        500,
        &StacksAddress::burn_address(false),
        "pox-4",
        "set-signer-key-authorization",
        &[
            clarity::vm::Value::Tuple(pox_addr.clone().as_clarity_tuple().unwrap()),
            clarity::vm::Value::UInt(lock_period.into()),
            clarity::vm::Value::UInt(reward_cycle.into()),
            clarity::vm::Value::string_ascii_from_bytes(topic.get_name_str().into()).unwrap(),
            clarity::vm::Value::buff_from(signer_pk_1.clone().to_bytes_compressed()).unwrap(),
            clarity::vm::Value::Bool(true),
            clarity::vm::Value::UInt(u128::MAX),
            clarity::vm::Value::UInt(auth_id.into()),
        ],
    );

    submit_tx(&http_origin, &set_signer_key_auth_tx);

    info!(
        "Mining until prepare phase start.";
        "prepare_phase_start" => prepare_phase_start,
        "block_height" => block_height,
        "blocks_until_prepare" => blocks_until_prepare,
    );

    for _i in 0..(blocks_until_prepare) {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    let reward_cycle = reward_cycle + 1;

    info!(
        "Submitting stack stx op";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
    );

    let mut signer_burnop_signer_1 = BurnchainOpSigner::new(signer_sk_1.clone(), false);
    let mut signer_burnop_signer_2 = BurnchainOpSigner::new(signer_sk_2.clone(), false);

    info!(
        "Before stack-stx op, signer 1 total: {}",
        btc_regtest_controller
            .get_utxos(
                StacksEpochId::Epoch30,
                &signer_burnop_signer_1.get_public_key(),
                1,
                None,
                block_height
            )
            .unwrap()
            .total_available(),
    );
    info!(
        "Before stack-stx op, signer 2 total: {}",
        btc_regtest_controller
            .get_utxos(
                StacksEpochId::Epoch30,
                &signer_burnop_signer_2.get_public_key(),
                1,
                None,
                block_height
            )
            .unwrap()
            .total_available(),
    );

    info!("Signer 1 addr: {}", signer_addr_1.to_b58());
    info!("Signer 2 addr: {}", signer_addr_2.to_b58());

    let pox_info = get_pox_info(&http_origin).unwrap();
    let min_stx = pox_info.next_cycle.min_threshold_ustx;

    let stack_stx_op_with_some_signer_key = StackStxOp {
        sender: signer_addr_1.clone(),
        reward_addr: pox_addr,
        stacked_ustx: min_stx.into(),
        num_cycles: lock_period,
        signer_key: Some(signer_key_arg_1),
        max_amount: Some(u128::MAX),
        auth_id: Some(auth_id),
        // to be filled in
        vtxindex: 0,
        txid: Txid([0u8; 32]),
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash::zero(),
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::StackStx(stack_stx_op_with_some_signer_key),
                &mut signer_burnop_signer_1,
                1
            )
            .is_some(),
        "Stack STX operation should submit successfully"
    );

    let stack_stx_op_with_no_signer_key = StackStxOp {
        sender: signer_addr_2.clone(),
        reward_addr: PoxAddress::Standard(signer_addr_2, None),
        stacked_ustx: 100000,
        num_cycles: 6,
        signer_key: None,
        max_amount: None,
        auth_id: None,
        // to be filled in
        vtxindex: 0,
        txid: Txid([0u8; 32]),
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash::zero(),
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::StackStx(stack_stx_op_with_no_signer_key),
                &mut signer_burnop_signer_2,
                1
            )
            .is_some(),
        "Stack STX operation should submit successfully"
    );

    info!("Submitted 2 stack STX ops at height {block_height}, mining a few blocks...");

    // the second block should process the vote, after which the balances should be unchanged
    for _i in 0..2 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    let mut stack_stx_found = false;
    let mut stack_stx_burn_op_tx_count = 0;
    let blocks = test_observer::get_blocks();
    info!("stack event observer num blocks: {:?}", blocks.len());
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        info!(
            "stack event observer num transactions: {:?}",
            transactions.len()
        );
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                info!("Found a burn op: {:?}", tx);
                let burnchain_op = tx.get("burnchain_op").unwrap().as_object().unwrap();
                if !burnchain_op.contains_key("stack_stx") {
                    warn!("Got unexpected burnchain op: {:?}", burnchain_op);
                    panic!("unexpected btc transaction type");
                }
                let stack_stx_obj = burnchain_op.get("stack_stx").unwrap();
                let signer_key_found = stack_stx_obj
                    .get("signer_key")
                    .expect("Expected signer_key in burn op")
                    .as_str()
                    .unwrap();
                assert_eq!(signer_key_found, signer_key_arg_1.to_hex());

                let max_amount_correct = stack_stx_obj
                    .get("max_amount")
                    .expect("Expected max_amount")
                    .as_number()
                    .expect("Expected max_amount to be a number")
                    .eq(&serde_json::Number::from(u128::MAX));
                assert!(max_amount_correct, "Expected max_amount to be u128::MAX");

                let auth_id_correct = stack_stx_obj
                    .get("auth_id")
                    .expect("Expected auth_id in burn op")
                    .as_number()
                    .expect("Expected auth id")
                    .eq(&serde_json::Number::from(auth_id));
                assert!(auth_id_correct, "Expected auth_id to be 1");

                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed =
                    clarity::vm::Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                info!("Clarity result of stack-stx op: {parsed}");
                parsed
                    .expect_result_ok()
                    .expect("Expected OK result for stack-stx op");

                stack_stx_found = true;
                stack_stx_burn_op_tx_count += 1;
            }
        }
    }
    assert!(stack_stx_found, "Expected stack STX op");
    assert_eq!(
        stack_stx_burn_op_tx_count, 1,
        "Stack-stx tx without a signer_key shouldn't have been submitted"
    );

    let sortdb = btc_regtest_controller.sortdb_mut();
    let sortdb_conn = sortdb.conn();
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb_conn).unwrap();

    let ancestor_burnchain_header_hashes =
        SortitionDB::get_ancestor_burnchain_header_hashes(sortdb.conn(), &tip.burn_header_hash, 6)
            .unwrap();

    let mut all_stacking_burn_ops = vec![];
    let mut found_none = false;
    let mut found_some = false;
    // go from oldest burn header hash to newest
    for ancestor_bhh in ancestor_burnchain_header_hashes.iter().rev() {
        let stacking_ops = SortitionDB::get_stack_stx_ops(sortdb_conn, ancestor_bhh).unwrap();
        for stacking_op in stacking_ops.into_iter() {
            debug!("Stacking op queried from sortdb: {:?}", stacking_op);
            match stacking_op.signer_key {
                Some(_) => found_some = true,
                None => found_none = true,
            }
            all_stacking_burn_ops.push(stacking_op);
        }
    }
    assert_eq!(
        all_stacking_burn_ops.len(),
        2,
        "Both stack-stx ops with and without a signer_key should be considered valid."
    );
    assert!(
        found_none,
        "Expected one stacking_op to have a signer_key of None"
    );
    assert!(
        found_some,
        "Expected one stacking_op to have a signer_key of Some"
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// Miner A mines a regular tenure, its last block being block a_x.
/// Miner B starts its tenure, Miner B produces a Stacks block b_0, but miner C submits its block commit before b_0 is broadcasted.
/// Bitcoin block C, containing Miner C's block commit, is mined BEFORE miner C has a chance to update their block commit with b_0's information.
/// This test asserts:
///  * tenure C ignores b_0, and correctly builds off of block a_x.
fn forked_tenure_is_ignored() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(10);
    let sender_sk = Secp256k1PrivateKey::new();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        send_amt + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let stacker_sk = setup_stacker(&mut naka_conf);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent, EventKeyType::MinedBlocks],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        naka_mined_blocks: mined_blocks,
        naka_skip_commit_op: test_skip_commit_op,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    info!("Starting tenure A.");
    wait_for_first_naka_block_commit(60, &commits_submitted);

    // In the next block, the miner should win the tenure and submit a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        Ok(commits_count > commits_before && blocks_count > blocks_before)
    })
    .unwrap();

    let block_tenure_a = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    // For the next tenure, submit the commit op but do not allow any stacks blocks to be broadcasted
    TEST_BROADCAST_STALL.lock().unwrap().replace(true);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    info!("Starting tenure B.");
    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        Ok(commits_count > commits_before)
    })
    .unwrap();
    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    info!("Commit op is submitted; unpause tenure B's block");

    // Unpause the broadcast of Tenure B's block, do not submit commits.
    test_skip_commit_op.0.lock().unwrap().replace(true);
    TEST_BROADCAST_STALL.lock().unwrap().replace(false);

    // Wait for a stacks block to be broadcasted
    let start_time = Instant::now();
    while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
        assert!(
            start_time.elapsed() < Duration::from_secs(30),
            "FAIL: Test timed out while waiting for block production",
        );
        thread::sleep(Duration::from_secs(1));
    }

    info!("Tenure B broadcasted a block. Issue the next bitcon block and unstall block commits.");
    let block_tenure_b = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_b = blocks.last().unwrap();

    info!("Starting tenure C.");
    // Submit a block commit op for tenure C
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    next_block_and(&mut btc_regtest_controller, 60, || {
        test_skip_commit_op.0.lock().unwrap().replace(false);
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        Ok(commits_count > commits_before && blocks_count > blocks_before)
    })
    .unwrap();

    info!("Tenure C produced a block!");
    let block_tenure_c = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_c = blocks.last().unwrap();

    // Now let's produce a second block for tenure C and ensure it builds off of block C.
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let start_time = Instant::now();

    // submit a tx so that the miner will mine an extra block
    let sender_nonce = 0;
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    let tx = submit_tx(&http_origin, &transfer_tx);

    info!("Submitted tx {tx} in Tenure C to mine a second block");
    while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
        assert!(
            start_time.elapsed() < Duration::from_secs(30),
            "FAIL: Test timed out while waiting for block production",
        );
        thread::sleep(Duration::from_secs(1));
    }

    info!("Tenure C produced a second block!");

    let block_2_tenure_c = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_2_c = blocks.last().unwrap();

    info!("Starting tenure D.");
    // Submit a block commit op for tenure D and mine a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        Ok(commits_count > commits_before && blocks_count > blocks_before)
    })
    .unwrap();

    let block_tenure_d = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_d = blocks.last().unwrap();
    assert_ne!(block_tenure_b, block_tenure_a);
    assert_ne!(block_tenure_b, block_tenure_c);
    assert_ne!(block_tenure_c, block_tenure_a);

    // Block B was built atop block A
    assert_eq!(
        block_tenure_b.stacks_block_height,
        block_tenure_a.stacks_block_height + 1
    );
    assert_eq!(
        block_b.parent_block_id,
        block_tenure_a.index_block_hash().to_string()
    );

    // Block C was built AFTER Block B was built, but BEFORE it was broadcasted, so it should be built off of Block A
    assert_eq!(
        block_tenure_c.stacks_block_height,
        block_tenure_a.stacks_block_height + 1
    );
    assert_eq!(
        block_c.parent_block_id,
        block_tenure_a.index_block_hash().to_string()
    );

    assert_ne!(block_tenure_c, block_2_tenure_c);
    assert_ne!(block_2_tenure_c, block_tenure_d);
    assert_ne!(block_tenure_c, block_tenure_d);

    // Second block of tenure C builds off of block C
    assert_eq!(
        block_2_tenure_c.stacks_block_height,
        block_tenure_c.stacks_block_height + 1,
    );
    assert_eq!(
        block_2_c.parent_block_id,
        block_tenure_c.index_block_hash().to_string()
    );

    // Tenure D builds off of the second block of tenure C
    assert_eq!(
        block_tenure_d.stacks_block_height,
        block_2_tenure_c.stacks_block_height + 1,
    );
    assert_eq!(
        block_d.parent_block_id,
        block_2_tenure_c.index_block_hash().to_string()
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes three assertions:
///  * 5 tenures are mined after 3.0 starts
///  * Each tenure has 10 blocks (the coinbase block and 9 interim blocks)
///  * Verifies the block heights of the blocks mined
fn check_block_heights() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 =
        "(define-read-only (get-heights) { burn-block-height: burn-block-height, block-height: block-height })";

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract0_name,
        contract_clarity1,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx0);

    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let heights0_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-heights",
        vec![],
    );
    let preheights = heights0_value.expect_tuple().unwrap();
    info!("Heights from pre-epoch 3.0: {}", preheights);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let mut last_burn_block_height;
    let mut last_stacks_block_height = info.stacks_tip_height as u128;
    let mut last_tenure_height = last_stacks_block_height as u128;

    let heights0_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-heights",
        vec![],
    );
    let heights0 = heights0_value.expect_tuple().unwrap();
    info!("Heights from epoch 3.0 start: {}", heights0);
    assert_eq!(
        heights0.get("burn-block-height"),
        preheights.get("burn-block-height"),
        "Burn block height should match"
    );
    assert_eq!(
        heights0
            .get("block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap(),
        last_stacks_block_height,
        "Stacks block height should match"
    );

    // This version uses the Clarity 1 / 2 keywords
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    // This version uses the Clarity 3 keywords
    let contract3_name = "test-contract-3";
    let contract_clarity3 =
        "(define-read-only (get-heights) { burn-block-height: burn-block-height, stacks-block-height: stacks-block-height, tenure-height: tenure-height })";

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {}", tenure_ix);
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let heights1_value = call_read_only(
            &naka_conf,
            &sender_addr,
            contract1_name,
            "get-heights",
            vec![],
        );
        let heights1 = heights1_value.expect_tuple().unwrap();
        info!("Heights from Clarity 1: {}", heights1);

        let heights3_value = call_read_only(
            &naka_conf,
            &sender_addr,
            contract3_name,
            "get-heights",
            vec![],
        );
        let heights3 = heights3_value.expect_tuple().unwrap();
        info!("Heights from Clarity 3: {}", heights3);

        let bbh1 = heights1
            .get("burn-block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        let bbh3 = heights3
            .get("burn-block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        assert_eq!(bbh1, bbh3, "Burn block heights should match");
        last_burn_block_height = bbh1;

        let bh1 = heights1
            .get("block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        let bh3 = heights3
            .get("tenure-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        assert_eq!(
            bh1, bh3,
            "Clarity 2 block-height should match Clarity 3 tenure-height"
        );
        assert_eq!(
            bh1,
            last_tenure_height + 1,
            "Tenure height should have incremented"
        );
        last_tenure_height = bh1;

        let sbh = heights3
            .get("stacks-block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        assert_eq!(
            sbh,
            last_stacks_block_height + 1,
            "Stacks block heights should have incremented"
        );
        last_stacks_block_height = sbh;

        // mine the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            info!("Mining interim block {interim_block_ix}");
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            // submit a tx so that the miner will mine an extra block
            let transfer_tx =
                make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
            sender_nonce += 1;
            submit_tx(&http_origin, &transfer_tx);

            loop {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                if blocks_processed > blocks_processed_before {
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }

            let heights1_value = call_read_only(
                &naka_conf,
                &sender_addr,
                contract1_name,
                "get-heights",
                vec![],
            );
            let heights1 = heights1_value.expect_tuple().unwrap();
            info!("Heights from Clarity 1: {}", heights1);

            let heights3_value = call_read_only(
                &naka_conf,
                &sender_addr,
                contract3_name,
                "get-heights",
                vec![],
            );
            let heights3 = heights3_value.expect_tuple().unwrap();
            info!("Heights from Clarity 3: {}", heights3);

            let bbh1 = heights1
                .get("burn-block-height")
                .unwrap()
                .clone()
                .expect_u128()
                .unwrap();
            let bbh3 = heights3
                .get("burn-block-height")
                .unwrap()
                .clone()
                .expect_u128()
                .unwrap();
            assert_eq!(bbh1, bbh3, "Burn block heights should match");
            assert_eq!(
                bbh1, last_burn_block_height,
                "Burn block heights should not have incremented"
            );

            let bh1 = heights1
                .get("block-height")
                .unwrap()
                .clone()
                .expect_u128()
                .unwrap();
            let bh3 = heights3
                .get("tenure-height")
                .unwrap()
                .clone()
                .expect_u128()
                .unwrap();
            assert_eq!(
                bh1, bh3,
                "Clarity 2 block-height should match Clarity 3 tenure-height"
            );
            assert_eq!(
                bh1, last_tenure_height,
                "Tenure height should not have changed"
            );

            let sbh = heights3
                .get("stacks-block-height")
                .unwrap()
                .clone()
                .expect_u128()
                .unwrap();
            assert_eq!(
                sbh,
                last_stacks_block_height + 1,
                "Stacks block heights should have incremented"
            );
            last_stacks_block_height = sbh;
        }

        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert_eq!(
        tip.stacks_block_height,
        block_height_pre_3_0 + ((inter_blocks_per_tenure + 1) * tenure_count),
        "Should have mined (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Test config parameter `nakamoto_attempt_time_ms`
#[test]
#[ignore]
fn nakamoto_attempt_time() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    naka_conf.connection_options.block_proposal_token = Some(password.clone());
    // Use fixed timing params for this test
    let nakamoto_attempt_time_ms = 20_000;
    naka_conf.miner.nakamoto_attempt_time_ms = nakamoto_attempt_time_ms;
    let stacker_sk = setup_stacker(&mut naka_conf);

    let sender_sk = Secp256k1PrivateKey::new();
    let sender_addr = tests::to_addr(&sender_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        1_000_000_000,
    );

    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100_000,
    );

    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    // We'll need a lot of accounts for one subtest to avoid MAXIMUM_MEMPOOL_TX_CHAINING
    struct Account {
        nonce: u64,
        privk: Secp256k1PrivateKey,
        _address: StacksAddress,
    }
    let num_accounts = 1_000;
    let init_account_balance = 1_000_000_000;
    let account_keys = add_initial_balances(&mut naka_conf, num_accounts, init_account_balance);
    let mut account = account_keys
        .into_iter()
        .map(|privk| {
            let _address = tests::to_addr(&privk);
            Account {
                nonce: 0,
                privk,
                _address,
            }
        })
        .collect::<Vec<_>>();

    // only subscribe to the block proposal events
    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::BlockProposal],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let _block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 3 nakamoto tenures
    for _ in 0..3 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
    }

    // TODO (hack) instantiate the sortdb in the burnchain
    _ = btc_regtest_controller.sortdb_mut();

    // ----- Setup boilerplate finished, test block proposal API endpoint -----

    let tenure_count = 2;
    let inter_blocks_per_tenure = 3;

    info!("Begin subtest 1");

    // Subtest 1
    // Mine nakamoto tenures with a few transactions
    // Blocks should be produced at least every 20 seconds
    for _ in 0..tenure_count {
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_tip_height = 0;

        // mine the interim blocks
        for tenure_count in 0..inter_blocks_per_tenure {
            debug!("nakamoto_attempt_time: begin tenure {}", tenure_count);

            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();

            let txs_per_block = 3;
            let tx_fee = 500;
            let amount = 500;

            let account = loop {
                // submit a tx so that the miner will mine an extra block
                let Ok(account) = get_account_result(&http_origin, &sender_addr) else {
                    debug!("nakamoto_attempt_time: Failed to load miner account");
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };
                break account;
            };

            let mut sender_nonce = account.nonce;
            for _ in 0..txs_per_block {
                let transfer_tx =
                    make_stacks_transfer(&sender_sk, sender_nonce, tx_fee, &recipient, amount);
                sender_nonce += 1;
                submit_tx(&http_origin, &transfer_tx);
            }

            // Miner should have made a new block by now
            let wait_start = Instant::now();
            loop {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                if blocks_processed > blocks_processed_before {
                    break;
                }
                // wait a little longer than what the max block time should be
                if wait_start.elapsed() > Duration::from_millis(nakamoto_attempt_time_ms + 100) {
                    panic!(
                        "A block should have been produced within {nakamoto_attempt_time_ms} ms"
                    );
                }
                thread::sleep(Duration::from_secs(1));
            }

            let info = get_chain_info_result(&naka_conf).unwrap();
            assert_ne!(info.stacks_tip, last_tip);
            assert_ne!(info.stacks_tip_height, last_tip_height);

            last_tip = info.stacks_tip;
            last_tip_height = info.stacks_tip_height;
        }

        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    info!("Begin subtest 2");

    // Subtest 2
    // Confirm that no blocks are mined if there are no transactions
    for _ in 0..2 {
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();

        let info_before = get_chain_info_result(&naka_conf).unwrap();

        // Wait long enough for a block to be mined
        thread::sleep(Duration::from_millis(nakamoto_attempt_time_ms * 2));

        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();

        let info = get_chain_info_result(&naka_conf).unwrap();

        // Assert that no block was mined while waiting
        assert_eq!(blocks_processed, blocks_processed_before);
        assert_eq!(info.stacks_tip, info_before.stacks_tip);
        assert_eq!(info.stacks_tip_height, info_before.stacks_tip_height);
    }

    info!("Begin subtest 3");

    // Subtest 3
    // Add more than `nakamoto_attempt_time_ms` worth of transactions into mempool
    // Multiple blocks should be mined
    let info_before = get_chain_info_result(&naka_conf).unwrap();

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    let tx_limit = 10000;
    let tx_fee = 500;
    let amount = 500;
    let mut tx_total_size = 0;
    let mut tx_count = 0;
    let mut acct_idx = 0;

    // Submit max # of txs from each account to reach tx_limit
    'submit_txs: loop {
        let acct = &mut account[acct_idx];
        for _ in 0..MAXIMUM_MEMPOOL_TX_CHAINING {
            let transfer_tx =
                make_stacks_transfer(&acct.privk, acct.nonce, tx_fee, &recipient, amount);
            submit_tx(&http_origin, &transfer_tx);
            tx_total_size += transfer_tx.len();
            tx_count += 1;
            acct.nonce += 1;
            if tx_count >= tx_limit {
                break 'submit_txs;
            }
            info!(
                "nakamoto_times_ms: on account {}; sent {} txs so far (out of {})",
                acct_idx, tx_count, tx_limit
            );
        }
        acct_idx += 1;
    }

    info!("Subtest 3 sent all transactions");

    // Make sure that these transactions *could* fit into a single block
    assert!(tx_total_size < MAX_BLOCK_LEN as usize);

    // Wait long enough for 2 blocks to be made
    thread::sleep(Duration::from_millis(nakamoto_attempt_time_ms * 2 + 100));

    // Check that 2 blocks were made
    let blocks_processed = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    let blocks_mined = blocks_processed - blocks_processed_before;
    assert!(blocks_mined > 2);

    let info = get_chain_info_result(&naka_conf).unwrap();
    assert_ne!(info.stacks_tip, info_before.stacks_tip);
    assert_ne!(info.stacks_tip_height, info_before.stacks_tip_height);

    // ----- Clean up -----
    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test is testing the burn state of the Stacks blocks. In Stacks 2.x,
/// the burn block state accessed in a Clarity contract is the burn block of
/// the block's parent, since the block is built before its burn block is
/// mined. In Nakamoto, there is no longer this race condition, so Clarity
/// contracts access the state of the current burn block.
/// We should verify:
/// - `burn-block-height` in epoch 3.x is the burn block of the Stacks block
/// - `get-burn-block-info` is able to access info of the current burn block
///   in epoch 3.x
fn clarity_burn_state() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let tx_fee = 1000;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        deploy_fee + tx_fee * tenure_count + tx_fee * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::MinedBlocks],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let mut sender_nonce = 0;

    // This version uses the Clarity 1 / 2 keywords
    let contract_name = "test-contract";
    let contract = r#"
         (define-read-only (foo (expected-height uint))
             (begin
                 (asserts! (is-eq expected-height burn-block-height) (err burn-block-height))
                 (asserts! (is-some (get-burn-block-info? header-hash burn-block-height)) (err u0))
                 (ok true)
             )
         )
         (define-public (bar (expected-height uint))
             (foo expected-height)
         )
     "#;

    let contract_tx = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract_name,
        contract,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx);

    let mut burn_block_height = 0;

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {}", tenure_ix);

        // Don't submit this tx on the first iteration, because the contract is not published yet.
        if tenure_ix > 0 {
            // Call the read-only function and see if we see the correct burn block height
            let result = call_read_only(
                &naka_conf,
                &sender_addr,
                contract_name,
                "foo",
                vec![&Value::UInt(burn_block_height)],
            );
            result.expect_result_ok().expect("Read-only call failed");

            // Submit a tx for the next block (the next block will be a new tenure, so the burn block height will increment)
            let call_tx = tests::make_contract_call(
                &sender_sk,
                sender_nonce,
                tx_fee,
                &sender_addr,
                contract_name,
                "bar",
                &[Value::UInt(burn_block_height + 1)],
            );
            sender_nonce += 1;
            submit_tx(&http_origin, &call_tx);
        }

        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let info = get_chain_info(&naka_conf);
        burn_block_height = info.burn_block_height as u128;
        info!("Expecting burn block height to be {}", burn_block_height);

        // Assert that the contract call was successful
        test_observer::get_mined_nakamoto_blocks()
            .last()
            .unwrap()
            .tx_events
            .iter()
            .for_each(|event| match event {
                TransactionEvent::Success(TransactionSuccessEvent { result, fee, .. }) => {
                    // Ignore coinbase and tenure transactions
                    if *fee == 0 {
                        return;
                    }

                    info!("Contract call result: {}", result);
                    result.clone().expect_result_ok().expect("Ok result");
                }
                _ => {
                    info!("Unsuccessful event: {:?}", event);
                    panic!("Expected a successful transaction");
                }
            });

        // mine the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            info!("Mining interim block {interim_block_ix}");
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();

            // Call the read-only function and see if we see the correct burn block height
            let expected_height = Value::UInt(burn_block_height);
            let result = call_read_only(
                &naka_conf,
                &sender_addr,
                contract_name,
                "foo",
                vec![&expected_height],
            );
            info!("Read-only result: {:?}", result);
            result.expect_result_ok().expect("Read-only call failed");

            // Submit a tx to trigger the next block
            let call_tx = tests::make_contract_call(
                &sender_sk,
                sender_nonce,
                tx_fee,
                &sender_addr,
                contract_name,
                "bar",
                &[expected_height],
            );
            sender_nonce += 1;
            submit_tx(&http_origin, &call_tx);

            loop {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                if blocks_processed > blocks_processed_before {
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }

            // Assert that the contract call was successful
            test_observer::get_mined_nakamoto_blocks()
                .last()
                .unwrap()
                .tx_events
                .iter()
                .for_each(|event| match event {
                    TransactionEvent::Success(TransactionSuccessEvent { result, .. }) => {
                        info!("Contract call result: {}", result);
                        result.clone().expect_result_ok().expect("Ok result");
                    }
                    _ => {
                        info!("Unsuccessful event: {:?}", event);
                        panic!("Expected a successful transaction");
                    }
                });
        }

        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
fn signer_chainstate() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = format!("{}:{}", "127.0.0.1", 6000);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 200;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        (send_amt + send_fee) * 20,
    );
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    // query for prometheus metrics
    #[cfg(feature = "monitoring_prom")]
    {
        let (chainstate, _) = StacksChainState::open(
            naka_conf.is_mainnet(),
            naka_conf.burnchain.chain_id,
            &naka_conf.get_chainstate_path_str(),
            None,
        )
        .unwrap();
        let block_height_pre_3_0 =
            NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
                .unwrap()
                .unwrap()
                .stacks_block_height;
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
        assert!(res.contains(&expected_result));
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted.clone());

    let socket = naka_conf
        .node
        .rpc_bind
        .to_socket_addrs()
        .unwrap()
        .next()
        .unwrap();
    let signer_client = stacks_signer::client::StacksClient::new(
        StacksPrivateKey::from_seed(&[0, 1, 2, 3]),
        socket,
        naka_conf
            .connection_options
            .block_proposal_token
            .clone()
            .unwrap_or("".into()),
        false,
    );

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let mut signer_db =
        SignerDb::new(format!("{}/signer_db_path", naka_conf.node.working_dir)).unwrap();

    // Mine some nakamoto tenures
    //  track the last tenure's first block and subsequent blocks so we can
    //  check that they get rejected by the sortitions_view
    let mut last_tenures_proposals: Option<(StacksPublicKey, NakamotoBlock, Vec<NakamotoBlock>)> =
        None;
    // hold the first and last blocks of the first tenure. we'll use this to submit reorging proposals
    let mut first_tenure_blocks: Option<Vec<NakamotoBlock>> = None;
    for i in 0..15 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            60,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();

        // this config disallows any reorg due to poorly timed block commits
        let proposal_conf = ProposalEvalConfig {
            first_proposal_burn_block_timing: Duration::from_secs(0),
            block_proposal_timeout: Duration::from_secs(100),
        };
        let mut sortitions_view =
            SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();

        // check the prior tenure's proposals again, confirming that the sortitions_view
        //  will reject them.
        if let Some((ref miner_pk, ref prior_tenure_first, ref prior_tenure_interims)) =
            last_tenures_proposals
        {
            let valid = sortitions_view
                .check_proposal(&signer_client, &signer_db, prior_tenure_first, miner_pk)
                .unwrap();
            assert!(
                !valid,
                "Sortitions view should reject proposals from prior tenure"
            );
            for block in prior_tenure_interims.iter() {
                let valid = sortitions_view
                    .check_proposal(&signer_client, &signer_db, block, miner_pk)
                    .unwrap();
                assert!(
                    !valid,
                    "Sortitions view should reject proposals from prior tenure"
                );
            }
        }

        // make sure we're getting a proposal from the current sortition (not 100% guaranteed by
        //  `next_block_and_mine_commit`) by looping
        let time_start = Instant::now();
        let proposal = loop {
            let proposal = get_latest_block_proposal(&naka_conf, &sortdb).unwrap();
            if proposal.0.header.consensus_hash == sortitions_view.latest_consensus_hash {
                break proposal;
            }
            if time_start.elapsed() > Duration::from_secs(20) {
                panic!("Timed out waiting for block proposal from the current bitcoin block");
            }
            thread::sleep(Duration::from_secs(1));
        };

        let valid = sortitions_view
            .check_proposal(&signer_client, &signer_db, &proposal.0, &proposal.1)
            .unwrap();

        assert!(
            valid,
            "Nakamoto integration test produced invalid block proposal"
        );
        let burn_block_height = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;
        let reward_cycle = burnchain
            .block_height_to_reward_cycle(burn_block_height)
            .unwrap();
        signer_db
            .insert_block(&BlockInfo {
                block: proposal.0.clone(),
                burn_block_height,
                reward_cycle,
                vote: None,
                valid: Some(true),
                signed_over: true,
                proposed_time: get_epoch_time_secs(),
                signed_self: None,
                signed_group: None,
                ext: ExtraBlockInfo::None,
            })
            .unwrap();

        let before = proposals_submitted.load(Ordering::SeqCst);

        // submit a tx to trigger an intermediate block
        let sender_nonce = i;
        let transfer_tx =
            make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
        submit_tx(&http_origin, &transfer_tx);

        signer_vote_if_needed(
            &btc_regtest_controller,
            &naka_conf,
            &[sender_signer_sk],
            &signers,
        );

        let timer = Instant::now();
        while proposals_submitted.load(Ordering::SeqCst) <= before {
            thread::sleep(Duration::from_millis(5));
            if timer.elapsed() > Duration::from_secs(30) {
                panic!("Timed out waiting for nakamoto miner to produce intermediate block");
            }
        }

        // an intermediate block was produced. check the proposed block
        let proposal_interim = get_latest_block_proposal(&naka_conf, &sortdb).unwrap();

        let valid = sortitions_view
            .check_proposal(
                &signer_client,
                &signer_db,
                &proposal_interim.0,
                &proposal_interim.1,
            )
            .unwrap();

        assert!(
            valid,
            "Nakamoto integration test produced invalid block proposal"
        );
        // force the view to refresh and check again

        // this config disallows any reorg due to poorly timed block commits
        let proposal_conf = ProposalEvalConfig {
            first_proposal_burn_block_timing: Duration::from_secs(0),
            block_proposal_timeout: Duration::from_secs(100),
        };
        let mut sortitions_view =
            SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();
        let valid = sortitions_view
            .check_proposal(
                &signer_client,
                &signer_db,
                &proposal_interim.0,
                &proposal_interim.1,
            )
            .unwrap();

        assert!(
            valid,
            "Nakamoto integration test produced invalid block proposal"
        );

        signer_db
            .insert_block(&BlockInfo {
                block: proposal_interim.0.clone(),
                burn_block_height,
                reward_cycle,
                vote: None,
                valid: Some(true),
                signed_over: true,
                proposed_time: get_epoch_time_secs(),
                signed_self: None,
                signed_group: None,
                ext: ExtraBlockInfo::None,
            })
            .unwrap();

        if first_tenure_blocks.is_none() {
            first_tenure_blocks = Some(vec![proposal.0.clone(), proposal_interim.0.clone()]);
        }
        last_tenures_proposals = Some((proposal.1, proposal.0, vec![proposal_interim.0]));
    }

    // now we'll check some specific cases of invalid proposals
    // Case: the block doesn't confirm the prior blocks that have been signed.
    let last_tenure = &last_tenures_proposals.as_ref().unwrap().1.clone();
    let last_tenure_header = &last_tenure.header;
    let miner_sk = naka_conf.miner.mining_key.clone().unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: last_tenure_header.chain_length,
        burn_spent: last_tenure_header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash.clone(),
        parent_block_id: last_tenure_header.block_id(),
        tx_merkle_root: Sha512Trunc256Sum::from_data(&[0]),
        state_index_root: TrieHash([0; 32]),
        timestamp: last_tenure_header.timestamp + 1,
        miner_signature: MessageSignature([0; 65]),
        signer_signature: Vec::new(),
        pox_treatment: BitVec::ones(1).unwrap(),
    };
    sibling_block_header.sign_miner(&miner_sk).unwrap();

    let sibling_block = NakamotoBlock {
        header: sibling_block_header,
        txs: vec![],
    };

    // this config disallows any reorg due to poorly timed block commits
    let proposal_conf = ProposalEvalConfig {
        first_proposal_burn_block_timing: Duration::from_secs(0),
        block_proposal_timeout: Duration::from_secs(100),
    };
    let mut sortitions_view = SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();

    assert!(
        !sortitions_view
            .check_proposal(&signer_client, &signer_db, &sibling_block, &miner_pk)
            .unwrap(),
        "A sibling of a previously approved block must be rejected."
    );

    // Case: the block contains a tenure change, but blocks have already
    //  been signed in this tenure
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: last_tenure_header.chain_length,
        burn_spent: last_tenure_header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash.clone(),
        parent_block_id: last_tenure_header.parent_block_id.clone(),
        tx_merkle_root: Sha512Trunc256Sum::from_data(&[0]),
        state_index_root: TrieHash([0; 32]),
        timestamp: last_tenure_header.timestamp + 1,
        miner_signature: MessageSignature([0; 65]),
        signer_signature: Vec::new(),
        pox_treatment: BitVec::ones(1).unwrap(),
    };
    sibling_block_header.sign_miner(&miner_sk).unwrap();

    let sibling_block = NakamotoBlock {
        header: sibling_block_header,
        txs: vec![
            StacksTransaction {
                version: TransactionVersion::Testnet,
                chain_id: 1,
                auth: TransactionAuth::Standard(TransactionSpendingCondition::Singlesig(
                    SinglesigSpendingCondition {
                        hash_mode: SinglesigHashMode::P2PKH,
                        signer: Hash160([0; 20]),
                        nonce: 0,
                        tx_fee: 0,
                        key_encoding: TransactionPublicKeyEncoding::Compressed,
                        signature: MessageSignature([0; 65]),
                    },
                )),
                anchor_mode: TransactionAnchorMode::Any,
                post_condition_mode: TransactionPostConditionMode::Allow,
                post_conditions: vec![],
                payload: TransactionPayload::TenureChange(
                    last_tenure.get_tenure_change_tx_payload().unwrap().clone(),
                ),
            },
            last_tenure.txs[1].clone(),
        ],
    };

    assert!(
        !sortitions_view
            .check_proposal(&signer_client, &signer_db, &sibling_block, &miner_pk)
            .unwrap(),
        "A sibling of a previously approved block must be rejected."
    );

    // Case: the block contains a tenure change, but it doesn't confirm all the blocks of the parent tenure
    let reorg_to_block = first_tenure_blocks.as_ref().unwrap().first().unwrap();
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: reorg_to_block.header.chain_length + 1,
        burn_spent: reorg_to_block.header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash.clone(),
        parent_block_id: reorg_to_block.block_id(),
        tx_merkle_root: Sha512Trunc256Sum::from_data(&[0]),
        state_index_root: TrieHash([0; 32]),
        timestamp: last_tenure_header.timestamp + 1,
        miner_signature: MessageSignature([0; 65]),
        signer_signature: Vec::new(),
        pox_treatment: BitVec::ones(1).unwrap(),
    };
    sibling_block_header.sign_miner(&miner_sk).unwrap();

    let sibling_block = NakamotoBlock {
        header: sibling_block_header.clone(),
        txs: vec![
            StacksTransaction {
                version: TransactionVersion::Testnet,
                chain_id: 1,
                auth: TransactionAuth::Standard(TransactionSpendingCondition::Singlesig(
                    SinglesigSpendingCondition {
                        hash_mode: SinglesigHashMode::P2PKH,
                        signer: Hash160([0; 20]),
                        nonce: 0,
                        tx_fee: 0,
                        key_encoding: TransactionPublicKeyEncoding::Compressed,
                        signature: MessageSignature([0; 65]),
                    },
                )),
                anchor_mode: TransactionAnchorMode::Any,
                post_condition_mode: TransactionPostConditionMode::Allow,
                post_conditions: vec![],
                payload: TransactionPayload::TenureChange(TenureChangePayload {
                    tenure_consensus_hash: sibling_block_header.consensus_hash.clone(),
                    prev_tenure_consensus_hash: reorg_to_block.header.consensus_hash.clone(),
                    burn_view_consensus_hash: sibling_block_header.consensus_hash.clone(),
                    previous_tenure_end: reorg_to_block.block_id(),
                    previous_tenure_blocks: 1,
                    cause: stacks::chainstate::stacks::TenureChangeCause::BlockFound,
                    pubkey_hash: Hash160::from_node_public_key(&miner_pk),
                }),
            },
            last_tenure.txs[1].clone(),
        ],
    };

    assert!(
        !sortitions_view
            .check_proposal(&signer_client, &signer_db, &sibling_block, &miner_pk)
            .unwrap(),
        "A sibling of a previously approved block must be rejected."
    );

    // Case: the block contains a tenure change, but the parent tenure is a reorg
    let reorg_to_block = first_tenure_blocks.as_ref().unwrap().last().unwrap();
    // make the sortition_view *think* that our block commit pointed at this old tenure
    sortitions_view.cur_sortition.parent_tenure_id = reorg_to_block.header.consensus_hash.clone();
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: reorg_to_block.header.chain_length + 1,
        burn_spent: reorg_to_block.header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash.clone(),
        parent_block_id: reorg_to_block.block_id(),
        tx_merkle_root: Sha512Trunc256Sum::from_data(&[0]),
        state_index_root: TrieHash([0; 32]),
        timestamp: reorg_to_block.header.timestamp + 1,
        miner_signature: MessageSignature([0; 65]),
        signer_signature: Vec::new(),
        pox_treatment: BitVec::ones(1).unwrap(),
    };
    sibling_block_header.sign_miner(&miner_sk).unwrap();

    let sibling_block = NakamotoBlock {
        header: sibling_block_header.clone(),
        txs: vec![
            StacksTransaction {
                version: TransactionVersion::Testnet,
                chain_id: 1,
                auth: TransactionAuth::Standard(TransactionSpendingCondition::Singlesig(
                    SinglesigSpendingCondition {
                        hash_mode: SinglesigHashMode::P2PKH,
                        signer: Hash160([0; 20]),
                        nonce: 0,
                        tx_fee: 0,
                        key_encoding: TransactionPublicKeyEncoding::Compressed,
                        signature: MessageSignature([0; 65]),
                    },
                )),
                anchor_mode: TransactionAnchorMode::Any,
                post_condition_mode: TransactionPostConditionMode::Allow,
                post_conditions: vec![],
                payload: TransactionPayload::TenureChange(TenureChangePayload {
                    tenure_consensus_hash: sibling_block_header.consensus_hash.clone(),
                    prev_tenure_consensus_hash: reorg_to_block.header.consensus_hash.clone(),
                    burn_view_consensus_hash: sibling_block_header.consensus_hash.clone(),
                    previous_tenure_end: reorg_to_block.block_id(),
                    previous_tenure_blocks: 1,
                    cause: stacks::chainstate::stacks::TenureChangeCause::BlockFound,
                    pubkey_hash: Hash160::from_node_public_key(&miner_pk),
                }),
            },
            last_tenure.txs[1].clone(),
        ],
    };

    assert!(
        !sortitions_view
            .check_proposal(&signer_client, &signer_db, &sibling_block, &miner_pk)
            .unwrap(),
        "A sibling of a previously approved block must be rejected."
    );

    let start_sortition = &reorg_to_block.header.consensus_hash;
    let stop_sortition = &sortitions_view.cur_sortition.prior_sortition;
    // check that the get_tenure_forking_info response is sane
    let fork_info = signer_client
        .get_tenure_forking_info(start_sortition, stop_sortition)
        .unwrap();

    // it should start and stop with the given inputs (reversed!)
    assert_eq!(fork_info.first().unwrap().consensus_hash, *stop_sortition);
    assert_eq!(fork_info.last().unwrap().consensus_hash, *start_sortition);

    // every step of the return should be linked to the parent
    let mut prior: Option<&TenureForkingInfo> = None;
    for step in fork_info.iter().rev() {
        if let Some(ref prior) = prior {
            assert_eq!(prior.sortition_id, step.parent_sortition_id);
        }
        prior = Some(step);
    }

    // view is stale, if we ever expand this test, sortitions_view should
    // be fetched again, so drop it here.
    drop(sortitions_view);

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0, and then switches
///  to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up. It mines a regular Nakamoto tenure
///  before pausing the commit op to produce an empty sortition, forcing a tenure extend.
///  Commit ops are resumed, and an additional 15 nakamoto tenures mined.
/// This test makes three assertions:
///  * 15 blocks are mined after 3.0 starts.
///  * A transaction submitted to the mempool in 3.0 will be mined in 3.0
///  * A tenure extend transaction was successfully mined in 3.0
///  * The final chain tip is a nakamoto block
fn continue_tenure_extend() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = format!("{}:{}", "127.0.0.1", 6000);
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);
    let sender_sk = Secp256k1PrivateKey::new();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        send_amt * 2 + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        naka_skip_commit_op: test_skip_commit_op,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (mut chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    // query for prometheus metrics
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
        assert!(res.contains(&expected_result));
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine a regular nakamoto tenure
    next_block_and_mine_commit(
        &mut btc_regtest_controller,
        60,
        &coord_channel,
        &commits_submitted,
    )
    .unwrap();

    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    info!("Pausing commit ops to trigger a tenure extend.");
    test_skip_commit_op.0.lock().unwrap().replace(true);

    next_block_and(&mut btc_regtest_controller, 60, || Ok(true)).unwrap();

    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    // Submit a TX
    let transfer_tx = make_stacks_transfer(&sender_sk, 0, send_fee, &recipient, send_amt);
    let transfer_tx_hex = format!("0x{}", to_hex(&transfer_tx));

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let mut mempool = naka_conf
        .connect_mempool_db()
        .expect("Database failure opening mempool");

    mempool
        .submit_raw(
            &mut chainstate,
            &sortdb,
            &tip.consensus_hash,
            &tip.anchored_header.block_hash(),
            transfer_tx.clone(),
            &ExecutionCost::max_value(),
            &StacksEpochId::Epoch30,
        )
        .unwrap();

    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    next_block_and(&mut btc_regtest_controller, 60, || Ok(true)).unwrap();

    signer_vote_if_needed(
        &btc_regtest_controller,
        &naka_conf,
        &[sender_signer_sk],
        &signers,
    );

    info!("Resuming commit ops to mine regular tenures.");
    test_skip_commit_op.0.lock().unwrap().replace(false);

    // Mine 15 more regular nakamoto tenures
    for _i in 0..15 {
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        next_block_and(&mut btc_regtest_controller, 60, || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            let blocks_processed = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            Ok(commits_count > commits_before && blocks_processed > blocks_processed_before)
        })
        .unwrap();

        signer_vote_if_needed(
            &btc_regtest_controller,
            &naka_conf,
            &[sender_signer_sk],
            &signers,
        );
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    // assert that the tenure extend tx was observed
    let mut tenure_extends = vec![];
    let mut tenure_block_founds = vec![];
    let mut transfer_tx_included = false;
    for block in test_observer::get_blocks() {
        for tx in block["transactions"].as_array().unwrap() {
            let raw_tx = tx["raw_tx"].as_str().unwrap();
            if raw_tx == &transfer_tx_hex {
                transfer_tx_included = true;
                continue;
            }
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            match &parsed.payload {
                TransactionPayload::TenureChange(payload) => match payload.cause {
                    TenureChangeCause::Extended => tenure_extends.push(parsed),
                    TenureChangeCause::BlockFound => tenure_block_founds.push(parsed),
                },
                _ => {}
            };
        }
    }
    assert!(
        !tenure_extends.is_empty(),
        "Nakamoto node failed to include the tenure extend txs"
    );

    assert!(
        tenure_block_founds.len() >= 17 - tenure_extends.len(),
        "Nakamoto node failed to include the block found tx per winning sortition"
    );

    assert!(
        transfer_tx_included,
        "Nakamoto node failed to include the transfer tx"
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert!(tip.stacks_block_height >= block_height_pre_3_0 + 17);

    // make sure prometheus returns an updated height
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        let expected_result = format!("stacks_node_stacks_tip_height {}", tip.stacks_block_height);
        assert!(res.contains(&expected_result));
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// Verify the timestamps using `get-block-info?`, `get-stacks-block-info?`, and `get-tenure-info?`.
fn check_block_times() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 2,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 =
        "(define-read-only (get-time (height uint)) (get-block-info? time height))";

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract0_name,
        contract_clarity1,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx0);

    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let time0_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(1)],
    );
    let time0 = time0_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    info!("Time from pre-epoch 3.0: {}", time0);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    // This version uses the Clarity 3 functions
    let contract3_name = "test-contract-3";
    let contract_clarity3 =
        "(define-read-only (get-block-time (height uint)) (get-stacks-block-info? time height))
         (define-read-only (get-tenure-time (height uint)) (get-tenure-info? time height))";

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;
    let last_tenure_height = last_stacks_block_height as u128;

    let time0_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time0 = time0_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time1_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time1 = time1_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert_eq!(
        time0, time1,
        "Time from pre- and post-epoch 3.0 contracts should match"
    );

    let time3_tenure_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-time",
        vec![&clarity::vm::Value::UInt(last_tenure_height - 1)],
    );
    let time3_tenure = time3_tenure_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert_eq!(
        time0, time3_tenure,
        "Tenure time should match Clarity 2 block time"
    );

    let time3_block_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time3_block = time3_block_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    sender_nonce += 1;
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;

    let time0a_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time0a = time0a_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert!(
        time0a - time0 >= 1,
        "get-block-info? time should have changed"
    );

    let time1a_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time1a = time1a_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert_eq!(
        time0a, time1a,
        "Time from pre- and post-epoch 3.0 contracts should match"
    );

    let time3a_block_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let time3a_block = time3a_block_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert!(
        time3a_block - time3_block >= 1,
        "get-stacks-block-info? time should have changed"
    );

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    let time0b_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height)],
    );
    let time0b = time0b_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert_eq!(
        time0a, time0b,
        "get-block-info? time should not have changed"
    );

    let time1b_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height)],
    );
    let time1b = time1b_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();
    assert_eq!(
        time0b, time1b,
        "Time from pre- and post-epoch 3.0 contracts should match"
    );

    let time3b_block_value = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-time",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height)],
    );
    let time3b_block = time3b_block_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    assert!(
        time3b_block - time3a_block >= 1,
        "get-stacks-block-info? time should have changed"
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

fn assert_block_info(
    tuple0: &BTreeMap<ClarityName, Value>,
    miner: &Value,
    miner_spend: &clarity::vm::Value,
) {
    assert!(tuple0
        .get("burnchain-header-hash")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());
    assert!(tuple0
        .get("id-header-hash")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());
    assert!(tuple0
        .get("header-hash")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());
    assert_eq!(
        &tuple0
            .get("miner-address")
            .unwrap()
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        miner
    );
    assert!(tuple0
        .get("time")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());
    assert!(tuple0
        .get("vrf-seed")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());
    assert!(tuple0
        .get("block-reward")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_none()); // not yet mature
    assert_eq!(
        &tuple0
            .get("miner-spend-total")
            .unwrap()
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        miner_spend
    );
    assert_eq!(
        &tuple0
            .get("miner-spend-winner")
            .unwrap()
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        miner_spend
    );
}

#[test]
#[ignore]
/// Verify all properties in `get-block-info?`, `get-stacks-block-info?`, and `get-tenure-info?`.
fn check_block_info() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 2,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    let miner = clarity::vm::Value::Principal(
        PrincipalData::parse_standard_principal("ST25WA53N4PWF8XZGQH2J5A4CGCWV4JADPM8MHTRV")
            .unwrap()
            .into(),
    );
    let miner_spend = clarity::vm::Value::UInt(20000);

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 = "(define-read-only (get-info (height uint))
            {
                burnchain-header-hash: (get-block-info? burnchain-header-hash height),
                id-header-hash: (get-block-info? id-header-hash height),
                header-hash: (get-block-info? header-hash height),
                miner-address: (get-block-info? miner-address height),
                time: (get-block-info? time height),
                vrf-seed: (get-block-info? vrf-seed height),
                block-reward: (get-block-info? block-reward height),
                miner-spend-total: (get-block-info? miner-spend-total height),
                miner-spend-winner: (get-block-info? miner-spend-winner height),
            }
        )";

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract0_name,
        contract_clarity1,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx0);

    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(1)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    info!("Info from pre-epoch 3.0: {:?}", tuple0);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    // This version uses the Clarity 3 functions
    let contract3_name = "test-contract-3";
    let contract_clarity3 = "(define-read-only (get-block-info (height uint))
            {
                id-header-hash: (get-stacks-block-info? id-header-hash height),
                header-hash: (get-stacks-block-info? header-hash height),
                time: (get-stacks-block-info? time height),
            }
        )
        (define-read-only (get-tenure-info (height uint))
            {
                burnchain-header-hash: (get-tenure-info? burnchain-header-hash height),
                miner-address: (get-tenure-info? miner-address height),
                time: (get-tenure-info? time height),
                vrf-seed: (get-tenure-info? vrf-seed height),
                block-reward: (get-tenure-info? block-reward height),
                miner-spend-total: (get-tenure-info? miner-spend-total height),
                miner-spend-winner: (get-tenure-info? miner-spend-winner height),
            }
        )";

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    assert_block_info(&tuple0, &miner, &miner_spend);

    let result1 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple1 = result1.expect_tuple().unwrap().data_map;
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_tenure0 = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple3_tenure0.get("burnchain-header-hash"),
        tuple0.get("burnchain-header-hash")
    );
    assert_eq!(
        tuple3_tenure0.get("miner-address"),
        tuple0.get("miner-address")
    );
    assert_eq!(tuple3_tenure0.get("time"), tuple0.get("time"));
    assert_eq!(tuple3_tenure0.get("vrf-seed"), tuple0.get("vrf-seed"));
    assert_eq!(
        tuple3_tenure0.get("block-reward"),
        tuple0.get("block-reward")
    );
    assert_eq!(
        tuple3_tenure0.get("miner-spend-total"),
        tuple0.get("miner-spend-total")
    );
    assert_eq!(
        tuple3_tenure0.get("miner-spend-winner"),
        tuple0.get("miner-spend-winner")
    );

    let result3_block = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_block1 = result3_block.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple3_block1.get("id-header-hash"),
        tuple0.get("id-header-hash")
    );
    assert_eq!(tuple3_block1.get("header-hash"), tuple0.get("header-hash"));
    assert!(tuple3_block1
        .get("time")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    sender_nonce += 1;
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    assert_block_info(&tuple0, &miner, &miner_spend);

    let result1 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple1 = result1.expect_tuple().unwrap().data_map;
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_tenure1 = result3_tenure.expect_tuple().unwrap().data_map;
    // There should have been a tenure change, so these should be different.
    assert_ne!(tuple3_tenure0, tuple3_tenure1);
    assert_eq!(
        tuple3_tenure1.get("burnchain-header-hash"),
        tuple0.get("burnchain-header-hash")
    );
    assert_eq!(
        tuple3_tenure1.get("miner-address"),
        tuple0.get("miner-address")
    );
    assert_eq!(tuple3_tenure1.get("time"), tuple0.get("time"));
    assert_eq!(tuple3_tenure1.get("vrf-seed"), tuple0.get("vrf-seed"));
    assert_eq!(
        tuple3_tenure1.get("block-reward"),
        tuple0.get("block-reward")
    );
    assert_eq!(
        tuple3_tenure1.get("miner-spend-total"),
        tuple0.get("miner-spend-total")
    );
    assert_eq!(
        tuple3_tenure1.get("miner-spend-winner"),
        tuple0.get("miner-spend-winner")
    );

    let result3_block = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_block2 = result3_block.expect_tuple().unwrap().data_map;
    // There should have been a block change, so these should be different.
    assert_ne!(tuple3_block1, tuple3_block2);
    assert_eq!(
        tuple3_block2.get("id-header-hash"),
        tuple0.get("id-header-hash")
    );
    assert_eq!(tuple3_block2.get("header-hash"), tuple0.get("header-hash"));
    assert!(tuple3_block2
        .get("time")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    assert_block_info(&tuple0, &miner, &miner_spend);

    let result1 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple1 = result1.expect_tuple().unwrap().data_map;
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_tenure1a = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(tuple3_tenure1, tuple3_tenure1a);

    let result3_block = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-block-info",
        vec![&clarity::vm::Value::UInt(last_stacks_block_height - 1)],
    );
    let tuple3_block3 = result3_block.expect_tuple().unwrap().data_map;
    // There should have been a block change, so these should be different.
    assert_ne!(tuple3_block3, tuple3_block2);
    assert_eq!(
        tuple3_block3.get("id-header-hash"),
        tuple0.get("id-header-hash")
    );
    assert_eq!(tuple3_block3.get("header-hash"), tuple0.get("header-hash"));
    assert!(tuple3_block3
        .get("time")
        .unwrap()
        .clone()
        .expect_optional()
        .unwrap()
        .is_some());

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

fn get_expected_reward_for_height(blocks: &Vec<serde_json::Value>, block_height: u128) -> u128 {
    // Find the target block
    let target_block = blocks
        .iter()
        .find(|b| b["block_height"].as_u64().unwrap() == block_height as u64)
        .unwrap();

    // Find the tenure change block (the first block with this burn block hash)
    let tenure_burn_block_hash = target_block["burn_block_hash"].as_str().unwrap();
    let tenure_block = blocks
        .iter()
        .find(|b| b["burn_block_hash"].as_str().unwrap() == tenure_burn_block_hash)
        .unwrap();
    let matured_block_hash = tenure_block["block_hash"].as_str().unwrap();

    let mut expected_reward_opt = None;
    for block in blocks.iter().rev() {
        for rewards in block["matured_miner_rewards"].as_array().unwrap() {
            if rewards.as_object().unwrap()["from_stacks_block_hash"]
                .as_str()
                .unwrap()
                == matured_block_hash
            {
                let reward_object = rewards.as_object().unwrap();
                let coinbase_amount: u128 = reward_object["coinbase_amount"]
                    .as_str()
                    .unwrap()
                    .parse()
                    .unwrap();
                let tx_fees_anchored: u128 = reward_object["tx_fees_anchored"]
                    .as_str()
                    .unwrap()
                    .parse()
                    .unwrap();
                let tx_fees_streamed_confirmed: u128 = reward_object["tx_fees_streamed_confirmed"]
                    .as_str()
                    .unwrap()
                    .parse()
                    .unwrap();
                let tx_fees_streamed_produced: u128 = reward_object["tx_fees_streamed_produced"]
                    .as_str()
                    .unwrap()
                    .parse()
                    .unwrap();
                expected_reward_opt = Some(
                    expected_reward_opt.unwrap_or(0)
                        + coinbase_amount
                        + tx_fees_anchored
                        + tx_fees_streamed_confirmed
                        + tx_fees_streamed_produced,
                );
            }
        }

        if let Some(expected_reward) = expected_reward_opt {
            return expected_reward;
        }
    }
    panic!("Expected reward not found");
}

#[test]
#[ignore]
/// Verify `block-reward` property in `get-block-info?` and `get-tenure-info?`.
/// This test is separated from `check_block_info` above because it needs to
/// mine 100+ blocks to mature the block reward, so it is slow.
fn check_block_info_rewards() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 2,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 = "(define-read-only (get-info (height uint))
            {
                burnchain-header-hash: (get-block-info? burnchain-header-hash height),
                id-header-hash: (get-block-info? id-header-hash height),
                header-hash: (get-block-info? header-hash height),
                miner-address: (get-block-info? miner-address height),
                time: (get-block-info? time height),
                vrf-seed: (get-block-info? vrf-seed height),
                block-reward: (get-block-info? block-reward height),
                miner-spend-total: (get-block-info? miner-spend-total height),
                miner-spend-winner: (get-block-info? miner-spend-winner height),
            }
        )";

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract0_name,
        contract_clarity1,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx0);

    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(1)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    info!("Info from pre-epoch 3.0: {:?}", tuple0);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    // This version uses the Clarity 3 functions
    let contract3_name = "test-contract-3";
    let contract_clarity3 = "(define-read-only (get-tenure-info (height uint))
            {
                burnchain-header-hash: (get-tenure-info? burnchain-header-hash height),
                miner-address: (get-tenure-info? miner-address height),
                time: (get-tenure-info? time height),
                vrf-seed: (get-tenure-info? vrf-seed height),
                block-reward: (get-tenure-info? block-reward height),
                miner-spend-total: (get-tenure-info? miner-spend-total height),
                miner-spend-winner: (get-tenure-info? miner-spend-winner height),
            }
        )";

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    sender_nonce += 1;
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    // Sleep to ensure the seconds have changed
    thread::sleep(Duration::from_secs(1));

    // Mine a Nakamoto block
    info!("Mining Nakamoto block");
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    // submit a tx so that the miner will mine an extra block
    let transfer_tx =
        make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
    submit_tx(&http_origin, &transfer_tx);

    loop {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        if blocks_processed > blocks_processed_before {
            break;
        }
        thread::sleep(Duration::from_millis(100));
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;
    let last_nakamoto_block = last_stacks_block_height;

    // Mine more than 2 burn blocks to get the last block's reward matured
    // (only 2 blocks maturation time in tests)
    info!("Mining 6 tenures to mature the block reward");
    for i in 0..6 {
        next_block_and_mine_commit(
            &mut btc_regtest_controller,
            20,
            &coord_channel,
            &commits_submitted,
        )
        .unwrap();
        info!("Mined a block ({i})");
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {:?}", info);
    let last_stacks_block_height = info.stacks_tip_height as u128;
    let blocks = test_observer::get_blocks();

    // Check the block reward is now matured in one of the tenure-change blocks
    let mature_height = last_stacks_block_height - 4;
    let expected_reward = get_expected_reward_for_height(&blocks, mature_height);
    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(mature_height)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple0
            .get("block-reward")
            .unwrap()
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        Value::UInt(expected_reward as u128)
    );

    let result1 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(mature_height)],
    );
    let tuple1 = result1.expect_tuple().unwrap().data_map;
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(mature_height)],
    );
    let tuple3_tenure = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple3_tenure.get("block-reward"),
        tuple0.get("block-reward")
    );

    // Check the block reward is now matured in one of the Nakamoto blocks
    let expected_reward = get_expected_reward_for_height(&blocks, last_nakamoto_block);

    let result0 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract0_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_nakamoto_block)],
    );
    let tuple0 = result0.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple0
            .get("block-reward")
            .unwrap()
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        Value::UInt(expected_reward as u128)
    );

    let result1 = call_read_only(
        &naka_conf,
        &sender_addr,
        contract1_name,
        "get-info",
        vec![&clarity::vm::Value::UInt(last_nakamoto_block)],
    );
    let tuple1 = result1.expect_tuple().unwrap().data_map;
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(last_nakamoto_block)],
    );
    let tuple3_tenure = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(
        tuple3_tenure.get("block-reward"),
        tuple0.get("block-reward")
    );

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Test Nakamoto mock miner by booting a follower node
#[test]
#[ignore]
fn mock_mining() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::new();
    let sender_signer_sk = Secp256k1PrivateKey::new();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk.clone()]);
    let tenure_count = 3;
    let inter_blocks_per_tenure = 3;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;

    let node_1_rpc = 51024;
    let node_1_p2p = 51023;
    let node_2_rpc = 51026;
    let node_2_p2p = 51025;

    let localhost = "127.0.0.1";
    naka_conf.node.rpc_bind = format!("{}:{}", localhost, node_1_rpc);
    naka_conf.node.p2p_bind = format!("{}:{}", localhost, node_1_p2p);
    naka_conf.node.data_url = format!("http://{}:{}", localhost, node_1_rpc);
    naka_conf.node.p2p_address = format!("{}:{}", localhost, node_1_p2p);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr.clone()).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_signer_addr.clone()).to_string(),
        100000,
    );
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    let observer_port = test_observer::EVENT_OBSERVER_PORT;
    naka_conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{observer_port}"),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    btc_regtest_controller.bootstrap_chain(201);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed,
        naka_submitted_commits: commits_submitted,
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    // Wait one block to confirm the VRF register, wait until a block commit is submitted
    wait_for_first_naka_block_commit(60, &commits_submitted);

    let mut follower_conf = naka_conf.clone();
    follower_conf.node.mock_mining = true;
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    follower_conf.node.rpc_bind = format!("{}:{}", localhost, node_2_rpc);
    follower_conf.node.p2p_bind = format!("{}:{}", localhost, node_2_p2p);
    follower_conf.node.data_url = format!("http://{}:{}", localhost, node_2_rpc);
    follower_conf.node.p2p_address = format!("{}:{}", localhost, node_2_p2p);

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        CHAIN_ID_TESTNET,
        PEER_VERSION_TESTNET,
    );

    let mut follower_run_loop = boot_nakamoto::BootRunLoop::new(follower_conf.clone()).unwrap();
    let follower_run_loop_stopper = follower_run_loop.get_termination_switch();
    let follower_coord_channel = follower_run_loop.coordinator_channels();

    let Counters {
        naka_mined_blocks: follower_naka_mined_blocks,
        ..
    } = follower_run_loop.counters();

    let mock_mining_blocks_start = follower_naka_mined_blocks.load(Ordering::SeqCst);

    debug!(
        "Booting follower-thread ({},{})",
        &follower_conf.node.p2p_bind, &follower_conf.node.rpc_bind
    );
    debug!(
        "Booting follower-thread: neighbors = {:?}",
        &follower_conf.node.bootstrap_node
    );

    // spawn a follower thread
    let follower_thread = thread::Builder::new()
        .name("follower-thread".into())
        .spawn(move || follower_run_loop.start(None, 0))
        .unwrap();

    debug!("Booted follower-thread");

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        let follower_naka_mined_blocks_before = follower_naka_mined_blocks.load(Ordering::SeqCst);

        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_tip_height = 0;

        // mine the interim blocks
        for interim_block_ix in 0..inter_blocks_per_tenure {
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            // submit a tx so that the miner will mine an extra block
            let sender_nonce = tenure_ix * inter_blocks_per_tenure + interim_block_ix;
            let transfer_tx =
                make_stacks_transfer(&sender_sk, sender_nonce, send_fee, &recipient, send_amt);
            submit_tx(&http_origin, &transfer_tx);

            loop {
                let blocks_processed = coord_channel
                    .lock()
                    .expect("Mutex poisoned")
                    .get_stacks_blocks_processed();
                if blocks_processed > blocks_processed_before {
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }

            let info = get_chain_info_result(&naka_conf).unwrap();
            assert_ne!(info.stacks_tip, last_tip);
            assert_ne!(info.stacks_tip_height, last_tip_height);

            last_tip = info.stacks_tip;
            last_tip_height = info.stacks_tip_height;
        }

        let mock_miner_timeout = Instant::now();
        while follower_naka_mined_blocks.load(Ordering::SeqCst) <= follower_naka_mined_blocks_before
        {
            if mock_miner_timeout.elapsed() >= Duration::from_secs(60) {
                panic!(
                    "Timed out waiting for mock miner block {}",
                    follower_naka_mined_blocks_before + 1
                );
            }
            thread::sleep(Duration::from_millis(100));
        }

        let start_time = Instant::now();
        while commits_submitted.load(Ordering::SeqCst) <= commits_before {
            if start_time.elapsed() >= Duration::from_secs(20) {
                panic!("Timed out waiting for block-commit");
            }
            thread::sleep(Duration::from_millis(100));
        }
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    let expected_blocks_mined = (inter_blocks_per_tenure + 1) * tenure_count;
    let expected_tip_height = block_height_pre_3_0 + expected_blocks_mined;
    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert_eq!(
        tip.stacks_block_height, expected_tip_height,
        "Should have mined (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    // Check follower's mock miner
    let mock_mining_blocks_end = follower_naka_mined_blocks.load(Ordering::SeqCst);
    let blocks_mock_mined = mock_mining_blocks_end - mock_mining_blocks_start;
    assert_eq!(
        blocks_mock_mined, tenure_count,
        "Should have mock mined `tenure_count` nakamoto blocks"
    );

    // wait for follower to reach the chain tip
    loop {
        sleep_ms(1000);
        let follower_node_info = get_chain_info(&follower_conf);

        info!(
            "Follower tip is now {}/{}",
            &follower_node_info.stacks_tip_consensus_hash, &follower_node_info.stacks_tip
        );
        if follower_node_info.stacks_tip_consensus_hash == tip.consensus_hash
            && follower_node_info.stacks_tip == tip.anchored_header.block_hash()
        {
            break;
        }
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    follower_coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    follower_run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
    follower_thread.join().unwrap();
}
