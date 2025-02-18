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
use std::ops::RangeBounds;
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
use lazy_static::lazy_static;
use libsigner::v0::messages::{RejectReason, SignerMessage as SignerMessageV0};
use libsigner::{SignerSession, StackerDBSession};
use rusqlite::OptionalExtension;
use stacks::burnchains::{MagicBytes, Txid};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::operations::{
    BlockstackOperationType, DelegateStxOp, PreStxOp, StackStxOp, TransferStxOp,
    VoteForAggregateKeyOp,
};
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::chainstate::coordinator::OnChainRewardSetProvider;
use stacks::chainstate::nakamoto::coordinator::{load_nakamoto_reward_set, TEST_COORDINATOR_STALL};
use stacks::chainstate::nakamoto::miner::NakamotoBlockBuilder;
use stacks::chainstate::nakamoto::shadow::shadow_chainstate_repair;
use stacks::chainstate::nakamoto::test_signers::TestSigners;
use stacks::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader, NakamotoChainState};
use stacks::chainstate::stacks::address::{PoxAddress, StacksAddressExtensions};
use stacks::chainstate::stacks::boot::{
    MINERS_NAME, SIGNERS_VOTING_FUNCTION_NAME, SIGNERS_VOTING_NAME,
};
use stacks::chainstate::stacks::db::{StacksChainState, StacksHeaderInfo};
use stacks::chainstate::stacks::miner::{
    BlockBuilder, BlockLimitFunction, TransactionEvent, TransactionResult, TransactionSuccessEvent,
};
use stacks::chainstate::stacks::{
    SinglesigHashMode, SinglesigSpendingCondition, StacksTransaction, TenureChangeCause,
    TenureChangePayload, TransactionAnchorMode, TransactionAuth, TransactionPayload,
    TransactionPostConditionMode, TransactionPublicKeyEncoding, TransactionSpendingCondition,
    TransactionVersion, MAX_BLOCK_LEN,
};
use stacks::config::{EventKeyType, InitialBalance};
use stacks::core::mempool::MAXIMUM_MEMPOOL_TX_CHAINING;
use stacks::core::{
    EpochList, StacksEpoch, StacksEpochId, BLOCK_LIMIT_MAINNET_10, HELIUM_BLOCK_LIMIT_20,
    PEER_VERSION_EPOCH_1_0, PEER_VERSION_EPOCH_2_0, PEER_VERSION_EPOCH_2_05,
    PEER_VERSION_EPOCH_2_1, PEER_VERSION_EPOCH_2_2, PEER_VERSION_EPOCH_2_3, PEER_VERSION_EPOCH_2_4,
    PEER_VERSION_EPOCH_2_5, PEER_VERSION_EPOCH_3_0, PEER_VERSION_EPOCH_3_1, PEER_VERSION_TESTNET,
};
use stacks::libstackerdb::SlotMetadata;
use stacks::net::api::callreadonly::CallReadOnlyRequestBody;
use stacks::net::api::get_tenures_fork_info::TenureForkingInfo;
use stacks::net::api::getsigner::GetSignerResponse;
use stacks::net::api::getstackers::GetStackersResponse;
use stacks::net::api::postblock_proposal::{
    BlockValidateReject, BlockValidateResponse, NakamotoBlockProposal, ValidateRejectCode,
};
use stacks::types::chainstate::{ConsensusHash, StacksBlockId};
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
use stacks_common::types::{set_test_coinbase_schedule, CoinbaseInterval, StacksPublicKeyBuffer};
use stacks_common::util::hash::{to_hex, Hash160, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{MessageSignature, Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks_common::util::{get_epoch_time_secs, sleep_ms};
use stacks_signer::chainstate::{ProposalEvalConfig, SortitionsView};
use stacks_signer::signerdb::{BlockInfo, BlockState, ExtraBlockInfo, SignerDb};
use stacks_signer::v0::SpawnedSigner;

use super::bitcoin_regtest::BitcoinCoreController;
use crate::nakamoto_node::miner::{
    TEST_BLOCK_ANNOUNCE_STALL, TEST_BROADCAST_PROPOSAL_STALL, TEST_MINE_STALL,
    TEST_P2P_BROADCAST_SKIP,
};
use crate::nakamoto_node::relayer::TEST_MINER_THREAD_STALL;
use crate::neon::{Counters, RunLoopCounter};
use crate::operations::BurnchainOpSigner;
use crate::run_loop::boot_nakamoto;
use crate::tests::neon_integrations::{
    call_read_only, get_account, get_account_result, get_chain_info_opt, get_chain_info_result,
    get_neighbors, get_pox_info, next_block_and_wait, run_until_burnchain_height, submit_tx,
    submit_tx_fallible, test_observer, wait_for_runloop,
};
use crate::tests::signer::SignerTest;
use crate::tests::{
    gen_random_port, get_chain_info, make_contract_call, make_contract_publish,
    make_contract_publish_versioned, make_stacks_transfer, to_addr,
};
use crate::{tests, BitcoinRegtestController, BurnchainController, Config, ConfigFile, Keychain};

pub static POX_4_DEFAULT_STACKER_BALANCE: u64 = 100_000_000_000_000;
pub static POX_4_DEFAULT_STACKER_STX_AMT: u128 = 99_000_000_000_000;

lazy_static! {
    pub static ref NAKAMOTO_INTEGRATION_EPOCHS: [StacksEpoch; 10] = [
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: BLOCK_LIMIT_MAINNET_10.clone(),
            network_epoch: PEER_VERSION_EPOCH_1_0
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2,
            end_height: 3,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch22,
            start_height: 3,
            end_height: 4,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_2
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch23,
            start_height: 4,
            end_height: 5,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_3
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch24,
            start_height: 5,
            end_height: 201,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_4
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch25,
            start_height: 201,
            end_height: 231,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_5
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch30,
            start_height: 231,
            end_height: 241,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_3_0
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch31,
            start_height: 241,
            end_height: STACKS_EPOCH_MAX,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_3_1
        },
    ];
}

pub static TEST_SIGNING: Mutex<Option<TestSigningChannel>> = Mutex::new(None);

pub struct TestSigningChannel {
    pub recv: Option<Receiver<Vec<MessageSignature>>>,
    pub send: Sender<Vec<MessageSignature>>,
}

impl TestSigningChannel {
    /// If the integration test has instantiated the singleton TEST_SIGNING channel,
    ///  wait for a signature from the blind-signer.
    /// Returns None if the singleton isn't instantiated and the miner should coordinate
    ///  a real signer set signature.
    /// Panics if the blind-signer times out.
    pub fn get_signature() -> Option<Vec<MessageSignature>> {
        let mut signer = TEST_SIGNING.lock().unwrap();
        let sign_channels = signer.as_mut()?;
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

/// Assert that the block events captured by the test observer
///  all match the miner heuristic of *exclusively* including the
///  tenure change transaction in tenure changing blocks.
pub fn check_nakamoto_empty_block_heuristics() {
    let blocks = test_observer::get_blocks();
    for block in blocks.iter() {
        // if its not a nakamoto block, don't check anything
        if block.get("miner_signature").is_none() {
            continue;
        }
        let txs = test_observer::parse_transactions(block);
        let has_tenure_change = txs.iter().any(|tx| {
            matches!(
                tx.payload,
                TransactionPayload::TenureChange(TenureChangePayload {
                    cause: TenureChangeCause::BlockFound,
                    ..
                })
            )
        });
        if has_tenure_change {
            let only_coinbase_and_tenure_change = txs.iter().all(|tx| {
                matches!(
                    tx.payload,
                    TransactionPayload::TenureChange(_) | TransactionPayload::Coinbase(..)
                )
            });
            assert!(only_coinbase_and_tenure_change, "Nakamoto blocks with a tenure change in them should only have coinbase or tenure changes");
        }
    }
}

pub fn get_stacker_set(http_origin: &str, cycle: u64) -> Result<GetStackersResponse, String> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v3/stacker_set/{cycle}");
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<serde_json::Value>()
        .map_err(|e| format!("{e}"))?;
    info!("Stacker set response: {res}");
    serde_json::from_value(res).map_err(|e| format!("{e}"))
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

pub fn get_last_block_in_current_tenure(
    sortdb: &SortitionDB,
    chainstate: &StacksChainState,
) -> Option<StacksHeaderInfo> {
    let ch = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
        .unwrap()
        .consensus_hash;
    let mut tenure_blocks = test_observer::get_blocks();
    tenure_blocks.retain(|block| {
        let consensus_hash = block.get("consensus_hash").unwrap().as_str().unwrap();
        consensus_hash == format!("0x{ch}")
    });
    let last_block = tenure_blocks.last()?.clone();
    let last_block_id = StacksBlockId::from_hex(
        &last_block
            .get("index_block_hash")
            .unwrap()
            .as_str()
            .unwrap()[2..],
    )
    .unwrap();
    NakamotoChainState::get_block_header(chainstate.db(), &last_block_id).unwrap()
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
            let configs: Vec<&Config> = configs.iter().collect();
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
                    warn!("Expected a block proposal. Got {message:?}");
                    return None;
                };
                block_proposal.block
            };
            Some((proposed_block, miner_addr, miner_ix == latest_miner))
        })
        .collect();

    proposed_blocks.sort_by(|(block_a, _, is_latest_a), (block_b, _, is_latest_b)| {
        let res = block_a
            .header
            .chain_length
            .cmp(&block_b.header.chain_length);
        if res != std::cmp::Ordering::Equal {
            return res;
        }
        // the heights are tied, tie break with the latest miner
        if *is_latest_a {
            return std::cmp::Ordering::Greater;
        }
        if *is_latest_b {
            return std::cmp::Ordering::Less;
        }
        std::cmp::Ordering::Equal
    });

    for (b, _, is_latest) in proposed_blocks.iter() {
        info!("Consider block"; "signer_sighash" => %b.header.signer_signature_hash(), "is_latest_sortition" => is_latest, "chain_height" => b.header.chain_length);
    }

    let Some((proposed_block, miner_addr, _)) = proposed_blocks.pop() else {
        return Err("No block proposals found".into());
    };

    let pubkey = StacksPublicKey::recover_to_pubkey(
        proposed_block.header.miner_signature_hash().as_bytes(),
        &proposed_block.header.miner_signature,
    )
    .map_err(|e| e.to_string())?;
    let miner_signed_addr = StacksAddress::p2pkh(false, &pubkey);
    if miner_signed_addr.bytes() != miner_addr.bytes() {
        return Err(format!(
            "Invalid miner signature on proposal. Found {}, expected {}",
            miner_signed_addr.bytes(),
            miner_addr.bytes()
        ));
    }

    Ok((proposed_block, pubkey))
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
            .block_height_to_reward_cycle(tip.block_height)
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
    Ok(signer_sig_hash)
}

/// Return a working nakamoto-neon config and the miner's bitcoin address to fund
pub fn naka_neon_integration_conf(seed: Option<&[u8]>) -> (Config, StacksAddress) {
    let mut conf = super::new_test_conf();

    conf.burnchain.mode = "nakamoto-neon".into();

    // tests can override this, but these tests run with epoch 2.05 by default
    conf.burnchain.epochs = Some(EpochList::new(&*NAKAMOTO_INTEGRATION_EPOCHS));

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

    conf.burnchain.magic_bytes = MagicBytes::from([b'T', b'3'].as_ref());
    conf.burnchain.poll_time_secs = 1;
    conf.node.pox_sync_sample_secs = 0;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

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
    next_block_and_controller(btc_controller, timeout_secs, |_| check())
}

pub fn next_block_and_controller<F>(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    mut check: F,
) -> Result<(), String>
where
    F: FnMut(&mut BitcoinRegtestController) -> Result<bool, String>,
{
    eprintln!("Issuing bitcoin block");
    btc_controller.build_next_block(1);
    let start = Instant::now();
    while !check(btc_controller)? {
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
        thread::sleep(Duration::from_millis(500));
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
    node_conf: &Config,
    node_counters: &Counters,
) -> Result<(), String> {
    next_block_and_wait_for_commits(
        btc_controller,
        timeout_secs,
        &[node_conf],
        &[node_counters],
        true,
    )
}

/// Mine a bitcoin block, and wait until a block-commit has been issued, **or** a timeout occurs
/// (timeout_secs)
pub fn next_block_and_commits_only(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    node_conf: &Config,
    node_counters: &Counters,
) -> Result<(), String> {
    next_block_and_wait_for_commits(
        btc_controller,
        timeout_secs,
        &[node_conf],
        &[node_counters],
        false,
    )
}

/// Mine a bitcoin block, and wait until:
///  (1) a new block has been processed by the coordinator (if `wait_for_stacks_block` is true)
///  (2) 2 block commits have been issued ** or ** more than 10 seconds have
///      passed since (1) occurred
/// This waits for this check to pass on *all* supplied channels
pub fn next_block_and_wait_for_commits(
    btc_controller: &mut BitcoinRegtestController,
    timeout_secs: u64,
    node_confs: &[&Config],
    node_counters: &[&Counters],
    wait_for_stacks_block: bool,
) -> Result<(), String> {
    let infos_before: Vec<_> = node_confs.iter().map(|c| get_chain_info(c)).collect();
    let burn_ht_before = infos_before
        .iter()
        .map(|info| info.burn_block_height)
        .max()
        .unwrap();
    let stacks_ht_before = infos_before
        .iter()
        .map(|info| info.stacks_tip_height)
        .max()
        .unwrap();
    let last_commit_burn_hts = node_counters
        .iter()
        .map(|c| &c.naka_submitted_commit_last_burn_height);
    let last_commit_stacks_hts = node_counters
        .iter()
        .map(|c| &c.naka_submitted_commit_last_stacks_tip);

    next_block_and(btc_controller, timeout_secs, || {
        let burn_height_committed_to =
            last_commit_burn_hts.clone().all(|last_commit_burn_height| {
                last_commit_burn_height.load(Ordering::SeqCst) > burn_ht_before
            });
        if !wait_for_stacks_block {
            Ok(burn_height_committed_to)
        } else {
            if !burn_height_committed_to {
                return Ok(false);
            }
            let stacks_tip_committed_to =
                last_commit_stacks_hts
                    .clone()
                    .all(|last_commit_stacks_height| {
                        last_commit_stacks_height.load(Ordering::SeqCst) > stacks_ht_before
                    });
            return Ok(stacks_tip_committed_to);
        }
    })
}

pub fn setup_stacker(naka_conf: &mut Config) -> Secp256k1PrivateKey {
    let stacker_sk = Secp256k1PrivateKey::random();
    let stacker_address = tests::to_addr(&stacker_sk);
    naka_conf.add_initial_balance(
        PrincipalData::from(stacker_address).to_string(),
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
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let current_height = btc_regtest_controller.get_headers_height();
    info!(
        "Chain bootstrapped to bitcoin block {current_height:?}, starting Epoch 2x miner";
        "Epoch 3.0 Boundary" => (epoch_3.start_height - 1),
    );
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    // first mined stacks block
    next_block_and_wait(btc_regtest_controller, blocks_processed);

    let start_time = Instant::now();
    loop {
        if start_time.elapsed() > Duration::from_secs(20) {
            panic!("Timed out waiting for the stacks height to increment")
        }
        let stacks_height = get_chain_info(naka_conf).stacks_tip_height;
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
            tests::to_addr(stacker_sk).bytes().clone(),
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            signer_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            naka_conf.burnchain.chain_id,
            12_u128,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = StacksPublicKey::from_private(signer_sk);

        let stacking_tx = tests::make_contract_call(
            stacker_sk,
            0,
            1000,
            naka_conf.burnchain.chain_id,
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

    // the reward set is generally calculated in the first block of the prepare phase hence the + 1
    let reward_set_calculation = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        )
        + 1;

    // Run until the prepare phase
    run_until_burnchain_height(
        btc_regtest_controller,
        blocks_processed,
        reward_set_calculation,
        naka_conf,
    );

    // We need to vote on the aggregate public key if this test is self signing
    if let Some(signers) = self_signing {
        // Get the aggregate key
        let aggregate_key = signers.clone().generate_aggregate_key(reward_cycle + 1);
        let aggregate_public_key = clarity::vm::Value::buff_from(aggregate_key)
            .expect("Failed to serialize aggregate public key");
        let signer_sks_unique: HashMap<_, _> = signer_sks.iter().map(|x| (x.to_hex(), x)).collect();
        wait_for(30, || {
            Ok(get_stacker_set(&http_origin, reward_cycle + 1).is_ok())
        })
        .expect("Timed out waiting for stacker set");
        let signer_set = get_stacker_set(&http_origin, reward_cycle + 1).unwrap();
        // Vote on the aggregate public key
        for signer_sk in signer_sks_unique.values() {
            let signer_index =
                get_signer_index(&signer_set, &Secp256k1PublicKey::from_private(signer_sk))
                    .unwrap();
            let voting_tx = tests::make_contract_call(
                signer_sk,
                0,
                300,
                naka_conf.burnchain.chain_id,
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
        blocks_processed,
        epoch_3.start_height - 1,
        naka_conf,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, Epoch2x miner should stop");
}

/// Boot the chain to just before the Epoch 3.0 boundary to allow for flash blocks
/// This function is similar to `boot_to_epoch_3`, but it stops at epoch 3 start height - 2,
/// allowing for flash blocks to occur when the epoch changes.
///
/// * `stacker_sks` - private keys for sending large `stack-stx` transactions to activate pox-4
/// * `signer_sks` - corresponding signer keys for the stackers
pub fn boot_to_pre_epoch_3_boundary(
    naka_conf: &Config,
    blocks_processed: &Arc<AtomicU64>,
    stacker_sks: &[StacksPrivateKey],
    signer_sks: &[StacksPrivateKey],
    self_signing: &mut Option<&mut TestSigners>,
    btc_regtest_controller: &mut BitcoinRegtestController,
) {
    assert_eq!(stacker_sks.len(), signer_sks.len());

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let current_height = btc_regtest_controller.get_headers_height();
    info!(
        "Chain bootstrapped to bitcoin block {current_height:?}, starting Epoch 2x miner";
        "Epoch 3.0 Boundary" => (epoch_3.start_height - 1),
    );
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    // first mined stacks block
    next_block_and_wait(btc_regtest_controller, blocks_processed);

    let start_time = Instant::now();
    loop {
        if start_time.elapsed() > Duration::from_secs(20) {
            panic!("Timed out waiting for the stacks height to increment")
        }
        let stacks_height = get_chain_info(naka_conf).stacks_tip_height;
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
            tests::to_addr(stacker_sk).bytes().clone(),
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            signer_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            naka_conf.burnchain.chain_id,
            12_u128,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = StacksPublicKey::from_private(signer_sk);

        let stacking_tx = tests::make_contract_call(
            stacker_sk,
            0,
            1000,
            naka_conf.burnchain.chain_id,
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

    // the reward set is generally calculated in the first block of the prepare phase hence the + 1
    let reward_set_calculation = btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .prepare_phase_start(
            btc_regtest_controller.get_burnchain().first_block_height,
            reward_cycle,
        )
        + 1;

    // Run until the prepare phase
    run_until_burnchain_height(
        btc_regtest_controller,
        blocks_processed,
        reward_set_calculation,
        naka_conf,
    );

    // We need to vote on the aggregate public key if this test is self signing
    if let Some(signers) = self_signing {
        // Get the aggregate key
        let aggregate_key = signers.clone().generate_aggregate_key(reward_cycle + 1);
        let aggregate_public_key = clarity::vm::Value::buff_from(aggregate_key)
            .expect("Failed to serialize aggregate public key");
        let signer_sks_unique: HashMap<_, _> = signer_sks.iter().map(|x| (x.to_hex(), x)).collect();
        wait_for(30, || {
            Ok(get_stacker_set(&http_origin, reward_cycle + 1).is_ok())
        })
        .expect("Timed out waiting for stacker set");
        let signer_set = get_stacker_set(&http_origin, reward_cycle + 1).unwrap();
        // Vote on the aggregate public key
        for signer_sk in signer_sks_unique.values() {
            let signer_index =
                get_signer_index(&signer_set, &Secp256k1PublicKey::from_private(signer_sk))
                    .unwrap();
            let voting_tx = tests::make_contract_call(
                signer_sk,
                0,
                300,
                naka_conf.burnchain.chain_id,
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
        blocks_processed,
        epoch_3.start_height - 2,
        naka_conf,
    );

    info!("Bootstrapped to one block before Epoch 3.0 boundary, Epoch 2.x miner should continue for one more block");
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
    let key = get_key_for_cycle(reward_cycle, is_mainnet, http_origin)?;
    Ok(key.is_some())
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
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    next_block_and_wait(btc_regtest_controller, blocks_processed);
    // first mined stacks block
    next_block_and_wait(btc_regtest_controller, blocks_processed);

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
            tests::to_addr(stacker_sk).bytes().clone(),
        );
        let pox_addr_tuple: clarity::vm::Value =
            pox_addr.clone().as_clarity_tuple().unwrap().into();
        let signature = make_pox_4_signer_key_signature(
            &pox_addr,
            signer_sk,
            reward_cycle.into(),
            &Pox4SignatureTopic::StackStx,
            naka_conf.burnchain.chain_id,
            lock_period,
            u128::MAX,
            1,
        )
        .unwrap()
        .to_rsv();

        let signer_pk = StacksPublicKey::from_private(signer_sk);
        let stacking_tx = tests::make_contract_call(
            stacker_sk,
            0,
            1000,
            naka_conf.burnchain.chain_id,
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
    let epoch_3_reward_set_calculation_boundary = epoch_3_reward_cycle_boundary
        .saturating_sub(prepare_phase_len)
        .saturating_add(1);

    run_until_burnchain_height(
        btc_regtest_controller,
        blocks_processed,
        epoch_3_reward_set_calculation_boundary,
        naka_conf,
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
    let epoch_25 = &epochs[StacksEpochId::Epoch25];
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
        blocks_processed,
        epoch_25_start_height,
        naka_conf,
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
    next_block_and_wait(btc_regtest_controller, blocks_processed);
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
            panic!("Timed out waiting for block commit");
        }
        thread::sleep(Duration::from_millis(100));
    }
}

// Check for missing burn blocks in `range`, but allow for a missed block at
// the epoch 3 transition. Panic if any other blocks are missing.
fn check_nakamoto_no_missing_blocks(conf: &Config, range: impl RangeBounds<u64>) {
    let epoch_3 = &conf.burnchain.epochs.as_ref().unwrap()[StacksEpochId::Epoch30];
    let missing = test_observer::get_missing_burn_blocks(range).unwrap();
    let missing_is_error: Vec<_> = missing
        .into_iter()
        .filter(|&i| {
            (i != epoch_3.start_height - 1) || {
                warn!("Missing burn block {} at epoch 3 transition", i);
                false
            }
        })
        .collect();

    if !missing_is_error.is_empty() {
        panic!("Missing the following burn blocks: {missing_is_error:?}");
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
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(5);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt * 2 + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let node_counters = run_loop.counters();

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
        wait_for(10, || {
            let prom_http_origin = format!("http://{prom_bind}");
            let client = reqwest::blocking::Client::new();
            let res = client
                .get(&prom_http_origin)
                .send()
                .unwrap()
                .text()
                .unwrap();
            let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
            Ok(res.contains(&expected_result))
        })
        .expect("Prometheus metrics did not update");
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 15 nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &node_counters)
            .unwrap();
    }

    // Submit a TX
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        0,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
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
            transfer_tx,
            &ExecutionCost::max_value(),
            &StacksEpochId::Epoch30,
        )
        .unwrap();

    wait_for(30, || {
        let transfer_tx_included = test_observer::get_blocks().into_iter().any(|block_json| {
            block_json["transactions"]
                .as_array()
                .unwrap()
                .iter()
                .any(|tx_json| tx_json["raw_tx"].as_str() == Some(&transfer_tx_hex))
        });
        Ok(transfer_tx_included)
    })
    .expect("Timed out waiting for submitted transaction to be included in a block");

    // Mine 15 more nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &node_counters)
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

    // assert that the transfer tx was observed
    let transfer_tx_included = test_observer::get_blocks().into_iter().any(|block_json| {
        block_json["transactions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|tx_json| tx_json["raw_tx"].as_str() == Some(&transfer_tx_hex))
    });

    assert!(
        transfer_tx_included,
        "Nakamoto node failed to include the transfer tx"
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert!(tip.stacks_block_height >= block_height_pre_3_0 + 30);

    // Check that we aren't missing burn blocks (except during the Nakamoto transition)
    let bhh = u64::from(tip.burn_header_height);
    check_nakamoto_no_missing_blocks(&naka_conf, 220..=bhh);

    // make sure prometheus returns an updated number of processed blocks
    #[cfg(feature = "monitoring_prom")]
    {
        wait_for(10, || {
            let prom_http_origin = format!("http://{prom_bind}");
            let client = reqwest::blocking::Client::new();
            let res = client
                .get(&prom_http_origin)
                .send()
                .unwrap()
                .text()
                .unwrap();
            let expected_result_1 = format!(
                "stacks_node_stx_blocks_processed_total {}",
                tip.stacks_block_height
            );

            let expected_result_2 =
                format!("stacks_node_stacks_tip_height {}", tip.stacks_block_height);
            Ok(res.contains(&expected_result_1) && res.contains(&expected_result_2))
        })
        .expect("Prometheus metrics did not update");
    }

    check_nakamoto_empty_block_heuristics();

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

#[test]
#[ignore]
/// Test a scenario in which a miner is restarted right before a tenure
///  which they won. The miner, on restart, should begin mining the new tenure.
fn restarting_miner() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.activated_vrf_key_path =
        Some(format!("{}/vrf_key", naka_conf.node.working_dir));
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(5);
    let sender_sk = Secp256k1PrivateKey::from_seed(&[1, 2, 1, 2, 1, 2]);
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt * 2 + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::from_seed(&[3, 2, 3, 2, 3, 2]);
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let rl1_counters = run_loop.counters();
    let coord_channel = run_loop.coordinator_channels();

    let mut run_loop_2 = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let _run_loop_2_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed: blocks_processed_2,
        naka_proposed_blocks: proposals_submitted_2,
        ..
    } = run_loop_2.counters();
    let rl2_counters = run_loop_2.counters();

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

    let block_height_pre_3_0 =
        NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap()
            .stacks_block_height;

    info!("Nakamoto miner started...");
    blind_signer_multinode(
        &signers,
        &[&naka_conf, &naka_conf],
        vec![proposals_submitted, proposals_submitted_2],
    );

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 2 nakamoto tenures
    for _i in 0..2 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &rl1_counters)
            .unwrap();
    }

    let last_tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => last_tip.stacks_block_height,
        "is_nakamoto" => last_tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    // close the current miner
    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);
    run_loop_thread.join().unwrap();

    // mine a bitcoin block -- this should include a winning commit from
    //  the miner
    btc_regtest_controller.build_next_block(1);

    // start it back up

    let _run_loop_thread = thread::spawn(move || run_loop_2.start(None, 0));
    wait_for_runloop(&blocks_processed_2);

    info!(" ================= RESTARTED THE MINER =================");

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    wait_for(60, || {
        let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap();
        let stacks_tip_committed_to = rl2_counters
            .naka_submitted_commit_last_stacks_tip
            .load(Ordering::SeqCst);
        Ok(tip.stacks_block_height > last_tip.stacks_block_height
            && stacks_tip_committed_to > last_tip.stacks_block_height)
    })
    .unwrap_or_else(|e| {
        let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap();
        error!(
            "Failed to get a new block after restart";
            "last_tip_height" => last_tip.stacks_block_height,
            "latest_tip" => tip.stacks_block_height,
            "error" => &e,
        );

        panic!("{e}")
    });

    // Mine 2 more nakamoto tenures
    for _i in 0..2 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &rl2_counters)
            .unwrap();
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "=== Last tip ===";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());

    // Check that we aren't missing burn blocks
    let bhh = u64::from(tip.burn_header_height);
    // make sure every burn block after the nakamoto transition has a mined
    //  nakamoto block in it.
    let missing = test_observer::get_missing_burn_blocks(220..=bhh).unwrap();

    // This test was flakey because it was sometimes missing burn block 230, which is right at the Nakamoto transition
    // So it was possible to miss a burn block during the transition
    // But I don't it matters at this point since the Nakamoto transition has already happened on mainnet
    // So just print a warning instead, don't count it as an error
    let missing_is_error: Vec<_> = missing
        .into_iter()
        .filter(|i| match i {
            230 => {
                warn!("Missing burn block {i}");
                false
            }
            _ => true,
        })
        .collect();

    if !missing_is_error.is_empty() {
        panic!("Missing the following burn blocks: {missing_is_error:?}");
    }

    check_nakamoto_empty_block_heuristics();

    assert!(tip.stacks_block_height >= block_height_pre_3_0 + 4);
}

#[test]
#[ignore]
#[allow(non_snake_case)]
/// This test spins up a nakamoto-neon node.
/// It starts in Epoch 2.0, mines with `neon_node` to Epoch 3.0,
/// having flash blocks when epoch updates and expects everything to work normally,
/// then switches to Nakamoto operation (activating pox-4 by submitting a stack-stx tx). The BootLoop
///  struct handles the epoch-2/3 tear-down and spin-up.
/// This test makes three assertions:
///  * 30 blocks are mined after 3.0 starts. This is enough to mine across 2 reward cycles
///  * A transaction submitted to the mempool in 3.0 will be mined in 3.0
///  * The final chain tip is a nakamoto block
///
/// NOTE: This test has been disabled because it's flaky, and we don't need to
/// test the Epoch 3 transition since it's already happened
///
/// See issue [#5765](https://github.com/stacks-network/stacks-core/issues/5765) for details
fn flash_blocks_on_epoch_3_FLAKY() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt * 2 + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    wait_for_runloop(&blocks_processed);
    boot_to_pre_epoch_3_boundary(
        &naka_conf,
        &blocks_processed,
        &[stacker_sk],
        &[sender_signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    let block_height_before_mining = tip.block_height;

    // Mine 3 Bitcoin blocks rapidly without waiting for Stacks blocks to be processed.
    // These blocks won't be considered "mined" until the next_block_and_wait call.
    for _i in 0..3 {
        btc_regtest_controller.build_next_block(1);
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

        // Verify that the canonical burn chain tip hasn't advanced yet
        assert_eq!(
            tip.block_height,
            btc_regtest_controller.get_headers_height() - 1
        );
        assert_eq!(tip.block_height, block_height_before_mining);
    }

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    // Mine a new block and wait for it to be processed.
    // This should update the canonical burn chain tip to include all 4 new blocks.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    // Verify that the burn chain tip has advanced by 4 blocks
    assert_eq!(
        tip.block_height,
        block_height_before_mining + 4,
        "Burn chain tip should have advanced by 4 blocks"
    );

    assert_eq!(
        tip.block_height,
        btc_regtest_controller.get_headers_height() - 1
    );

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

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 15 nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
    }

    // Submit a TX
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        0,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
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
            transfer_tx,
            &ExecutionCost::max_value(),
            &StacksEpochId::Epoch30,
        )
        .unwrap();

    // Mine 15 more nakamoto tenures
    for _i in 0..15 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
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
    let transfer_tx_included = test_observer::get_blocks().into_iter().any(|block_json| {
        block_json["transactions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|tx_json| tx_json["raw_tx"].as_str() == Some(&transfer_tx_hex))
    });

    assert!(
        transfer_tx_included,
        "Nakamoto node failed to include the transfer tx"
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());
    assert!(tip.stacks_block_height >= block_height_pre_3_0 + 30);

    // Check that we have the expected burn blocks
    // We expect to have around the blocks 220-230 and 234 onwards, with a gap of 3 blocks for the flash blocks
    let bhh = u64::from(tip.burn_header_height);

    // Get the Epoch 3.0 activation height (in terms of Bitcoin block height)
    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let epoch_3_start_height = epoch_3.start_height;

    // Find the gap in burn blocks
    let mut gap_start = 0;
    let mut gap_end = 0;
    for i in 220..=bhh {
        if test_observer::contains_burn_block_range(i..=i).is_err() {
            if gap_start == 0 {
                gap_start = i;
            }
            gap_end = i;
        } else if gap_start != 0 {
            break;
        }
    }

    // Verify that there's a gap of AT LEAST 3 blocks
    assert!(
        gap_end - gap_start + 1 >= 3,
        "Expected a gap of AT LEAST 3 burn blocks due to flash blocks, found gap from {gap_start} to {gap_end}"
    );

    // Verify that the gap includes the Epoch 3.0 activation height
    assert!(
        gap_start <= epoch_3_start_height && epoch_3_start_height <= gap_end,
        "Expected the gap ({gap_start}..={gap_end}) to include the Epoch 3.0 activation height ({epoch_3_start_height})"
    );

    // Verify blocks before and after the gap
    test_observer::contains_burn_block_range(220..=(gap_start - 1)).unwrap();
    test_observer::contains_burn_block_range((gap_end + 1)..=bhh).unwrap();
    check_nakamoto_empty_block_heuristics();

    info!("Verified burn block ranges, including expected gap for flash blocks");
    info!("Confirmed that the gap includes the Epoch 3.0 activation height (Bitcoin block height): {epoch_3_start_height}");

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
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
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
        debug!("Mining tenure {tenure_ix}");
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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
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

    check_nakamoto_empty_block_heuristics();

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
    naka_conf.node.pox_sync_sample_secs = 30;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 15;
    let inter_blocks_per_tenure = 6;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    let mut conf_node_2 = naka_conf.clone();
    let localhost = "127.0.0.1";
    conf_node_2.node.rpc_bind = format!("{localhost}:{node_2_rpc}");
    conf_node_2.node.p2p_bind = format!("{localhost}:{node_2_p2p}");
    conf_node_2.node.data_url = format!("http://{localhost}:{node_2_rpc}");
    conf_node_2.node.p2p_address = format!("{localhost}:{node_2_p2p}");
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

    conf_node_2.node.working_dir = format!("{}-1", conf_node_2.node.working_dir);

    conf_node_2.node.set_bootstrap_nodes(
        format!("{}@{}", &node_1_pk.to_hex(), naka_conf.node.p2p_bind),
        naka_conf.burnchain.chain_id,
        naka_conf.burnchain.peer_version,
    );

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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

    let mut signers = TestSigners::new(vec![sender_signer_sk]);
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
        info!("Mining tenure {tenure_ix}");
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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
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

    check_nakamoto_empty_block_heuristics();

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
        epochs[StacksEpochId::Epoch24].end_height = 208;
        epochs[StacksEpochId::Epoch25].start_height = 208;
        epochs[StacksEpochId::Epoch25].end_height = 225;
        epochs[StacksEpochId::Epoch30].start_height = 225;
    }

    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
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
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);

    let signers = TestSigners::new(vec![sender_signer_sk]);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let epochs = naka_conf.burnchain.epochs.clone().unwrap();
    let epoch_3 = &epochs[StacksEpochId::Epoch30];
    let epoch_25 = &epochs[StacksEpochId::Epoch25];
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
    let stacker_accounts_copy = stacker_accounts;
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
                tests::to_addr(account.0).bytes().clone(),
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
                naka_conf.burnchain.chain_id,
                1_u128,
                u128::MAX,
                1,
            )
            .unwrap()
            .to_rsv();

            let stacking_tx = tests::make_contract_call(
                account.0,
                account.2.nonce,
                1000,
                naka_conf.burnchain.chain_id,
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

    info!("first_epoch_3_cycle: {first_epoch_3_cycle:?}");

    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let stacker_response = get_stacker_set(&http_origin, first_epoch_3_cycle).unwrap();
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
        if let Err(e) =
            next_block_and_mine_commit(&mut btc_regtest_controller, 30, &naka_conf, &counters)
        {
            panic!(
                "Error while minting a bitcoin block and waiting for stacks-node activity: {e:?}"
            );
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

    let mut last_block_time = None;
    for block in new_blocks_with_reward_set.iter() {
        if let Some(block_time) = block["block_time"].as_u64() {
            if let Some(last) = last_block_time {
                assert!(block_time > last, "Block times should be increasing");
            }
            last_block_time = Some(block_time);
        }
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

    check_nakamoto_empty_block_heuristics();

    run_loop_thread.join().unwrap();
}

/// Test `/v3/block_proposal` API endpoint
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
    conf.connection_options.auth_token = Some(password.clone());
    let account_keys = add_initial_balances(&mut conf, 10, 1_000_000);
    let stacker_sk = setup_stacker(&mut conf);
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);

    // only subscribe to the block proposal events
    test_observer::spawn();
    test_observer::register(&mut conf, &[EventKeyType::BlockProposal]);

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
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
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
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &conf, &counters).unwrap();
    }

    // TODO (hack) instantiate the sortdb in the burnchain
    _ = btc_regtest_controller.sortdb_mut();

    // ----- Setup boilerplate finished, test block proposal API endpoint -----

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let privk = conf.miner.mining_key.unwrap();
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
            None,
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
            conf.burnchain.chain_id,
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
    const HTTP_UNPROCESSABLE: u16 = 422;
    let test_cases = [
        (
            "Valid Nakamoto block proposal",
            sign(&proposal),
            HTTP_ACCEPTED,
            Some(Ok(())),
        ),
        ("Must wait", sign(&proposal), HTTP_TOO_MANY, None),
        (
            "Non-canonical or absent tenure",
            {
                let mut sp = sign(&proposal);
                sp.block.header.consensus_hash.0[3] ^= 0x07;
                sp
            },
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::NonCanonicalTenure)),
        ),
        (
            "Corrupted (bit flipped after signing)",
            {
                let mut sp = sign(&proposal);
                sp.block.header.timestamp ^= 0x07;
                sp
            },
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::ChainstateError)),
        ),
        (
            "Invalid `chain_id`",
            {
                let mut p = proposal.clone();
                p.chain_id ^= 0xFFFFFFFF;
                sign(&p)
            },
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::InvalidBlock)),
        ),
        (
            "Invalid `miner_signature`",
            {
                let mut sp = sign(&proposal);
                sp.block.header.miner_signature.0[1] ^= 0x80;
                sp
            },
            HTTP_ACCEPTED,
            Some(Err(ValidateRejectCode::ChainstateError)),
        ),
        ("Not authorized", sign(&proposal), HTTP_NOT_AUTHORIZED, None),
        (
            "Unprocessable entity",
            {
                let mut p = proposal.clone();
                p.block.header.timestamp = 0;
                sign(&p)
            },
            HTTP_UNPROCESSABLE,
            None,
        ),
    ];

    // Build HTTP client
    let client = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(60))
        .build()
        .expect("Failed to build `reqwest::Client`");
    // Build URL
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let path = format!("{http_origin}/v3/block_proposal");

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
            assert!(
                start_time.elapsed() <= Duration::from_secs(30),
                "Took over 30 seconds to process pending proposal, panicking test"
            );
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
            _ = hold_proposal_mutex.take();
        }
    }

    let expected_proposal_responses: Vec<_> = test_cases
        .iter()
        .filter_map(|(_, _, _, expected_response)| expected_response.as_ref())
        .collect();

    let mut proposal_responses = test_observer::get_proposal_responses();
    let start_time = Instant::now();
    while proposal_responses.len() < expected_proposal_responses.len() {
        assert!(
            start_time.elapsed() <= Duration::from_secs(30),
            "Took over 30 seconds to process pending proposal, panicking test"
        );
        info!("Waiting for prior request to finish processing");
        thread::sleep(Duration::from_secs(5));
        proposal_responses = test_observer::get_proposal_responses();
    }

    for (expected_response, response) in expected_proposal_responses
        .iter()
        .zip(proposal_responses.iter())
    {
        info!("Received response {response:?}, expecting {expected_response:?}");
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
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 100;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt + send_fee,
    );
    let stacker_sk = setup_stacker(&mut naka_conf);

    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);

    let mut signers = TestSigners::new(vec![sender_signer_sk]);

    test_observer::spawn();
    test_observer::register(
        &mut naka_conf,
        &[EventKeyType::AnyEvent, EventKeyType::MinedBlocks],
    );

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
    let counters = run_loop.counters();

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
    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

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
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);

    let mut signers = TestSigners::new(vec![signer_sk]);

    naka_conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

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
        output: signer_addr,
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
            .is_ok(),
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
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
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
    let aggregate_key = signer_key;

    let vote_for_aggregate_key_op =
        BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
            signer_key,
            signer_index,
            sender: signer_addr,
            round: 0,
            reward_cycle,
            aggregate_key,
            // to be filled in
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        });

    let mut signer_burnop_signer = BurnchainOpSigner::new(signer_sk, false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                vote_for_aggregate_key_op,
                &mut signer_burnop_signer,
                1
            )
            .is_ok(),
        "Vote for aggregate key operation should submit successfully"
    );

    info!("Submitted vote for aggregate key op at height {block_height}, mining a few blocks...");

    // the second block should process the vote, after which the vote should be set
    for _i in 0..2 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
    }

    let mut vote_for_aggregate_key_found = false;
    let blocks = test_observer::get_blocks();
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                info!("Found a burn op: {tx:?}");
                let burnchain_op = tx.get("burnchain_op").unwrap().as_object().unwrap();
                if !burnchain_op.contains_key("vote_for_aggregate_key") {
                    warn!("Got unexpected burnchain op: {burnchain_op:?}");
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
fn follower_bootup_simple() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    follower_conf.node.miner = false;
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    let rpc_port = gen_random_port();
    let p2p_port = gen_random_port();

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{localhost}:{rpc_port}");
    follower_conf.node.p2p_bind = format!("{localhost}:{p2p_port}");
    follower_conf.node.data_url = format!("http://{localhost}:{rpc_port}");
    follower_conf.node.p2p_address = format!("{localhost}:{p2p_port}");
    follower_conf.node.pox_sync_sample_secs = 30;

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        naka_conf.burnchain.chain_id,
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
        debug!("follower_bootup: Miner runs tenure {tenure_ix}");
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_nonce = None;

        debug!("follower_bootup: Miner mines interum blocks for tenure {tenure_ix}");

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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            submit_tx(&http_origin, &transfer_tx);

            last_nonce = Some(sender_nonce);

            let tx = StacksTransaction::consensus_deserialize(&mut &transfer_tx[..]).unwrap();

            debug!("follower_bootup: Miner account: {account:?}");
            debug!("follower_bootup: Miner sent {}: {tx:?}", &tx.txid());

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

/// This test boots a follower node using the block downloader, but the follower will be multiple
/// Nakamoto reward cycles behind.
#[test]
#[ignore]
fn follower_bootup_across_multiple_cycles() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    naka_conf.node.pox_sync_sample_secs = 180;
    naka_conf.burnchain.max_rbf = 10_000_000;

    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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

    // mine two reward cycles
    for _ in 0..btc_regtest_controller
        .get_burnchain()
        .pox_constants
        .reward_cycle_length
        * 2
    {
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();
        wait_for(20, || {
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap();
    }

    info!("Nakamoto miner has advanced two reward cycles");

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
        "block_height_pre_3_0" => block_height_pre_3_0
    );

    assert!(tip.anchored_header.as_stacks_nakamoto().is_some());

    // spawn follower
    let mut follower_conf = naka_conf.clone();
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];
    follower_conf.node.miner = false;

    let rpc_port = gen_random_port();
    let p2p_port = gen_random_port();

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{localhost}:{rpc_port}");
    follower_conf.node.p2p_bind = format!("{localhost}:{p2p_port}");
    follower_conf.node.data_url = format!("http://{localhost}:{rpc_port}");
    follower_conf.node.p2p_address = format!("{localhost}:{p2p_port}");

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        naka_conf.burnchain.chain_id,
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

    // Wait a long time for the follower to catch up because CI is slow.
    wait_for(600, || {
        sleep_ms(1000);
        let Ok(follower_node_info) = get_chain_info_result(&follower_conf) else {
            return Ok(false);
        };

        info!(
            "Follower tip is now {}/{}",
            &follower_node_info.stacks_tip_consensus_hash, &follower_node_info.stacks_tip
        );
        Ok(
            follower_node_info.stacks_tip_consensus_hash == tip.consensus_hash
                && follower_node_info.stacks_tip == tip.anchored_header.block_hash(),
        )
    })
    .unwrap();

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

/// Boot up a node and a follower with a non-default chain id
#[test]
#[ignore]
fn follower_bootup_custom_chain_id() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.burnchain.chain_id = 0x87654321;
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    follower_conf.node.miner = false;
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    let rpc_port = gen_random_port();
    let p2p_port = gen_random_port();

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{localhost}:{rpc_port}");
    follower_conf.node.p2p_bind = format!("{localhost}:{p2p_port}");
    follower_conf.node.data_url = format!("http://{localhost}:{rpc_port}");
    follower_conf.node.p2p_address = format!("{localhost}:{p2p_port}");
    follower_conf.node.pox_sync_sample_secs = 30;

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        naka_conf.burnchain.chain_id,
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
        debug!("follower_bootup: Miner runs tenure {tenure_ix}");
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        let mut last_tip = BlockHeaderHash([0x00; 32]);
        let mut last_nonce = None;

        debug!("follower_bootup: Miner mines interum blocks for tenure {tenure_ix}");

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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            submit_tx(&http_origin, &transfer_tx);

            last_nonce = Some(sender_nonce);

            let tx = StacksTransaction::consensus_deserialize(&mut &transfer_tx[..]).unwrap();

            debug!("follower_bootup: Miner account: {account:?}");
            debug!("follower_bootup: Miner sent {}: {tx:?}", &tx.txid());

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

    // Verify both nodes have the correct chain id
    let miner_info = get_chain_info(&naka_conf);
    assert_eq!(miner_info.network_id, 0x87654321);

    let follower_info = get_chain_info(&follower_conf);
    assert_eq!(follower_info.network_id, 0x87654321);

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
/// Test out various burn operations being processed in Nakamoto.
///
/// There are 4 burn ops submitted:
///
/// - stx-transfer
/// - delegate-stx
/// - stack-stx
///
/// Additionally, a stack-stx without a signer key is submitted, which should
/// not be processed in Nakamoto.
fn burn_ops_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.burnchain.satoshis_per_byte = 2;
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);

    let signer_sk_1 = setup_stacker(&mut naka_conf);
    let signer_addr_1 = tests::to_addr(&signer_sk_1);

    let signer_sk_2 = Secp256k1PrivateKey::random();
    let signer_addr_2 = tests::to_addr(&signer_sk_2);

    let stacker_sk_1 = Secp256k1PrivateKey::random();
    let stacker_addr_1 = tests::to_addr(&stacker_sk_1);

    let stacker_sk_2 = Secp256k1PrivateKey::random();
    let stacker_addr_2 = tests::to_addr(&stacker_sk_2);

    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    let mut sender_nonce = 0;

    let mut signers = TestSigners::new(vec![signer_sk_1]);

    let stacker_sk = setup_stacker(&mut naka_conf);

    // Add the initial balances to the other accounts
    naka_conf.add_initial_balance(PrincipalData::from(stacker_addr_1).to_string(), 1000000);
    naka_conf.add_initial_balance(PrincipalData::from(stacker_addr_2).to_string(), 1000000);
    naka_conf.add_initial_balance(PrincipalData::from(sender_addr).to_string(), 100_000_000);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

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
        output: signer_addr_1,
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
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    let mut miner_signer_2 = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();
    info!("Submitting second pre-stx op");
    let pre_stx_op_2 = PreStxOp {
        output: signer_addr_2,
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
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    let mut miner_signer_3 = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();
    info!("Submitting third pre-stx op");
    let pre_stx_op_3 = PreStxOp {
        output: stacker_addr_1,
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::PreStx(pre_stx_op_3),
                &mut miner_signer_3,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    info!("Submitting fourth pre-stx op");
    let mut miner_signer_4 = Keychain::default(naka_conf.node.seed.clone()).generate_op_signer();
    let pre_stx_op_4 = PreStxOp {
        output: stacker_addr_2,
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::PreStx(pre_stx_op_4),
                &mut miner_signer_4,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );
    info!("Submitted 4 pre-stx ops at block {block_height}, mining a few blocks...");

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
        naka_conf.burnchain.chain_id,
        &StacksAddress::burn_address(false),
        "pox-4",
        "set-signer-key-authorization",
        &[
            clarity::vm::Value::Tuple(pox_addr.as_clarity_tuple().unwrap()),
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
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
    }

    let reward_cycle = reward_cycle + 1;

    info!(
        "Submitting stack stx op";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
    );

    let mut signer_burnop_signer_1 = BurnchainOpSigner::new(signer_sk_1, false);
    let mut signer_burnop_signer_2 = BurnchainOpSigner::new(signer_sk_2, false);
    let mut stacker_burnop_signer_1 = BurnchainOpSigner::new(stacker_sk_1, false);
    let mut stacker_burnop_signer_2 = BurnchainOpSigner::new(stacker_sk_2, false);

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

    info!("Submitting transfer STX op");
    let transfer_stx_op = TransferStxOp {
        sender: stacker_addr_1,
        recipient: stacker_addr_2,
        transfered_ustx: 10000,
        memo: vec![],
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::TransferStx(transfer_stx_op),
                &mut stacker_burnop_signer_1,
                1
            )
            .is_ok(),
        "Transfer STX operation should submit successfully"
    );

    info!("Submitting delegate STX op");
    let del_stx_op = DelegateStxOp {
        sender: stacker_addr_2,
        delegate_to: stacker_addr_1,
        reward_addr: None,
        delegated_ustx: 100_000,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
        until_burn_height: None,
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch30,
                BlockstackOperationType::DelegateStx(del_stx_op),
                &mut stacker_burnop_signer_2,
                1
            )
            .is_ok(),
        "Delegate STX operation should submit successfully"
    );

    let pox_info = get_pox_info(&http_origin).unwrap();
    let min_stx = pox_info.next_cycle.min_threshold_ustx;

    let stack_stx_op_with_some_signer_key = StackStxOp {
        sender: signer_addr_1,
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
            .is_ok(),
        "Stack STX operation should submit successfully"
    );

    let stack_stx_op_with_no_signer_key = StackStxOp {
        sender: signer_addr_2,
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
            .is_ok(),
        "Stack STX operation should submit successfully"
    );

    info!("Submitted 2 stack STX ops at height {block_height}, mining a few blocks...");

    // the second block should process the ops
    // Also mine 2 interim blocks to ensure the stack-stx ops are not processed in them
    for _i in 0..2 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
        for interim_block_ix in 0..2 {
            info!("Mining interim block {interim_block_ix}");
            let blocks_processed_before = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            // submit a tx so that the miner will mine an extra block
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                200,
                naka_conf.burnchain.chain_id,
                &stacker_addr_1.into(),
                10000,
            );
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
        }
    }

    let mut stack_stx_found = false;
    let mut transfer_stx_found = false;
    let mut delegate_stx_found = false;
    let mut stack_stx_burn_op_tx_count = 0;
    let blocks = test_observer::get_blocks();
    info!("stack event observer num blocks: {:?}", blocks.len());
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        info!(
            "stack event observer num transactions: {:?}",
            transactions.len()
        );
        let mut block_has_tenure_change = false;
        for tx in transactions.iter().rev() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                info!("Found a burn op: {tx:?}");
                assert!(block_has_tenure_change, "Block should have a tenure change");
                let burnchain_op = tx.get("burnchain_op").unwrap().as_object().unwrap();
                if burnchain_op.contains_key("transfer_stx") {
                    let transfer_stx_obj = burnchain_op.get("transfer_stx").unwrap();
                    let sender_obj = transfer_stx_obj.get("sender").unwrap();
                    let sender = sender_obj.get("address").unwrap().as_str().unwrap();
                    let recipient_obj = transfer_stx_obj.get("recipient").unwrap();
                    let recipient = recipient_obj.get("address").unwrap().as_str().unwrap();
                    let transfered_ustx = transfer_stx_obj
                        .get("transfered_ustx")
                        .unwrap()
                        .as_u64()
                        .unwrap();
                    assert_eq!(sender, stacker_addr_1.to_string());
                    assert_eq!(recipient, stacker_addr_2.to_string());
                    assert_eq!(transfered_ustx, 10000);
                    info!(
                        "Transfer STX op: sender: {sender}, recipient: {recipient}, transfered_ustx: {transfered_ustx}"
                    );
                    assert!(!transfer_stx_found, "Transfer STX op should be unique");
                    transfer_stx_found = true;
                    continue;
                }
                if burnchain_op.contains_key("delegate_stx") {
                    info!("Got delegate STX op: {burnchain_op:?}");
                    let delegate_stx_obj = burnchain_op.get("delegate_stx").unwrap();
                    let sender_obj = delegate_stx_obj.get("sender").unwrap();
                    let sender = sender_obj.get("address").unwrap().as_str().unwrap();
                    let delegate_to_obj = delegate_stx_obj.get("delegate_to").unwrap();
                    let delegate_to = delegate_to_obj.get("address").unwrap().as_str().unwrap();
                    let delegated_ustx = delegate_stx_obj
                        .get("delegated_ustx")
                        .unwrap()
                        .as_u64()
                        .unwrap();
                    assert_eq!(sender, stacker_addr_2.to_string());
                    assert_eq!(delegate_to, stacker_addr_1.to_string());
                    assert_eq!(delegated_ustx, 100_000);
                    assert!(!delegate_stx_found, "Delegate STX op should be unique");
                    delegate_stx_found = true;
                    continue;
                }
                if !burnchain_op.contains_key("stack_stx") {
                    warn!("Got unexpected burnchain op: {burnchain_op:?}");
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

                assert!(!stack_stx_found, "Stack STX op should be unique");
                stack_stx_found = true;
                stack_stx_burn_op_tx_count += 1;
            } else {
                let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
                let parsed =
                    StacksTransaction::consensus_deserialize(&mut tx_bytes.as_slice()).unwrap();
                if let TransactionPayload::TenureChange(_tenure_change) = parsed.payload {
                    block_has_tenure_change = true;
                }
            }
        }
    }
    assert!(stack_stx_found, "Expected stack STX op");
    assert_eq!(
        stack_stx_burn_op_tx_count, 1,
        "Stack-stx tx without a signer_key shouldn't have been submitted"
    );
    assert!(transfer_stx_found, "Expected transfer STX op");

    assert!(delegate_stx_found, "Expected delegate STX op");
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
            debug!("Stacking op queried from sortdb: {stacking_op:?}");
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
    naka_conf.miner.block_commit_delay = Duration::from_secs(0);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt + send_fee,
    );
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    test_observer::spawn();
    test_observer::register(
        &mut naka_conf,
        &[EventKeyType::AnyEvent, EventKeyType::MinedBlocks],
    );

    let miner_sk = naka_conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);

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

    info!("Starting Tenure A.");
    wait_for_first_naka_block_commit(60, &commits_submitted);

    // In the next block, the miner should win the tenure and submit a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(commits_count > commits_before + 1
            && blocks_count > blocks_before
            && blocks_processed > blocks_processed_before)
    })
    .unwrap();

    let block_tenure_a = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    info!("Tenure A block: {}", &block_tenure_a.index_block_hash());

    // For the next tenure, submit the commit op but do not allow any stacks blocks to be broadcasted.
    // Stall the miner thread; only wait until the number of submitted commits increases.
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![miner_pk]);
    TEST_BLOCK_ANNOUNCE_STALL.set(true);

    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let commits_before = commits_submitted.load(Ordering::SeqCst);

    info!("Starting Tenure B.");

    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        Ok(commits_count > commits_before)
    })
    .unwrap();

    info!("Commit op is submitted; unpause Tenure B's block");

    // Unpause the broadcast of Tenure B's block, do not submit commits, and do not allow blocks to
    // be processed
    test_skip_commit_op.set(true);
    TEST_BROADCAST_PROPOSAL_STALL.set(vec![]);

    // Wait for a stacks block to be broadcasted.
    // However, it will not be processed.
    let start_time = Instant::now();
    while mined_blocks.load(Ordering::SeqCst) <= blocks_before {
        assert!(
            start_time.elapsed() < Duration::from_secs(30),
            "FAIL: Test timed out while waiting for block production",
        );
        thread::sleep(Duration::from_secs(1));
    }

    info!("Tenure B broadcasted but did not process a block. Issue the next bitcoin block and unstall block commits.");

    // the block will be stored, not processed, so load it out of staging
    let tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
        .expect("Failed to get sortition tip");

    let block_tenure_b = chainstate
        .nakamoto_blocks_db()
        .get_nakamoto_tenure_start_blocks(&tip_sn.consensus_hash)
        .unwrap()
        .first()
        .cloned()
        .unwrap();

    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_b = blocks.last().unwrap();
    info!("Tenure B tip block: {}", &block_tenure_b.block_id());
    info!("Tenure B last block: {}", &block_b.block_id);

    // Block B was built atop block A
    assert_eq!(
        block_tenure_b.header.chain_length,
        block_tenure_a.stacks_block_height + 1
    );

    info!("Starting Tenure C.");

    // force the timestamp to be different
    sleep_ms(2000);

    // Submit a block commit op for tenure C.
    // It should also build on block A, since the node has paused processing of block B.
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    next_block_and(&mut btc_regtest_controller, 60, || {
        test_skip_commit_op.set(false);
        TEST_BLOCK_ANNOUNCE_STALL.set(false);
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        let block_in_tenure = get_last_block_in_current_tenure(&sortdb, &chainstate).is_some();
        Ok(commits_count > commits_before
            && blocks_count > blocks_before
            && blocks_processed > blocks_processed_before
            && block_in_tenure)
    })
    .unwrap();

    info!("Tenure C produced a block!");

    let block_tenure_c = get_last_block_in_current_tenure(&sortdb, &chainstate).unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_c = blocks.last().unwrap();
    info!("Tenure C tip block: {}", &block_tenure_c.index_block_hash());
    info!("Tenure C last block: {}", &block_c.block_id);
    assert_ne!(block_tenure_b.block_id(), block_tenure_c.index_block_hash());

    // Block C was built AFTER Block B was built, but BEFORE it was broadcasted (processed), so it should be built off of Block A
    assert_eq!(
        block_tenure_c.stacks_block_height,
        block_tenure_a.stacks_block_height + 1
    );

    // Now let's produce a second block for tenure C and ensure it builds off of block C.
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
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

    wait_for(10, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_processed > blocks_processed_before)
    })
    .unwrap();

    info!("Tenure C produced a second block!");

    let block_2_tenure_c = get_last_block_in_current_tenure(&sortdb, &chainstate).unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_2_c = blocks.last().unwrap();

    info!(
        "Tenure C tip block: {}",
        &block_2_tenure_c.index_block_hash()
    );
    info!("Tenure C last block: {}", &block_2_c.block_id);

    info!("Starting tenure D.");
    // Submit a block commit op for tenure D and mine a stacks block
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    next_block_and(&mut btc_regtest_controller, 60, || {
        let commits_count = commits_submitted.load(Ordering::SeqCst);
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(commits_count > commits_before
            && blocks_count > blocks_before
            && blocks_processed > blocks_processed_before)
    })
    .unwrap();

    let block_tenure_d = get_last_block_in_current_tenure(&sortdb, &chainstate).unwrap();
    let blocks = test_observer::get_mined_nakamoto_blocks();
    let block_d = blocks.last().unwrap();

    info!("Tenure D tip block: {}", block_tenure_d.index_block_hash());
    info!("Tenure D last block: {}", block_d.block_id);

    assert_ne!(block_tenure_b.block_id(), block_tenure_a.index_block_hash());
    assert_ne!(block_tenure_b.block_id(), block_tenure_c.index_block_hash());
    assert_ne!(block_tenure_c, block_tenure_a);

    // Block B was built atop block A
    assert_eq!(
        block_tenure_b.header.chain_length,
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
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
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
        PrincipalData::from(sender_addr).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    naka_conf.miner.tenure_cost_limit_per_block_percentage = None;
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
        naka_conf.burnchain.chain_id,
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
    info!("Heights from pre-epoch 3.0: {preheights}");

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {info:?}");

    // With the first Nakamoto block, the chain tip and the number of tenures
    // must be the same (before Nakamoto every block counts as a tenure)
    assert_eq!(info.tenure_height, info.stacks_tip_height);

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
    info!("Heights from epoch 3.0 start: {heights0}");
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
        naka_conf.burnchain.chain_id,
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
        naka_conf.burnchain.chain_id,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {tenure_ix}");
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();

        // in the first tenure, make sure that the contracts are published
        if tenure_ix == 0 {
            wait_for(30, || {
                let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
                Ok(cur_sender_nonce >= sender_nonce)
            })
            .expect("Timed out waiting for contracts to publish");
        }

        let heights1_value = call_read_only(
            &naka_conf,
            &sender_addr,
            contract1_name,
            "get-heights",
            vec![],
        );
        let heights1 = heights1_value.expect_tuple().unwrap();
        info!("Heights from Clarity 1: {heights1}");

        let heights3_value = call_read_only(
            &naka_conf,
            &sender_addr,
            contract3_name,
            "get-heights",
            vec![],
        );
        let heights3 = heights3_value.expect_tuple().unwrap();
        info!("Heights from Clarity 3: {heights3}");

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

        let info = get_chain_info_result(&naka_conf).unwrap();
        assert_eq!(info.tenure_height, bh3 as u64);

        let sbh = heights3
            .get("stacks-block-height")
            .unwrap()
            .clone()
            .expect_u128()
            .unwrap();
        let expected_height = if tenure_ix == 0 {
            // tenure 0 will include an interim block at this point because of the contract publish
            //  txs
            last_stacks_block_height + 2
        } else {
            last_stacks_block_height + 1
        };
        assert_eq!(
            sbh, expected_height,
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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
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
            info!("Heights from Clarity 1: {heights1}");

            let heights3_value = call_read_only(
                &naka_conf,
                &sender_addr,
                contract3_name,
                "get-heights",
                vec![],
            );
            let heights3 = heights3_value.expect_tuple().unwrap();
            info!("Heights from Clarity 3: {heights3}");

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

            let info = get_chain_info_result(&naka_conf).unwrap();
            assert_eq!(info.tenure_height, bh3 as u64);

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
        block_height_pre_3_0 + 1 + ((inter_blocks_per_tenure + 1) * tenure_count),
        "Should have mined 1 + (1 + interim_blocks_per_tenure) * tenure_count nakamoto blocks"
    );

    let info = get_chain_info_result(&naka_conf).unwrap();
    assert_eq!(info.tenure_height, block_height_pre_3_0 + tenure_count);

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
    naka_conf.connection_options.auth_token = Some(password);
    // Use fixed timing params for this test
    let nakamoto_attempt_time_ms = 20_000;
    naka_conf.miner.nakamoto_attempt_time_ms = nakamoto_attempt_time_ms;
    let stacker_sk = setup_stacker(&mut naka_conf);

    let sender_sk = Secp256k1PrivateKey::random();
    let sender_addr = tests::to_addr(&sender_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_addr).to_string(), 1_000_000_000);

    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100_000);

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
    test_observer::register(&mut naka_conf, &[EventKeyType::BlockProposal]);

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
    let counters = run_loop.counters();

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
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
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
            debug!("nakamoto_attempt_time: begin tenure {tenure_count}");

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
                let transfer_tx = make_stacks_transfer(
                    &sender_sk,
                    sender_nonce,
                    tx_fee,
                    naka_conf.burnchain.chain_id,
                    &recipient,
                    amount,
                );
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
            let transfer_tx = make_stacks_transfer(
                &acct.privk,
                acct.nonce,
                tx_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                amount,
            );
            submit_tx(&http_origin, &transfer_tx);
            tx_total_size += transfer_tx.len();
            tx_count += 1;
            acct.nonce += 1;
            if tx_count >= tx_limit {
                break 'submit_txs;
            }
            info!(
                "nakamoto_times_ms: on account {acct_idx}; sent {tx_count} txs so far (out of {tx_limit})"
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
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let tx_fee = 1000;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        deploy_fee + tx_fee * tenure_count + tx_fee * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    naka_conf.miner.tenure_cost_limit_per_block_percentage = None;
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register(&mut naka_conf, &[EventKeyType::MinedBlocks]);

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
        naka_conf.burnchain.chain_id,
        contract_name,
        contract,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx);

    let mut burn_block_height = 0;

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {tenure_ix}");

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

            // Pause mining to prevent the stacks block from being mined before the tenure change is processed
            TEST_MINE_STALL.set(true);
            // Submit a tx for the next block (the next block will be a new tenure, so the burn block height will increment)
            let call_tx = tests::make_contract_call(
                &sender_sk,
                sender_nonce,
                tx_fee,
                naka_conf.burnchain.chain_id,
                &sender_addr,
                contract_name,
                "bar",
                &[Value::UInt(burn_block_height + 1)],
            );
            sender_nonce += 1;
            submit_tx(&http_origin, &call_tx);
        }

        let commits_before = commits_submitted.load(Ordering::SeqCst);
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        next_block_and(&mut btc_regtest_controller, 60, || {
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap();
        TEST_MINE_STALL.set(false);
        wait_for(20, || {
            Ok(coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed()
                > blocks_processed_before)
        })
        .unwrap();

        // in the first tenure, make sure that the contracts are published
        if tenure_ix == 0 {
            wait_for(30, || {
                let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
                Ok(cur_sender_nonce >= sender_nonce)
            })
            .expect("Timed out waiting for contracts to publish");
        }

        let info = get_chain_info(&naka_conf);
        burn_block_height = info.burn_block_height as u128;
        info!("Expecting burn block height to be {burn_block_height}");

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

                    info!("Contract call result: {result}");
                    result.clone().expect_result_ok().expect("Ok result");
                }
                _ => {
                    info!("Unsuccessful event: {event:?}");
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
            info!("Read-only result: {result:?}");
            result.expect_result_ok().expect("Read-only call failed");

            // Submit a tx to trigger the next block
            let call_tx = tests::make_contract_call(
                &sender_sk,
                sender_nonce,
                tx_fee,
                naka_conf.burnchain.chain_id,
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
                        info!("Contract call result: {result}");
                        result.clone().expect_result_ok().expect("Ok result");
                    }
                    _ => {
                        info!("Unsuccessful event: {event:?}");
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
#[allow(clippy::drop_non_drop)]
fn signer_chainstate() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signers = TestSigners::default();
    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = "127.0.0.1:6000".to_string();
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 200;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * 20,
    );
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

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
        let prom_http_origin = format!("http://{prom_bind}");
        wait_for(10, || {
            let client = reqwest::blocking::Client::new();
            let res = client
                .get(&prom_http_origin)
                .send()
                .unwrap()
                .text()
                .unwrap();
            let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
            Ok(res.contains(&expected_result))
        })
        .expect("Failed waiting for prometheus metrics to update")
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted.clone());

    let signer_client = stacks_signer::client::StacksClient::new(
        StacksPrivateKey::from_seed(&[0, 1, 2, 3]),
        naka_conf.node.rpc_bind.clone(),
        naka_conf
            .connection_options
            .auth_token
            .clone()
            .unwrap_or("".into()),
        false,
        CHAIN_ID_TESTNET,
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
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

        // this config disallows any reorg due to poorly timed block commits
        let proposal_conf = ProposalEvalConfig {
            first_proposal_burn_block_timing: Duration::from_secs(0),
            block_proposal_timeout: Duration::from_secs(100),
            tenure_last_block_proposal_timeout: Duration::from_secs(30),
            tenure_idle_timeout: Duration::from_secs(300),
            tenure_idle_timeout_buffer: Duration::from_secs(2),
            reorg_attempts_activity_timeout: Duration::from_secs(30),
        };
        let mut sortitions_view =
            SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();

        // check the prior tenure's proposals again, confirming that the sortitions_view
        //  will reject them.
        if let Some((ref miner_pk, ref prior_tenure_first, ref prior_tenure_interims)) =
            last_tenures_proposals
        {
            let reject_code = sortitions_view
                .check_proposal(
                    &signer_client,
                    &mut signer_db,
                    prior_tenure_first,
                    miner_pk,
                    true,
                )
                .expect_err("Sortitions view should reject proposals from prior tenure");
            assert_eq!(
                reject_code,
                RejectReason::NotLatestSortitionWinner,
                "Sortitions view should reject proposals from prior tenure"
            );
            for block in prior_tenure_interims.iter() {
                let reject_code = sortitions_view
                    .check_proposal(&signer_client, &mut signer_db, block, miner_pk, true)
                    .expect_err("Sortitions view should reject proposals from prior tenure");
                assert_eq!(
                    reject_code,
                    RejectReason::NotLatestSortitionWinner,
                    "Sortitions view should reject proposals from prior tenure"
                );
            }
        }

        // make sure we're getting a proposal from the current sortition (not 100% guaranteed by
        //  `next_block_and_mine_commit`) by looping
        let time_start = Instant::now();
        let proposal = loop {
            let proposal = get_latest_block_proposal(&naka_conf, &sortdb).unwrap();
            if proposal.0.header.consensus_hash == sortitions_view.cur_sortition.consensus_hash {
                break proposal;
            }
            if time_start.elapsed() > Duration::from_secs(20) {
                panic!("Timed out waiting for block proposal from the current bitcoin block");
            }
            thread::sleep(Duration::from_secs(1));
        };

        let burn_block_height = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;
        let reward_cycle = burnchain
            .block_height_to_reward_cycle(burn_block_height)
            .unwrap();
        sortitions_view
            .check_proposal(
                &signer_client,
                &mut signer_db,
                &proposal.0,
                &proposal.1,
                true,
            )
            .expect("Nakamoto integration test produced invalid block proposal");
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
                state: BlockState::Unprocessed,
                validation_time_ms: None,
            })
            .unwrap();

        let before = proposals_submitted.load(Ordering::SeqCst);

        // submit a tx to trigger an intermediate block
        let sender_nonce = i;
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            sender_nonce,
            send_fee,
            naka_conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        submit_tx(&http_origin, &transfer_tx);

        let timer = Instant::now();
        while proposals_submitted.load(Ordering::SeqCst) <= before {
            thread::sleep(Duration::from_millis(5));
            if timer.elapsed() > Duration::from_secs(30) {
                panic!("Timed out waiting for nakamoto miner to produce intermediate block");
            }
        }

        // an intermediate block was produced. check the proposed block
        let proposal_interim = get_latest_block_proposal(&naka_conf, &sortdb).unwrap();

        sortitions_view
            .check_proposal(
                &signer_client,
                &mut signer_db,
                &proposal_interim.0,
                &proposal_interim.1,
                true,
            )
            .expect("Nakamoto integration test produced invalid block proposal");
        // force the view to refresh and check again

        // this config disallows any reorg due to poorly timed block commits
        let proposal_conf = ProposalEvalConfig {
            first_proposal_burn_block_timing: Duration::from_secs(0),
            block_proposal_timeout: Duration::from_secs(100),
            tenure_last_block_proposal_timeout: Duration::from_secs(30),
            tenure_idle_timeout: Duration::from_secs(300),
            tenure_idle_timeout_buffer: Duration::from_secs(2),
            reorg_attempts_activity_timeout: Duration::from_secs(30),
        };
        let burn_block_height = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .unwrap()
            .block_height;
        let reward_cycle = burnchain
            .block_height_to_reward_cycle(burn_block_height)
            .unwrap();
        let mut sortitions_view =
            SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();
        sortitions_view
            .check_proposal(
                &signer_client,
                &mut signer_db,
                &proposal_interim.0,
                &proposal_interim.1,
                true,
            )
            .expect("Nakamoto integration test produced invalid block proposal");

        signer_db
            .insert_block(&BlockInfo {
                block: proposal_interim.0.clone(),
                burn_block_height,
                reward_cycle,
                vote: None,
                valid: Some(true),
                signed_over: true,
                proposed_time: get_epoch_time_secs(),
                signed_self: Some(get_epoch_time_secs()),
                signed_group: Some(get_epoch_time_secs()),
                ext: ExtraBlockInfo::None,
                state: BlockState::GloballyAccepted,
                validation_time_ms: Some(1000),
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
    let miner_sk = naka_conf.miner.mining_key.unwrap();
    let miner_pk = StacksPublicKey::from_private(&miner_sk);
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: last_tenure_header.chain_length,
        burn_spent: last_tenure_header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash,
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
        tenure_last_block_proposal_timeout: Duration::from_secs(30),
        tenure_idle_timeout: Duration::from_secs(300),
        tenure_idle_timeout_buffer: Duration::from_secs(2),
        reorg_attempts_activity_timeout: Duration::from_secs(30),
    };
    let mut sortitions_view = SortitionsView::fetch_view(proposal_conf, &signer_client).unwrap();
    sortitions_view
        .check_proposal(
            &signer_client,
            &mut signer_db,
            &sibling_block,
            &miner_pk,
            false,
        )
        .expect_err("A sibling of a previously approved block must be rejected.");

    // Case: the block contains a tenure change, but blocks have already
    //  been signed in this tenure
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: last_tenure_header.chain_length,
        burn_spent: last_tenure_header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash,
        parent_block_id: last_tenure_header.parent_block_id,
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

    sortitions_view
        .check_proposal(
            &signer_client,
            &mut signer_db,
            &sibling_block,
            &miner_pk,
            false,
        )
        .expect_err("A sibling of a previously approved block must be rejected.");

    // Case: the block contains a tenure change, but it doesn't confirm all the blocks of the parent tenure
    let reorg_to_block = first_tenure_blocks.as_ref().unwrap().first().unwrap();
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: reorg_to_block.header.chain_length + 1,
        burn_spent: reorg_to_block.header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash,
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
                    tenure_consensus_hash: sibling_block_header.consensus_hash,
                    prev_tenure_consensus_hash: reorg_to_block.header.consensus_hash,
                    burn_view_consensus_hash: sibling_block_header.consensus_hash,
                    previous_tenure_end: reorg_to_block.block_id(),
                    previous_tenure_blocks: 1,
                    cause: stacks::chainstate::stacks::TenureChangeCause::BlockFound,
                    pubkey_hash: Hash160::from_node_public_key(&miner_pk),
                }),
            },
            last_tenure.txs[1].clone(),
        ],
    };

    sortitions_view
        .check_proposal(
            &signer_client,
            &mut signer_db,
            &sibling_block,
            &miner_pk,
            false,
        )
        .expect_err("A sibling of a previously approved block must be rejected.");

    // Case: the block contains a tenure change, but the parent tenure is a reorg
    let reorg_to_block = first_tenure_blocks.as_ref().unwrap().last().unwrap();
    // make the sortition_view *think* that our block commit pointed at this old tenure
    sortitions_view.cur_sortition.parent_tenure_id = reorg_to_block.header.consensus_hash;
    let mut sibling_block_header = NakamotoBlockHeader {
        version: 1,
        chain_length: reorg_to_block.header.chain_length + 1,
        burn_spent: reorg_to_block.header.burn_spent,
        consensus_hash: last_tenure_header.consensus_hash,
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
                    tenure_consensus_hash: sibling_block_header.consensus_hash,
                    prev_tenure_consensus_hash: reorg_to_block.header.consensus_hash,
                    burn_view_consensus_hash: sibling_block_header.consensus_hash,
                    previous_tenure_end: reorg_to_block.block_id(),
                    previous_tenure_blocks: 1,
                    cause: stacks::chainstate::stacks::TenureChangeCause::BlockFound,
                    pubkey_hash: Hash160::from_node_public_key(&miner_pk),
                }),
            },
            last_tenure.txs[1].clone(),
        ],
    };

    sortitions_view
        .check_proposal(
            &signer_client,
            &mut signer_db,
            &sibling_block,
            &miner_pk,
            false,
        )
        .expect_err("A sibling of a previously approved block must be rejected.");

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
        if let Some(prior) = prior {
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
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind.clone());
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    naka_conf.connection_options.block_proposal_max_age_secs = u64::MAX;
    let http_origin = naka_conf.node.data_url.clone();
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for a test stx transfer
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 1000;
    let send_fee = 200;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * 20,
    );
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);
    let mut transfer_nonce = 0;

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

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
        let prom_http_origin = format!("http://{prom_bind}");
        wait_for(10, || {
            let client = reqwest::blocking::Client::new();
            let res = client
                .get(&prom_http_origin)
                .send()
                .unwrap()
                .text()
                .unwrap();
            let expected_result = format!("stacks_node_stacks_tip_height {block_height_pre_3_0}");
            Ok(res.contains(&expected_result))
        })
        .expect("Prometheus metrics did not update");
    }

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine a regular nakamoto tenure
    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    wait_for(5, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_processed > blocks_processed_before)
    })
    .unwrap();

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    info!("Pausing commit ops to trigger a tenure extend.");
    test_skip_commit_op.set(true);

    next_block_and(&mut btc_regtest_controller, 60, || Ok(true)).unwrap();

    wait_for(5, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_processed > blocks_processed_before)
    })
    .unwrap();

    // Submit a TX
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        transfer_nonce,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
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
            transfer_tx,
            &ExecutionCost::max_value(),
            &StacksEpochId::Epoch30,
        )
        .unwrap();

    // wait for the extended miner to include the tx in a block
    //  before we produce the next bitcoin block (this test will assert
    //  that this is the case at the end of the test).
    wait_for(60, || {
        let nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        Ok(nonce > transfer_nonce)
    })
    .unwrap();

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    wait_for(5, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        let sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        Ok(blocks_processed > blocks_processed_before && sender_nonce >= 1)
    })
    .unwrap();

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();

    next_block_and(&mut btc_regtest_controller, 60, || Ok(true)).unwrap();

    wait_for(5, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_processed > blocks_processed_before)
    })
    .unwrap();

    // Mine 3 nakamoto blocks
    for i in 0..3 {
        info!("Triggering Nakamoto blocks after extend ({})", i + 1);
        transfer_nonce += 1;
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            transfer_nonce,
            send_fee,
            naka_conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        submit_tx(&http_origin, &transfer_tx);
        wait_for(10, || {
            let sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
            Ok(sender_nonce >= transfer_nonce)
        })
        .expect("Timed out waiting for transfer TX to confirm");
    }

    info!("Resuming commit ops to mine regular tenures.");
    test_skip_commit_op.set(false);

    // Mine 15 more regular nakamoto tenures
    for _i in 0..15 {
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        next_block_and(&mut btc_regtest_controller, 60, || {
            let commits_count = commits_submitted.load(Ordering::SeqCst);
            Ok(commits_count > commits_before)
        })
        .unwrap();

        wait_for(5, || {
            let blocks_processed = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            Ok(blocks_processed > blocks_processed_before)
        })
        .unwrap();

        sleep_ms(5_000);
    }

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    // assert that the tenure extend tx was observed
    let mut tenure_extends = vec![];
    let mut tenure_block_founds = vec![];
    let mut transfer_tx_included = false;
    let mut last_block_had_extend = false;
    for pair in test_observer::get_blocks().windows(2) {
        let prev_block = &pair[0];
        let block = &pair[1];
        let mut has_extend = false;
        for tx in block["transactions"].as_array().unwrap() {
            let raw_tx = tx["raw_tx"].as_str().unwrap();
            if raw_tx == transfer_tx_hex {
                transfer_tx_included = true;
                continue;
            }
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();

            if let TransactionPayload::TenureChange(payload) = &parsed.payload {
                match payload.cause {
                    TenureChangeCause::Extended => {
                        has_extend = true;
                        tenure_extends.push(parsed);
                    }
                    TenureChangeCause::BlockFound => {
                        if last_block_had_extend
                            && prev_block["transactions"].as_array().unwrap().len() <= 1
                        {
                            panic!("Expected other transactions to happen after tenure extend");
                        }
                        tenure_block_founds.push(parsed);
                    }
                };
            }
        }
        last_block_had_extend = has_extend;
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
        let prom_http_origin = format!("http://{prom_bind}");
        wait_for(10, || {
            let client = reqwest::blocking::Client::new();
            let res = client
                .get(&prom_http_origin)
                .send()
                .unwrap()
                .text()
                .unwrap();
            let expected_result =
                format!("stacks_node_stacks_tip_height {}", tip.stacks_block_height);
            Ok(res.contains(&expected_result))
        })
        .expect("Prometheus metrics did not update");
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

fn get_block_times(
    naka_conf: &Config,
    sender_addr: &StacksAddress,
    block_height: u128,
    tenure_height: u128,
) -> (u128, u128, u128, u128, u128, u128, u128) {
    let contract0_name = "test-contract-0";
    let contract1_name = "test-contract-1";
    let contract3_name = "test-contract-3";

    info!("Getting block times at block {block_height}, tenure {tenure_height}...");

    let time0_value = call_read_only(
        naka_conf,
        sender_addr,
        contract0_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(tenure_height)],
    );
    let time0 = time0_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time_now0_value = call_read_only(
        naka_conf,
        sender_addr,
        contract0_name,
        "get-last-time",
        vec![],
    );
    let time0_now = time_now0_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time1_value = call_read_only(
        naka_conf,
        sender_addr,
        contract1_name,
        "get-time",
        vec![&clarity::vm::Value::UInt(tenure_height)],
    );
    let time1 = time1_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time1_now_value = call_read_only(
        naka_conf,
        sender_addr,
        contract1_name,
        "get-last-time",
        vec![],
    );
    let time1_now = time1_now_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time3_tenure_value = call_read_only(
        naka_conf,
        sender_addr,
        contract3_name,
        "get-tenure-time",
        vec![&clarity::vm::Value::UInt(block_height)],
    );
    let time3_tenure = time3_tenure_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time3_block_value = call_read_only(
        naka_conf,
        sender_addr,
        contract3_name,
        "get-block-time",
        vec![&clarity::vm::Value::UInt(block_height)],
    );
    let time3_block = time3_block_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    let time3_now_tenure_value = call_read_only(
        naka_conf,
        sender_addr,
        contract3_name,
        "get-last-tenure-time",
        vec![],
    );
    let time3_now_tenure = time3_now_tenure_value
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_u128()
        .unwrap();

    info!("Reported times:";
        "time0" => time0,
        "time0_now" => time0_now,
        "time1" => time1,
        "time1_now" => time1_now,
        "time3_block" => time3_block,
        "time3_tenure" => time3_tenure,
        "time3_now_tenure" => time3_now_tenure
    );

    assert_eq!(
        time0, time1,
        "Time from pre- and post-epoch 3.0 contracts should match"
    );
    assert_eq!(
        time0_now, time1_now,
        "Time from pre- and post-epoch 3.0 contracts should match"
    );
    assert_eq!(time0_now, time1_now, "Time should match across contracts");

    (
        time0,
        time0_now,
        time1,
        time1_now,
        time3_tenure,
        time3_block,
        time3_now_tenure,
    )
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
    naka_conf.burnchain.chain_id = CHAIN_ID_TESTNET + 1;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 12,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 = r#"
        (define-read-only (get-time (height uint)) (get-block-info? time height))
        (define-read-only (get-last-time) (get-block-info? time (- block-height u1)))
    "#;

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
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
    wait_for_first_naka_block_commit(60, &counters.naka_submitted_commits);

    let info = get_chain_info_result(&naka_conf).unwrap();
    let mut last_stacks_block_height = info.stacks_tip_height as u128;
    let mut last_tenure_height = last_stacks_block_height + 1;

    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

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
    info!("Time from pre-epoch 3.0: {time0}");

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    // This version uses the Clarity 3 functions
    let contract3_name = "test-contract-3";
    let contract_clarity3 = r#"
        (define-read-only (get-block-time (height uint)) (get-stacks-block-info? time height))
        (define-read-only (get-tenure-time (height uint)) (get-tenure-info? time height))
        (define-read-only (get-last-tenure-time) (get-tenure-info? time (- stacks-block-height u1)))
    "#;

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        contract3_name,
        contract_clarity3,
    );
    submit_tx(&http_origin, &contract_tx3);
    sender_nonce += 1;

    let mut stacks_block_height = 0;
    wait_for(60, || {
        let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        let info = get_chain_info_result(&naka_conf).unwrap();
        stacks_block_height = info.stacks_tip_height as u128;
        Ok(stacks_block_height > last_stacks_block_height && cur_sender_nonce == sender_nonce)
    })
    .expect("Timed out waiting for contracts to publish");

    // Repeat these tests for 5 tenures
    for _ in 0..5 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
        let info = get_chain_info_result(&naka_conf).unwrap();
        stacks_block_height = info.stacks_tip_height as u128;

        last_stacks_block_height = stacks_block_height;
        last_tenure_height += 1;
        info!("New tenure {last_tenure_height}, Stacks height: {last_stacks_block_height}");

        let (time0, time0_now, _time1, _time1_now, time3_tenure, time3_block, time3_now_tenure) =
            get_block_times(
                &naka_conf,
                &sender_addr,
                last_stacks_block_height - 1,
                last_tenure_height - 1,
            );

        assert_eq!(
            time0, time3_tenure,
            "Tenure time should match Clarity 2 block time"
        );
        assert_eq!(
            time0_now, time3_now_tenure,
            "Clarity 3 tenure time should match Clarity 2 block time in the first block of a tenure"
        );

        // Mine a Nakamoto block
        info!("Mining Nakamoto block");

        // submit a tx so that the miner will mine an extra block
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            sender_nonce,
            send_fee,
            naka_conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        sender_nonce += 1;
        submit_tx(&http_origin, &transfer_tx);

        // wait for the block to be mined
        wait_for(30, || {
            let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
            let info = get_chain_info_result(&naka_conf).unwrap();
            stacks_block_height = info.stacks_tip_height as u128;
            Ok(stacks_block_height > last_stacks_block_height && cur_sender_nonce == sender_nonce)
        })
        .expect("Timed out waiting for block");
        last_stacks_block_height = stacks_block_height;

        info!("New Stacks block {last_stacks_block_height} in tenure {last_tenure_height}");

        let (
            time0a,
            _time0a_now,
            _time1a,
            _time1a_now,
            _time3a_tenure,
            time3a_block,
            time3a_now_tenure,
        ) = get_block_times(
            &naka_conf,
            &sender_addr,
            last_stacks_block_height - 1,
            last_tenure_height - 1,
        );

        assert_eq!(
            time0a, time0,
            "get-block-info? time should not have changed"
        );
        assert!(
            time3a_block - time3_block >= 1,
            "get-stacks-block-info? time should have changed"
        );

        // Mine a Nakamoto block
        info!("Mining Nakamoto block");

        // submit a tx so that the miner will mine an extra block
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

        // wait for the block to be mined
        wait_for(30, || {
            let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
            let info = get_chain_info_result(&naka_conf).unwrap();
            stacks_block_height = info.stacks_tip_height as u128;
            Ok(stacks_block_height > last_stacks_block_height && cur_sender_nonce == sender_nonce)
        })
        .expect("Timed out waiting for block");
        last_stacks_block_height = stacks_block_height;

        let (
            time0b,
            _time0b_now,
            _time1b,
            _time1b_now,
            _time3b_tenure,
            time3b_block,
            time3b_now_tenure,
        ) = get_block_times(
            &naka_conf,
            &sender_addr,
            last_stacks_block_height - 1,
            last_tenure_height - 1,
        );

        assert_eq!(
            time0b, time0a,
            "get-block-info? time should not have changed"
        );
        assert!(
            time3b_block - time3a_block >= 1,
            "get-stacks-block-info? time should have changed"
        );
        assert_eq!(
            time3b_now_tenure, time3a_now_tenure,
            "get-tenure-info? time should not have changed"
        );
    }

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
    info!("block info tuple data: {tuple0:#?}");

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

fn parse_block_id(optional_buff32: &Value) -> StacksBlockId {
    let bytes = optional_buff32
        .clone()
        .expect_optional()
        .unwrap()
        .unwrap()
        .expect_buff(32)
        .unwrap();
    StacksBlockId::from_vec(&bytes).unwrap()
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
    // change the chain id so that it isn't the same as primary testnet
    naka_conf.burnchain.chain_id = CHAIN_ID_TESTNET + 1;
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    naka_conf.miner.tenure_cost_limit_per_block_percentage = None;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 2,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);
    let contract3_name = "test-contract-3";

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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

    let get_block_info = |contract_name: &str, query_height: u128| {
        let result = call_read_only(
            &naka_conf,
            &sender_addr,
            contract_name,
            "get-block-info",
            vec![&clarity::vm::Value::UInt(query_height)],
        );
        result.expect_tuple().unwrap().data_map
    };

    let get_tenure_info = |query_height: u128| {
        let result = call_read_only(
            &naka_conf,
            &sender_addr,
            contract3_name,
            "get-tenure-info",
            vec![&clarity::vm::Value::UInt(query_height)],
        );
        result.expect_tuple().unwrap().data_map
    };

    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let miner = clarity::vm::Value::Principal(
        PrincipalData::parse_standard_principal("ST25WA53N4PWF8XZGQH2J5A4CGCWV4JADPM8MHTRV")
            .unwrap()
            .into(),
    );
    let miner_spend = clarity::vm::Value::UInt(20000);

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 = "(define-read-only (get-block-info (height uint))
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
    // This version uses the Clarity 3 functions
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

    let contract_tx0 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
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

    let info = get_chain_info(&naka_conf);
    let last_pre_nakamoto_block_height = info.stacks_tip_height.into();

    blind_signer(&naka_conf, &signers, proposals_submitted);

    let c0_block_ht_1_pre_3 = get_block_info(contract0_name, 1);
    info!("Info from pre-epoch 3.0: {c0_block_ht_1_pre_3:?}");

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        contract1_name,
        contract_clarity1,
        Some(ClarityVersion::Clarity2),
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx1);

    let contract_tx3 = make_contract_publish(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
        contract3_name,
        contract_clarity3,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx3);

    // sleep to ensure seconds have changed
    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    // make sure that the contracts are published
    wait_for(30, || {
        let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        Ok(cur_sender_nonce >= sender_nonce)
    })
    .expect("Timed out waiting for contracts to publish");

    // the first test we want to do is around the behavior of
    //  looking up 2.x blocks.

    // look up block height 1 with all 3 contracts after nakamoto activates
    let c0_block_ht_1_post_3 = get_block_info(contract0_name, 1);
    let c1_block_ht_1_post_3 = get_block_info(contract1_name, 1);
    let c3_block_ht_1_post_3 = get_block_info(contract3_name, 1);
    assert_eq!(c0_block_ht_1_post_3, c0_block_ht_1_pre_3);
    assert_eq!(c0_block_ht_1_post_3, c1_block_ht_1_post_3);
    for (key, value) in c3_block_ht_1_post_3.iter() {
        assert_eq!(&c0_block_ht_1_post_3[key], value);
    }

    // look up last 2.x height with all 3 contracts
    let c0_last_2x_block = get_block_info(contract0_name, last_pre_nakamoto_block_height);
    let c1_last_2x_block = get_block_info(contract1_name, last_pre_nakamoto_block_height);
    let c3_last_2x_block = get_block_info(contract3_name, last_pre_nakamoto_block_height);
    assert_eq!(c0_last_2x_block, c1_last_2x_block);
    for (key, value) in c3_last_2x_block.iter() {
        assert_eq!(&c0_last_2x_block[key], value);
    }

    // now we want to test the behavior of the first block in a tenure
    // so, we'll issue a bitcoin block, and not submit any transactions
    // (which will keep the miner from issuing any blocks after the first
    //  one in the tenure)

    let info = get_chain_info(&naka_conf);
    info!("Chain info: {info:?}");
    let last_stacks_block_height = info.stacks_tip_height as u128;
    let last_stacks_tip = StacksBlockId::new(&info.stacks_tip_consensus_hash, &info.stacks_tip);
    let last_tenure_height: u128 =
        NakamotoChainState::get_coinbase_height(&mut chainstate.index_conn(), &last_stacks_tip)
            .unwrap()
            .unwrap()
            .into();
    let last_tenure_start_block_header = NakamotoChainState::get_tenure_start_block_header(
        &mut chainstate.index_conn(),
        &last_stacks_tip,
        &info.stacks_tip_consensus_hash,
    )
    .unwrap()
    .unwrap();
    let last_tenure_start_block_id = last_tenure_start_block_header.index_block_hash();
    let last_tenure_start_block_ht = last_tenure_start_block_header.stacks_block_height.into();

    // lets issue the next bitcoin block
    next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
        .unwrap();

    let info = get_chain_info(&naka_conf);
    info!("Chain info: {info:?}");
    let cur_stacks_block_height = info.stacks_tip_height as u128;
    let cur_stacks_tip = StacksBlockId::new(&info.stacks_tip_consensus_hash, &info.stacks_tip);
    let cur_tenure_height: u128 =
        NakamotoChainState::get_coinbase_height(&mut chainstate.index_conn(), &cur_stacks_tip)
            .unwrap()
            .unwrap()
            .into();
    let cur_tenure_start_block_id = NakamotoChainState::get_tenure_start_block_header(
        &mut chainstate.index_conn(),
        &cur_stacks_tip,
        &info.stacks_tip_consensus_hash,
    )
    .unwrap()
    .unwrap()
    .index_block_hash();

    assert_eq!(cur_tenure_start_block_id, cur_stacks_tip);
    assert_eq!(cur_stacks_block_height, last_stacks_block_height + 1);
    assert_eq!(cur_tenure_height, last_tenure_height + 1);

    // first checks: get-block-info with the current tenure height should return None
    let c0_cur_tenure = get_block_info(contract0_name, cur_tenure_height);
    let c1_cur_tenure = get_block_info(contract1_name, cur_tenure_height);
    // contract 3 uses the current stacks block height rather than current tenure.
    let c3_cur_tenure = get_block_info(contract3_name, cur_stacks_block_height);
    let c3_cur_tenure_ti = get_tenure_info(cur_stacks_block_height);
    assert!(c0_cur_tenure["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());
    assert!(c1_cur_tenure["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());
    assert!(c3_cur_tenure["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());
    assert!(c3_cur_tenure_ti["burnchain-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());

    // second checks: get-block-info with prior tenure height should return Some
    let c0_last_tenure = get_block_info(contract0_name, last_tenure_height);
    let c1_last_tenure = get_block_info(contract1_name, last_tenure_height);
    // contract 3 uses the current stacks block height rather than current tenure.
    let c3_last_tenure_bi = get_block_info(contract3_name, last_stacks_block_height);
    let c3_last_tenure_ti = get_tenure_info(last_stacks_block_height);
    let c3_last_tenure_start_bi = get_block_info(contract3_name, last_tenure_start_block_ht);

    // assert that c0 and c1 returned some data
    assert_block_info(&c0_last_tenure, &miner, &miner_spend);
    assert_block_info(&c1_last_tenure, &miner, &miner_spend);
    assert_eq!(c0_last_tenure, c1_last_tenure);

    let c3_fetched_id_hash = parse_block_id(&c3_last_tenure_bi["id-header-hash"]);
    assert_eq!(c3_fetched_id_hash, last_stacks_tip);

    // c0 and c1 should have different block info data than c3
    assert_ne!(
        c0_last_tenure["header-hash"],
        c3_last_tenure_bi["header-hash"]
    );
    assert_ne!(
        c0_last_tenure["id-header-hash"],
        c3_last_tenure_bi["id-header-hash"]
    );
    assert_ne!(c0_last_tenure["time"], c3_last_tenure_bi["time"]);
    // c0 and c1 should have the same burn data as the *tenure info* lookup in c3
    for (key, value) in c3_last_tenure_ti.iter() {
        assert_eq!(&c0_last_tenure[key], value);
    }
    // c0 and c1 should have the same header hash data as the *block info* lookup in c3 using last tenure start block ht
    for key in ["header-hash", "id-header-hash"] {
        assert_eq!(&c0_last_tenure[key], &c3_last_tenure_start_bi[key]);
    }
    // c0 should have the same index hash as last_tenure start block id
    assert_eq!(
        parse_block_id(&c0_last_tenure["id-header-hash"]),
        last_tenure_start_block_id
    );

    // Now we want to test the behavior of a new nakamoto block within the same tenure
    // We'll force a nakamoto block by submitting a transfer, then waiting for the nonce to bump
    info!("Mining an interim nakamoto block");
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &transfer_tx);

    wait_for(30, || {
        thread::sleep(Duration::from_secs(1));
        let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        Ok(cur_sender_nonce >= sender_nonce)
    })
    .expect("Failed to process the submitted transfer tx in a new nakamoto block");

    let info = get_chain_info(&naka_conf);
    let interim_stacks_block_height = info.stacks_tip_height as u128;
    let interim_stacks_tip = StacksBlockId::new(&info.stacks_tip_consensus_hash, &info.stacks_tip);
    let interim_tenure_height: u128 =
        NakamotoChainState::get_coinbase_height(&mut chainstate.index_conn(), &interim_stacks_tip)
            .unwrap()
            .unwrap()
            .into();
    let interim_tenure_start_block_id = NakamotoChainState::get_tenure_start_block_header(
        &mut chainstate.index_conn(),
        &interim_stacks_tip,
        &info.stacks_tip_consensus_hash,
    )
    .unwrap()
    .unwrap()
    .index_block_hash();
    assert_eq!(interim_tenure_height, cur_tenure_height);
    assert_eq!(interim_tenure_start_block_id, cur_tenure_start_block_id);
    assert_eq!(interim_stacks_block_height, cur_stacks_block_height + 1);

    // querying the same block heights that returned data before should yield the identical result
    assert_eq!(
        c0_last_tenure,
        get_block_info(contract0_name, last_tenure_height)
    );
    assert_eq!(
        c1_last_tenure,
        get_block_info(contract1_name, last_tenure_height)
    );
    assert_eq!(
        c3_last_tenure_bi,
        get_block_info(contract3_name, last_stacks_block_height)
    );
    assert_eq!(c3_last_tenure_ti, get_tenure_info(last_stacks_block_height));
    assert_eq!(
        c3_last_tenure_start_bi,
        get_block_info(contract3_name, last_tenure_start_block_ht)
    );

    // querying for the current tenure should work now though
    let c0_cur_tenure = get_block_info(contract0_name, cur_tenure_height);
    let c1_cur_tenure = get_block_info(contract1_name, cur_tenure_height);
    // contract 3 uses the current stacks block height rather than current tenure.
    let c3_cur_tenure = get_block_info(contract3_name, cur_stacks_block_height);
    let c3_cur_tenure_ti = get_tenure_info(cur_stacks_block_height);
    assert_block_info(&c0_cur_tenure, &miner, &miner_spend);
    assert_block_info(&c1_cur_tenure, &miner, &miner_spend);
    assert_eq!(c0_cur_tenure, c1_cur_tenure);

    // c0 and c1 should have the same header hash data as the *block info* lookup in c3 using cur_stacks_block
    //  (because cur_stacks_tip == cur_tenure_start_block_id, as was asserted before)
    for key in ["header-hash", "id-header-hash"] {
        assert_eq!(&c0_cur_tenure[key], &c3_cur_tenure[key]);
    }
    // c0 should have the same index hash as cur_tenure start block id
    assert_eq!(
        parse_block_id(&c0_cur_tenure["id-header-hash"]),
        cur_tenure_start_block_id,
        "c0 should have the same index hash as cur_tenure_start_block_id"
    );
    // c0 and c1 should have the same burn data as the *tenure info* lookup in c3
    for (key, value) in c3_cur_tenure_ti.iter() {
        assert_eq!(&c0_cur_tenure[key], value);
    }

    let c3_interim_bi = get_block_info(contract3_name, interim_stacks_block_height);
    let c3_interim_ti = get_tenure_info(interim_stacks_block_height);
    assert!(c3_interim_bi["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());
    assert!(c3_interim_ti["burnchain-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());

    // Now we'll mine one more interim block so that we can test that the stacks-block-info outputs update
    //  again.
    info!("Mining a second interim nakamoto block");
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &transfer_tx);

    wait_for(30, || {
        thread::sleep(Duration::from_secs(1));
        let cur_sender_nonce = get_account(&http_origin, &to_addr(&sender_sk)).nonce;
        Ok(cur_sender_nonce >= sender_nonce)
    })
    .expect("Failed to process the submitted transfer tx in a new nakamoto block");

    let info = get_chain_info(&naka_conf);
    assert_eq!(
        info.stacks_tip_height as u128,
        interim_stacks_block_height + 1
    );

    // querying for the current tenure should work the same as before
    assert_eq!(
        c0_cur_tenure,
        get_block_info(contract0_name, cur_tenure_height)
    );
    assert_eq!(
        c1_cur_tenure,
        get_block_info(contract1_name, cur_tenure_height)
    );
    // contract 3 uses the current stacks block height rather than current tenure.
    assert_eq!(
        c3_cur_tenure,
        get_block_info(contract3_name, cur_stacks_block_height)
    );
    assert_eq!(c3_cur_tenure_ti, get_tenure_info(cur_stacks_block_height));

    // querying using the first interim's block height should now work in contract 3
    let c3_interim_bi = get_block_info(contract3_name, interim_stacks_block_height);
    let c3_interim_ti = get_tenure_info(interim_stacks_block_height);

    // it will *not* work in contracts 1 and 2
    let c0_interim = get_block_info(contract0_name, interim_stacks_block_height);
    let c1_interim = get_block_info(contract1_name, interim_stacks_block_height);
    assert!(c0_interim["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());
    assert!(c1_interim["id-header-hash"]
        .clone()
        .expect_optional()
        .unwrap()
        .is_none());

    assert_eq!(c3_interim_ti, c3_cur_tenure_ti, "Tenure info should be the same whether queried using the starting block or the interim block height");

    // c0 and c1 should have different block info data than the interim block
    assert_ne!(c0_cur_tenure["header-hash"], c3_interim_bi["header-hash"]);
    assert_ne!(
        c0_cur_tenure["id-header-hash"],
        c3_interim_bi["id-header-hash"]
    );
    assert_ne!(c0_cur_tenure["time"], c3_interim_bi["time"]);

    // c3 should have gotten the interim's tip
    assert_eq!(
        parse_block_id(&c3_interim_bi["id-header-hash"]),
        interim_stacks_tip,
        "Contract 3 should be able to fetch the StacksBlockId of the tip"
    );

    let mut blocks = test_observer::get_blocks();
    blocks.sort_by_key(|block| block["block_height"].as_u64().unwrap());

    let mut last_tenture_height = 0;
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        let mut block_has_tenure_change = false;
        for tx in transactions.iter().rev() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx != "0x00" {
                let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
                let parsed =
                    StacksTransaction::consensus_deserialize(&mut tx_bytes.as_slice()).unwrap();
                if let TransactionPayload::TenureChange(_tenure_change) = parsed.payload {
                    block_has_tenure_change = true;
                    continue;
                }
            }
        }
        // if `signer_bitvec` is set on a block, then it's a nakamoto block
        let is_nakamoto_block = block.get("signer_bitvec").map_or(false, |v| !v.is_null());
        let tenure_height = block.get("tenure_height").unwrap().as_u64().unwrap();
        let block_height = block.get("block_height").unwrap().as_u64().unwrap();

        if block_height == 0 {
            // genesis block
            continue;
        }

        if is_nakamoto_block {
            if block_has_tenure_change {
                // tenure change block should have tenure height 1 more than the last tenure height
                assert_eq!(last_tenture_height + 1, tenure_height);
                last_tenture_height = tenure_height;
            } else {
                // tenure extend block should have the same tenure height as the last tenure height
                assert_eq!(last_tenture_height, tenure_height);
            }
        } else {
            // epoch2.x block tenure height is the same as the block height
            assert_eq!(tenure_height, block_height);
            last_tenture_height = block_height;
        }
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

fn get_expected_reward_for_height(blocks: &[serde_json::Value], block_height: u128) -> u128 {
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
    naka_conf.burnchain.chain_id = CHAIN_ID_TESTNET + 1;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);

    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    let deploy_fee = 3000;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        3 * deploy_fee + (send_amt + send_fee) * 2,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::Builder::new()
        .name("run_loop".into())
        .spawn(move || run_loop.start(None, 0))
        .unwrap();
    wait_for_runloop(&blocks_processed);

    let mut sender_nonce = 0;

    // Deploy this version with the Clarity 1 / 2 before epoch 3
    let contract0_name = "test-contract-0";
    let contract_clarity1 = "(define-read-only (get-block-info (height uint))
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
        naka_conf.burnchain.chain_id,
        contract0_name,
        contract_clarity1,
    );
    sender_nonce += 1;
    submit_tx(&http_origin, &contract_tx0);

    let get_block_info = |contract_name: &str, query_height: u128| {
        let result = call_read_only(
            &naka_conf,
            &sender_addr,
            contract_name,
            "get-block-info",
            vec![&clarity::vm::Value::UInt(query_height)],
        );
        result.expect_tuple().unwrap().data_map
    };

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

    let tuple0 = get_block_info(contract0_name, 1);
    info!("Info from pre-epoch 3.0: {tuple0:?}");

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // This version uses the Clarity 1 / 2 function
    let contract1_name = "test-contract-1";
    let contract_tx1 = make_contract_publish_versioned(
        &sender_sk,
        sender_nonce,
        deploy_fee,
        naka_conf.burnchain.chain_id,
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
        naka_conf.burnchain.chain_id,
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
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
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
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        naka_conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
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
    info!("Chain info: {info:?}");
    let (chainstate, _) = StacksChainState::open(
        naka_conf.is_mainnet(),
        naka_conf.burnchain.chain_id,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    let last_stacks_block_height = info.stacks_tip_height as u128;
    let last_nakamoto_block = last_stacks_block_height;
    let last_stacks_tip = StacksBlockId::new(&info.stacks_tip_consensus_hash, &info.stacks_tip);
    let last_nakamoto_block_tenure_height: u128 =
        NakamotoChainState::get_coinbase_height(&mut chainstate.index_conn(), &last_stacks_tip)
            .unwrap()
            .unwrap()
            .into();

    // Mine more than 2 burn blocks to get the last block's reward matured
    // (only 2 blocks maturation time in tests)
    info!("Mining 6 tenures to mature the block reward");
    for i in 0..6 {
        next_block_and_mine_commit(&mut btc_regtest_controller, 20, &naka_conf, &counters).unwrap();
        info!("Mined a block ({i})");
    }

    let info = get_chain_info_result(&naka_conf).unwrap();
    info!("Chain info: {info:?}");
    let last_stacks_block_height = info.stacks_tip_height as u128;
    let blocks = test_observer::get_blocks();

    let last_stacks_tip = StacksBlockId::new(&info.stacks_tip_consensus_hash, &info.stacks_tip);
    let last_tenure_height: u128 =
        NakamotoChainState::get_coinbase_height(&mut chainstate.index_conn(), &last_stacks_tip)
            .unwrap()
            .unwrap()
            .into();

    // Check the block reward is now matured in one of the tenure-change blocks
    let mature_height = last_stacks_block_height - 4;
    let expected_reward = get_expected_reward_for_height(&blocks, mature_height);
    let tuple0 = get_block_info(contract0_name, last_tenure_height - 4);
    info!(
        "block rewards";
        "fetched" => %tuple0["block-reward"],
        "expected" => expected_reward,
    );
    assert_eq!(
        tuple0["block-reward"]
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        Value::UInt(expected_reward)
    );

    let tuple1 = get_block_info(contract1_name, last_tenure_height - 4);
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(mature_height)],
    );
    let tuple3_tenure = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(tuple3_tenure["block-reward"], tuple0["block-reward"]);

    // Check the block reward is now matured in one of the Nakamoto blocks
    let expected_reward = get_expected_reward_for_height(&blocks, last_nakamoto_block);

    let tuple0 = get_block_info(contract0_name, last_nakamoto_block_tenure_height);

    assert_eq!(
        tuple0["block-reward"]
            .clone()
            .expect_optional()
            .unwrap()
            .unwrap(),
        Value::UInt(expected_reward)
    );

    let tuple1 = get_block_info(contract1_name, last_nakamoto_block_tenure_height);
    assert_eq!(tuple0, tuple1);

    let result3_tenure = call_read_only(
        &naka_conf,
        &sender_addr,
        contract3_name,
        "get-tenure-info",
        vec![&clarity::vm::Value::UInt(last_nakamoto_block)],
    );
    let tuple3_tenure = result3_tenure.expect_tuple().unwrap().data_map;
    assert_eq!(tuple3_tenure["block-reward"], tuple0["block-reward"]);

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
    naka_conf.node.pox_sync_sample_secs = 30;
    naka_conf.miner.tenure_cost_limit_per_block_percentage = None;
    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let tenure_count = 3;
    let inter_blocks_per_tenure = 3;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;

    let node_1_rpc = gen_random_port();
    let node_1_p2p = gen_random_port();
    let node_2_rpc = gen_random_port();
    let node_2_p2p = gen_random_port();

    let localhost = "127.0.0.1";
    naka_conf.node.rpc_bind = format!("{localhost}:{node_1_rpc}");
    naka_conf.node.p2p_bind = format!("{localhost}:{node_1_p2p}");
    naka_conf.node.data_url = format!("http://{localhost}:{node_1_rpc}");
    naka_conf.node.p2p_address = format!("{localhost}:{node_1_p2p}");
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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

    follower_conf.node.rpc_bind = format!("{localhost}:{node_2_rpc}");
    follower_conf.node.p2p_bind = format!("{localhost}:{node_2_p2p}");
    follower_conf.node.data_url = format!("http://{localhost}:{node_2_rpc}");
    follower_conf.node.p2p_address = format!("{localhost}:{node_2_p2p}");

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        naka_conf.burnchain.chain_id,
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

    info!("Booting follower-thread, waiting for the follower to sync to the chain tip");

    // use a high timeout for avoiding problem with github workflow
    wait_for(600, || {
        let Some(miner_node_info) = get_chain_info_opt(&naka_conf) else {
            return Ok(false);
        };
        let Some(follower_node_info) = get_chain_info_opt(&follower_conf) else {
            return Ok(false);
        };
        Ok(miner_node_info.stacks_tip_height == follower_node_info.stacks_tip_height)
    })
    .expect("Timed out waiting for follower to catch up to the miner");
    let miner_node_info = get_chain_info(&naka_conf);
    let follower_node_info = get_chain_info(&follower_conf);
    info!("Node heights"; "miner" => miner_node_info.stacks_tip_height, "follower" => follower_node_info.stacks_tip_height);

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
            let transfer_tx = make_stacks_transfer(
                &sender_sk,
                sender_nonce,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
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

        let miner_node_info = get_chain_info(&naka_conf);
        let follower_node_info = get_chain_info(&follower_conf);
        info!("Node heights"; "miner" => miner_node_info.stacks_tip_height, "follower" => follower_node_info.stacks_tip_height);

        wait_for(60, || {
            Ok(follower_naka_mined_blocks.load(Ordering::SeqCst)
                > follower_naka_mined_blocks_before)
        })
        .unwrap_or_else(|_| {
            panic!(
                "Timed out waiting for mock miner block {}",
                follower_naka_mined_blocks_before + 1
            )
        });

        wait_for(20, || {
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap_or_else(|_| {
            panic!(
                "Timed out waiting for mock miner block {}",
                follower_naka_mined_blocks_before + 1
            )
        });
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
    assert!(
        blocks_mock_mined >= tenure_count,
        "Should have mock mined at least `tenure_count` nakamoto blocks. Mined = {blocks_mock_mined}. Expected = {tenure_count}"
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
/// This test checks for the proper handling of the case where UTXOs are not
/// available on startup. After 1 minute, the miner thread should panic.
fn utxo_check_on_startup_panic() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    println!("Nakamoto node started with config: {naka_conf:?}");
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

    let mut epochs = NAKAMOTO_INTEGRATION_EPOCHS.to_vec();
    let (last, rest) = epochs.split_last_mut().unwrap();
    for (index, epoch) in rest.iter_mut().enumerate() {
        epoch.start_height = index as u64;
        epoch.end_height = (index + 1) as u64;
    }
    last.start_height = 131;

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    // Do not fully bootstrap the chain, so that the UTXOs are not yet available
    btc_regtest_controller.bootstrap_chain(99);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));

    let timeout = Duration::from_secs(70);
    let start_time = Instant::now();

    loop {
        // Check if the thread has panicked
        if run_loop_thread.is_finished() {
            match run_loop_thread.join() {
                Ok(_) => {
                    // Thread completed without panicking
                    panic!("Miner should have panicked but it exited cleanly.");
                }
                Err(_) => {
                    // Thread panicked
                    info!("Thread has panicked!");
                    break;
                }
            }
        }

        // Check if 70 seconds have passed
        assert!(
            start_time.elapsed() < timeout,
            "Miner should have panicked."
        );

        thread::sleep(Duration::from_millis(1000));
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);
}

#[test]
#[ignore]
/// This test checks for the proper handling of the case where UTXOs are not
/// available on startup, but become available later, before the 1 minute
/// timeout. The miner thread should recover and continue mining.
fn utxo_check_on_startup_recover() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    println!("Nakamoto node started with config: {naka_conf:?}");
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1000);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

    let mut epochs = NAKAMOTO_INTEGRATION_EPOCHS.to_vec();
    let (last, rest) = epochs.split_last_mut().unwrap();
    for (index, epoch) in rest.iter_mut().enumerate() {
        epoch.start_height = index as u64;
        epoch.end_height = (index + 1) as u64;
    }
    last.start_height = 131;

    let mut btcd_controller = BitcoinCoreController::new(naka_conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");
    let mut btc_regtest_controller = BitcoinRegtestController::new(naka_conf.clone(), None);
    // Do not fully bootstrap the chain, so that the UTXOs are not yet available
    btc_regtest_controller.bootstrap_chain(99);
    // btc_regtest_controller.bootstrap_chain(108);

    let mut run_loop = boot_nakamoto::BootRunLoop::new(naka_conf.clone()).unwrap();
    let run_loop_stopper = run_loop.get_termination_switch();
    let Counters {
        blocks_processed, ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));

    // Sleep for 30s to allow the miner to start and reach the UTXO check loop
    thread::sleep(Duration::from_secs(30));

    btc_regtest_controller.bootstrap_chain(3);

    wait_for_runloop(&blocks_processed);

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);
    run_loop_thread.join().unwrap();
}

/// Test `/v3/signer` API endpoint
///
/// This endpoint returns a count of how many blocks a signer has signed during a given reward cycle
#[test]
#[ignore]
fn v3_signer_api_endpoint() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    conf.connection_options.auth_token = Some(password);
    conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let stacker_sk = setup_stacker(&mut conf);
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);
    let signer_pubkey = Secp256k1PublicKey::from_private(&signer_sk);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt + send_fee,
    );
    conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    // only subscribe to the block proposal events
    test_observer::spawn();
    test_observer::register(&mut conf, &[EventKeyType::BlockProposal]);

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
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();
    let counters = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![signer_sk]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("------------------------- Reached Epoch 3.0 -------------------------");
    blind_signer(&conf, &signers, proposals_submitted);
    // TODO (hack) instantiate the sortdb in the burnchain
    _ = btc_regtest_controller.sortdb_mut();

    info!("------------------------- Setup finished, run test -------------------------");

    let naka_tenures = conf.burnchain.pox_reward_length.unwrap().into();
    let pre_naka_reward_cycle = 1;
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

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

    // Check reward cycle 1, should be 0 (pre-nakamoto)
    let blocks_signed_pre_naka = get_v3_signer(&signer_pubkey, pre_naka_reward_cycle);
    assert_eq!(blocks_signed_pre_naka, 0);

    let block_height = btc_regtest_controller.get_headers_height();
    let first_reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    let second_reward_cycle = first_reward_cycle.saturating_add(1);
    let second_reward_cycle_start = btc_regtest_controller
        .get_burnchain()
        .reward_cycle_to_block_height(second_reward_cycle)
        .saturating_sub(1);

    let nmb_naka_blocks_in_first_cycle = second_reward_cycle_start - block_height;
    let nmb_naka_blocks_in_second_cycle = naka_tenures - nmb_naka_blocks_in_first_cycle;

    // Mine some nakamoto tenures
    for _i in 0..naka_tenures {
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &conf, &counters).unwrap();
    }
    let block_height = btc_regtest_controller.get_headers_height();
    let reward_cycle = btc_regtest_controller
        .get_burnchain()
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    assert_eq!(reward_cycle, second_reward_cycle);

    // Assert that we mined a single block (the commit op) per tenure
    let nmb_signed_first_cycle = get_v3_signer(&signer_pubkey, first_reward_cycle);
    let nmb_signed_second_cycle = get_v3_signer(&signer_pubkey, second_reward_cycle);

    assert_eq!(nmb_signed_first_cycle, nmb_naka_blocks_in_first_cycle);
    assert_eq!(nmb_signed_second_cycle, nmb_naka_blocks_in_second_cycle);

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    // submit a tx so that the miner will mine an extra stacks block
    let sender_nonce = 0;
    let transfer_tx = make_stacks_transfer(
        &sender_sk,
        sender_nonce,
        send_fee,
        conf.burnchain.chain_id,
        &recipient,
        send_amt,
    );
    submit_tx(&http_origin, &transfer_tx);

    wait_for(30, || {
        Ok(coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed()
            > blocks_processed_before)
    })
    .unwrap();
    // Assert that we mined an additional block in the second cycle
    assert_eq!(
        get_v3_signer(&signer_pubkey, second_reward_cycle),
        nmb_naka_blocks_in_second_cycle + 1
    );

    info!("------------------------- Test finished, clean up -------------------------");

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Test `/v3/blocks/height` API endpoint
///
/// This endpoint returns the block blob given a height
#[test]
#[ignore]
fn v3_blockbyheight_api_endpoint() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    conf.connection_options.auth_token = Some(password);
    conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let stacker_sk = setup_stacker(&mut conf);
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt + send_fee,
    );
    conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);

    // only subscribe to the block proposal events
    test_observer::spawn();
    test_observer::register(&mut conf, &[EventKeyType::BlockProposal]);

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
    let counters = run_loop.counters();
    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![signer_sk]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("------------------------- Reached Epoch 3.0 -------------------------");

    blind_signer(&conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // Mine 1 nakamoto tenure
    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &conf, &counters).unwrap();

    let burnchain = conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    info!("------------------------- Setup finished, run test -------------------------");

    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    let get_v3_block_by_height = |height: u64| {
        let url = &format!("{http_origin}/v3/blocks/height/{height}");
        info!("Send request: GET {url}");
        reqwest::blocking::get(url).unwrap_or_else(|e| panic!("GET request failed: {e}"))
    };

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();

    let block_height = tip.stacks_block_height;
    let block_data = get_v3_block_by_height(block_height);

    assert!(block_data.status().is_success());
    let block_bytes_vec = block_data.bytes().unwrap().to_vec();
    assert!(!block_bytes_vec.is_empty());

    // does the block id of the returned blob matches ?
    let block_id = NakamotoBlockHeader::consensus_deserialize(&mut block_bytes_vec.as_slice())
        .unwrap()
        .block_id();
    assert_eq!(block_id, tip.index_block_hash());

    info!("------------------------- Test finished, clean up -------------------------");

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Verify that lockup events are attached to a phantom tx receipt
/// if the block does not have a coinbase tx
#[test]
#[ignore]
fn nakamoto_lockup_events() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    conf.connection_options.auth_token = Some(password);
    conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let stacker_sk = setup_stacker(&mut conf);
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);
    let _signer_pubkey = Secp256k1PublicKey::from_private(&signer_sk);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * 100,
    );
    conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));

    // only subscribe to the block proposal events
    test_observer::spawn();
    test_observer::register_any(&mut conf);

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
        naka_proposed_blocks: proposals_submitted,
        ..
    } = run_loop.counters();
    let counters = run_loop.counters();
    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![signer_sk]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("------------------------- Reached Epoch 3.0 -------------------------");
    blind_signer(&conf, &signers, proposals_submitted);
    let burnchain = conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();
    let (chainstate, _) = StacksChainState::open(
        conf.is_mainnet(),
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();
    // TODO (hack) instantiate the sortdb in the burnchain
    _ = btc_regtest_controller.sortdb_mut();

    info!("------------------------- Setup finished, run test -------------------------");

    next_block_and_mine_commit(&mut btc_regtest_controller, 60, &conf, &counters).unwrap();

    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    let get_stacks_height = || {
        let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
            .unwrap()
            .unwrap();
        tip.stacks_block_height
    };
    let initial_block_height = get_stacks_height();

    // This matches the data in `stx-genesis/chainstate-test.txt`
    // Recipient: ST2CTPPV8BHBVSQR727A3MK00ZD85RNY9015WGW2D
    let unlock_recipient = "ST2CTPPV8BHBVSQR727A3MK00ZD85RNY9015WGW2D";
    let unlock_height = 35_u64;
    let interims_to_mine = unlock_height - initial_block_height;

    info!(
        "----- Mining to unlock height -----";
        "unlock_height" => unlock_height,
        "initial_height" => initial_block_height,
        "interims_to_mine" => interims_to_mine,
    );

    // submit a tx so that the miner will mine an extra stacks block
    let mut sender_nonce = 0;

    for _ in 0..interims_to_mine {
        let height_before = get_stacks_height();
        info!("----- Mining interim block -----";
            "height" => %height_before,
            "nonce" => %sender_nonce,
        );
        let transfer_tx = make_stacks_transfer(
            &sender_sk,
            sender_nonce,
            send_fee,
            conf.burnchain.chain_id,
            &recipient,
            send_amt,
        );
        submit_tx(&http_origin, &transfer_tx);
        sender_nonce += 1;

        wait_for(30, || Ok(get_stacks_height() > height_before)).unwrap();
    }

    let blocks = test_observer::get_blocks();
    let block = blocks.last().unwrap();
    assert_eq!(
        block.get("block_height").unwrap().as_u64().unwrap(),
        unlock_height
    );

    let events = block.get("events").unwrap().as_array().unwrap();
    let mut found_event = false;
    for event in events {
        let mint_event = event.get("stx_mint_event");
        if mint_event.is_some() {
            found_event = true;
            let mint_event = mint_event.unwrap();
            let recipient = mint_event.get("recipient").unwrap().as_str().unwrap();
            assert_eq!(recipient, unlock_recipient);
            let amount = mint_event.get("amount").unwrap().as_str().unwrap();
            assert_eq!(amount, "12345678");
            let txid = event.get("txid").unwrap().as_str().unwrap();
            assert_eq!(
                txid,
                "0x63dd5773338782755e4947a05a336539137dfe13b19a0eac5154306850aca8ef"
            );
        }
    }
    assert!(found_event);

    info!("------------------------- Test finished, clean up -------------------------");

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
/// This test asserts that a long running transaction doesn't get mined,
///  but that the stacks-node continues to make progress
fn skip_mining_long_tx() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let prom_bind = "127.0.0.1:6000".to_string();
    naka_conf.node.prometheus_bind = Some(prom_bind);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    naka_conf.miner.nakamoto_attempt_time_ms = 5_000;
    naka_conf.miner.tenure_cost_limit_per_block_percentage = None;
    let sender_1_sk = Secp256k1PrivateKey::from_seed(&[30]);
    let sender_2_sk = Secp256k1PrivateKey::from_seed(&[31]);
    // setup sender + recipient for a test stx transfer
    let sender_1_addr = tests::to_addr(&sender_1_sk);
    let sender_2_addr = tests::to_addr(&sender_2_sk);
    let send_amt = 1000;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_1_addr).to_string(),
        send_amt * 15 + send_fee * 15,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_2_addr).to_string(), 10000);
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let recipient = PrincipalData::from(StacksAddress::burn_address(false));
    let stacker_sk = setup_stacker(&mut naka_conf);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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
        naka_mined_blocks: mined_naka_blocks,
        ..
    } = run_loop.counters();
    let counters = run_loop.counters();

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

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // submit a long running TX and the transfer TX
    let input_list: Vec<_> = (1..100u64).map(|x| x.to_string()).collect();
    let input_list = input_list.join(" ");

    // Mine a few nakamoto tenures with some interim blocks in them
    for i in 0..5 {
        let mined_before = mined_naka_blocks.load(Ordering::SeqCst);
        next_block_and_mine_commit(&mut btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

        if i == 0 {
            // we trigger the nakamoto miner to evaluate the long running transaction,
            //  but we disable the block broadcast, so the tx doesn't end up included in a
            //  confirmed block, even though its been evaluated.
            // once we've seen the miner increment the mined counter, we allow it to start
            //  broadcasting (because at this point, any future blocks produced will skip the long
            //  running tx because they have an estimate).
            wait_for(30, || {
                Ok(mined_naka_blocks.load(Ordering::SeqCst) > mined_before)
            })
            .unwrap();

            TEST_P2P_BROADCAST_SKIP.set(true);
            let tx = make_contract_publish(
                &sender_2_sk,
                0,
                9_000,
                naka_conf.burnchain.chain_id,
                "large_contract",
                &format!(
                    "(define-constant INP_LIST (list {input_list}))
                        (define-private (mapping-fn (input int))
                                (begin (sha256 (sha256 (sha256 (sha256 (sha256 (sha256 (sha256 (sha256 (sha256 input)))))))))
                                       0))

                        (define-private (mapping-fn-2 (input int))
                                (begin (map mapping-fn INP_LIST) (map mapping-fn INP_LIST) (map mapping-fn INP_LIST) (map mapping-fn INP_LIST) 0))

                        (begin
                            (map mapping-fn-2 INP_LIST))"
                ),
            );
            submit_tx(&http_origin, &tx);

            wait_for(90, || {
                Ok(mined_naka_blocks.load(Ordering::SeqCst) > mined_before + 1)
            })
            .unwrap();

            TEST_P2P_BROADCAST_SKIP.set(false);
        } else {
            let transfer_tx = make_stacks_transfer(
                &sender_1_sk,
                i - 1,
                send_fee,
                naka_conf.burnchain.chain_id,
                &recipient,
                send_amt,
            );
            submit_tx(&http_origin, &transfer_tx);

            wait_for(30, || {
                let cur_sender_nonce = get_account(&http_origin, &sender_1_addr).nonce;
                Ok(cur_sender_nonce >= i)
            })
            .unwrap();
        }
    }

    let sender_1_nonce = get_account(&http_origin, &sender_1_addr).nonce;
    let sender_2_nonce = get_account(&http_origin, &sender_2_addr).nonce;

    // load the chain tip, and assert that it is a nakamoto block and at least 30 blocks have advanced in epoch 3
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    info!(
        "Latest tip";
        "height" => tip.stacks_block_height,
        "is_nakamoto" => tip.anchored_header.as_stacks_nakamoto().is_some(),
        "sender_1_nonce" => sender_1_nonce,
        "sender_2_nonce" => sender_2_nonce,
    );

    assert_eq!(sender_2_nonce, 0);
    assert_eq!(sender_1_nonce, 4);

    // Check that we aren't missing burn blocks (except during the Nakamoto transition)
    let bhh = u64::from(tip.burn_header_height);
    check_nakamoto_no_missing_blocks(&naka_conf, 220..=bhh);

    check_nakamoto_empty_block_heuristics();

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Verify that a node in which there is no prepare-phase block can be recovered by
/// live-instantiating shadow tenures in the prepare phase
#[test]
#[ignore]
fn test_shadow_recovery() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new(1, vec![]);
    signer_test.boot_to_epoch_3();

    let naka_conf = signer_test.running_nodes.conf.clone();
    let btc_regtest_controller = &mut signer_test.running_nodes.btc_regtest_controller;
    let counters = signer_test.running_nodes.counters.clone();

    // make another tenure
    next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

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

    let blocks_until_next_rc = prepare_phase_start + 1 - block_height
        + (btc_regtest_controller
            .get_burnchain()
            .pox_constants
            .prepare_length as u64)
        + 1;

    // kill the chain by blowing through a prepare phase
    btc_regtest_controller.bootstrap_chain(blocks_until_next_rc);
    let target_burn_height = btc_regtest_controller.get_headers_height();

    let burnchain = naka_conf.get_burnchain();
    let mut sortdb = burnchain.open_sortition_db(true).unwrap();
    let (mut chainstate, _) = StacksChainState::open(
        false,
        CHAIN_ID_TESTNET,
        &naka_conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    wait_for(30, || {
        let burn_height = get_chain_info(&naka_conf).burn_block_height;
        if burn_height >= target_burn_height {
            return Ok(true);
        }
        sleep_ms(500);
        Ok(false)
    })
    .unwrap();

    let stacks_height_before = get_chain_info(&naka_conf).stacks_tip_height;

    // TODO: stall block processing; otherwise this test can flake
    // stop block processing on the node
    TEST_COORDINATOR_STALL.lock().unwrap().replace(true);

    // fix node
    let shadow_blocks = shadow_chainstate_repair(&mut chainstate, &mut sortdb).unwrap();
    assert!(!shadow_blocks.is_empty());

    wait_for(30, || {
        let Some(info) = get_chain_info_opt(&naka_conf) else {
            sleep_ms(500);
            return Ok(false);
        };
        Ok(info.stacks_tip_height >= stacks_height_before)
    })
    .unwrap();

    TEST_COORDINATOR_STALL.lock().unwrap().replace(false);
    info!("Beginning post-shadow tenures");

    // revive ATC-C by waiting for commits
    next_block_and_commits_only(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    // make another tenure
    next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    // all shadow blocks are present and processed
    let mut shadow_ids = HashSet::new();
    for sb in shadow_blocks {
        let (_, processed, orphaned, _) = chainstate
            .nakamoto_blocks_db()
            .get_block_processed_and_signed_weight(
                &sb.header.consensus_hash,
                &sb.header.block_hash(),
            )
            .unwrap()
            .unwrap();
        assert!(processed);
        assert!(!orphaned);
        shadow_ids.insert(sb.block_id());
    }

    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), &sortdb)
        .unwrap()
        .unwrap();
    let mut cursor = tip.index_block_hash();

    // the chainstate has four parts:
    // * epoch 2
    // * epoch 3 prior to failure
    // * shadow blocks
    // * epoch 3 after recovery
    // Make sure they're all there

    let mut has_epoch_3_recovery = false;
    let mut has_shadow_blocks = false;
    let mut has_epoch_3_failure = false;

    loop {
        let header = NakamotoChainState::get_block_header(chainstate.db(), &cursor)
            .unwrap()
            .unwrap();
        if header.anchored_header.as_stacks_epoch2().is_some() {
            break;
        }

        let header = header.anchored_header.as_stacks_nakamoto().clone().unwrap();

        if header.is_shadow_block() {
            assert!(shadow_ids.contains(&header.block_id()));
        } else {
            assert!(!shadow_ids.contains(&header.block_id()));
        }

        if !header.is_shadow_block() && !has_epoch_3_recovery {
            has_epoch_3_recovery = true;
        } else if header.is_shadow_block() && has_epoch_3_recovery && !has_shadow_blocks {
            has_shadow_blocks = true;
        } else if !header.is_shadow_block()
            && has_epoch_3_recovery
            && has_shadow_blocks
            && !has_epoch_3_failure
        {
            has_epoch_3_failure = true;
        }

        cursor = header.parent_block_id;
    }

    assert!(has_epoch_3_recovery);
    assert!(has_shadow_blocks);
    assert!(has_epoch_3_failure);
}

#[test]
#[ignore]
/// Integration test for SIP-029
fn sip029_coinbase_change() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }
    let new_sched = vec![
        CoinbaseInterval {
            coinbase: 1_000_000_000,
            effective_start_height: 0,
        },
        // NOTE: epoch 3.1 goes into effect at 241
        CoinbaseInterval {
            coinbase: 500_000_000,
            effective_start_height: 245,
        },
        CoinbaseInterval {
            coinbase: 125_000_000,
            effective_start_height: 255,
        },
        CoinbaseInterval {
            coinbase: 62_500_000,
            effective_start_height: 265,
        },
    ];

    set_test_coinbase_schedule(Some(new_sched));

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    naka_conf.node.pox_sync_sample_secs = 180;
    naka_conf.burnchain.max_rbf = 10_000_000;

    let sender_sk = Secp256k1PrivateKey::random();
    let sender_signer_sk = Secp256k1PrivateKey::random();
    let sender_signer_addr = tests::to_addr(&sender_signer_sk);
    let mut signers = TestSigners::new(vec![sender_signer_sk]);
    let tenure_count = 5;
    let inter_blocks_per_tenure = 9;
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    naka_conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        (send_amt + send_fee) * tenure_count * inter_blocks_per_tenure,
    );
    naka_conf.add_initial_balance(PrincipalData::from(sender_signer_addr).to_string(), 100000);
    let stacker_sk = setup_stacker(&mut naka_conf);

    test_observer::spawn();
    test_observer::register_any(&mut naka_conf);

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

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // mine until burnchain height 270
    loop {
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and_process_new_stacks_block(&mut btc_regtest_controller, 60, &coord_channel)
            .unwrap();
        wait_for(20, || {
            Ok(commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap();

        let node_info = get_chain_info_opt(&naka_conf).unwrap();
        if node_info.burn_block_height >= 270 {
            break;
        }
    }

    info!("Nakamoto miner has advanced to burn height 270");

    // inspect `payments` table to see that coinbase was applied
    let all_snapshots = sortdb.get_all_snapshots().unwrap();

    // whether or not the last snapshot had a sortition
    let mut prev_sortition = false;

    // whether or not we witnessed the requisite coinbases
    let mut witnessed_1000 = false;
    let mut witnessed_500 = false;
    let mut witnessed_125 = false;
    let mut witnessed_62_5 = false;

    // initial mining bonus
    let initial_mining_bonus = 20400000;

    for sn in all_snapshots {
        if !sn.sortition {
            prev_sortition = false;
            continue;
        }
        if sn.consensus_hash == ConsensusHash([0x00; 20]) {
            continue;
        }
        let coinbase = {
            let sql = "SELECT coinbase FROM payments WHERE consensus_hash = ?1";
            let args = rusqlite::params![&sn.consensus_hash];
            let Some(coinbase) = chainstate
                .db()
                .query_row(sql, args, |r| {
                    let coinbase_txt: String = r.get_unwrap(0);
                    let coinbase: u64 = coinbase_txt.parse().unwrap();
                    Ok(coinbase)
                })
                .optional()
                .unwrap()
            else {
                info!("No coinbase for {} {}", sn.block_height, &sn.consensus_hash);
                continue;
            };

            coinbase
        };

        info!(
            "Coinbase at {} {}: {}",
            sn.block_height, &sn.consensus_hash, coinbase
        );
        // use >= for coinbases since a missed sortition can lead to coinbase accumulation
        if sn.block_height < 245 {
            if prev_sortition {
                assert_eq!(coinbase, 1_000_000_000 + initial_mining_bonus);
                witnessed_1000 = true;
            } else {
                assert!(coinbase >= 1_000_000_000 + initial_mining_bonus);
            }
        } else if sn.block_height < 255 {
            if prev_sortition {
                assert_eq!(coinbase, 500_000_000 + initial_mining_bonus);
                witnessed_500 = true;
            } else {
                assert!(coinbase >= 500_000_000 + initial_mining_bonus);
            }
        } else if sn.block_height < 265 {
            if prev_sortition {
                assert_eq!(coinbase, 125_000_000 + initial_mining_bonus);
                witnessed_125 = true;
            } else {
                assert!(coinbase >= 125_000_000 + initial_mining_bonus);
            }
        } else {
            if prev_sortition {
                assert_eq!(coinbase, 62_500_000 + initial_mining_bonus);
                witnessed_62_5 = true;
            } else {
                assert!(coinbase >= 62_500_000 + initial_mining_bonus);
            }
        }

        prev_sortition = true;
    }

    assert!(witnessed_1000);
    assert!(witnessed_500);
    assert!(witnessed_125);
    assert!(witnessed_62_5);

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// This test is testing that the clarity cost spend down works as expected,
/// spreading clarity contract calls across the tenure instead of all in the first block.
/// It also ensures that the clarity cost resets at the start of each tenure.
#[test]
#[ignore]
fn clarity_cost_spend_down() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut naka_conf, _miner_account) = naka_neon_integration_conf(None);
    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let num_signers = 30;
    naka_conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let sender_sks: Vec<_> = (0..num_signers)
        .map(|_| Secp256k1PrivateKey::random())
        .collect();
    let sender_signer_sks: Vec<_> = (0..num_signers)
        .map(|_| Secp256k1PrivateKey::random())
        .collect();
    let sender_signer_addrs: Vec<_> = sender_signer_sks.iter().map(tests::to_addr).collect();
    let sender_addrs: Vec<_> = sender_sks.iter().map(tests::to_addr).collect();
    let deployer_sk = sender_sks[0];
    let deployer_addr = sender_addrs[0];
    let mut sender_nonces: HashMap<String, u64> = HashMap::new();

    let get_and_increment_nonce =
        |sender_sk: &Secp256k1PrivateKey, sender_nonces: &mut HashMap<String, u64>| {
            let nonce = sender_nonces.get(&sender_sk.to_hex()).unwrap_or(&0);
            let result = *nonce;
            sender_nonces.insert(sender_sk.to_hex(), result + 1);
            result
        };
    let tenure_count = 5;
    let nmb_txs_per_signer = 2;
    let mut signers = TestSigners::new(sender_signer_sks.clone());
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let tx_fee = 10000;
    let small_deploy_fee = 190200;
    let large_deploy_fee = 570200;
    let amount =
        (large_deploy_fee + small_deploy_fee) + tx_fee * nmb_txs_per_signer + 100 * tenure_count;
    for sender_addr in sender_addrs {
        naka_conf.add_initial_balance(PrincipalData::from(sender_addr).to_string(), amount);
    }
    for sender_signer_addr in sender_signer_addrs {
        naka_conf.add_initial_balance(
            PrincipalData::from(sender_signer_addr).to_string(),
            amount * 2,
        );
    }
    naka_conf.miner.tenure_cost_limit_per_block_percentage = Some(5);
    let stacker_sks: Vec<_> = (0..num_signers)
        .map(|_| setup_stacker(&mut naka_conf))
        .collect();

    test_observer::spawn();
    test_observer::register(&mut naka_conf, &[EventKeyType::MinedBlocks]);

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
        &stacker_sks,
        &sender_signer_sks,
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("Bootstrapped to Epoch-3.0 boundary, starting nakamoto miner");

    info!("Nakamoto miner started...");
    blind_signer(&naka_conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let small_contract = format!(
        r#"
(define-data-var my-var uint u0)
(define-public (f) (begin {} (ok 1))) (begin (f))
        "#,
        ["(var-get my-var)"; 250].join(" ")
    );

    // Create an expensive contract that will be republished multiple times
    let contract_call = format!(
        "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
        boot_code_id("cost-voting", false),
        boot_code_id("costs", false),
        boot_code_id("costs", false)
    );
    let large_contract = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        [contract_call.as_str(); 250].join(" ")
    );

    // First, lets deploy the contract
    let deployer_nonce = get_and_increment_nonce(&deployer_sk, &mut sender_nonces);
    let small_contract_tx = make_contract_publish(
        &deployer_sk,
        deployer_nonce,
        large_deploy_fee,
        naka_conf.burnchain.chain_id,
        "small-contract",
        &small_contract,
    );
    submit_tx(&http_origin, &small_contract_tx);
    let deployer_nonce = get_and_increment_nonce(&deployer_sk, &mut sender_nonces);
    let large_contract_tx = make_contract_publish(
        &deployer_sk,
        deployer_nonce,
        large_deploy_fee,
        naka_conf.burnchain.chain_id,
        "big-contract",
        &large_contract,
    );
    submit_tx(&http_origin, &large_contract_tx);

    info!("----- Submitted deploy txs, mining BTC block -----");

    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    next_block_and(&mut btc_regtest_controller, 60, || {
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_count > blocks_before && blocks_processed > blocks_processed_before)
    })
    .unwrap();

    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    let mined_before = test_observer::get_mined_nakamoto_blocks();
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    info!("----- Waiting for deploy txs to be mined -----");
    wait_for(30, || {
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_processed > blocks_processed_before
            && test_observer::get_mined_nakamoto_blocks().len() > mined_before.len()
            && commits_submitted.load(Ordering::SeqCst) > commits_before)
    })
    .expect("Timed out waiting for interim blocks to be mined");

    info!("----- Mining interim blocks -----");

    // Mine `tenure_count` nakamoto tenures
    for tenure_ix in 0..tenure_count {
        info!("Mining tenure {tenure_ix}");
        // Wait for the tenure change payload to be mined
        let blocks_before = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        let commits_before = commits_submitted.load(Ordering::SeqCst);
        next_block_and(&mut btc_regtest_controller, 60, || {
            let blocks_count = mined_blocks.load(Ordering::SeqCst);
            let blocks_processed = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            Ok(blocks_count > blocks_before
                && blocks_processed > blocks_processed_before
                && commits_submitted.load(Ordering::SeqCst) > commits_before)
        })
        .unwrap();

        // mine the interim blocks
        let mined_before = test_observer::get_mined_nakamoto_blocks();
        let blocks_processed_before = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        // Pause mining so we can add all our transactions to the mempool at once.
        TEST_MINE_STALL.set(true);
        for _nmb_tx in 0..nmb_txs_per_signer {
            for sender_sk in sender_sks.iter() {
                let sender_nonce = get_and_increment_nonce(sender_sk, &mut sender_nonces);
                // Fill up the mempool with contract calls
                let contract_tx = make_contract_call(
                    sender_sk,
                    sender_nonce,
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
                        sender_nonces.insert(sender_sk.to_hex(), sender_nonce);
                    }
                }
            }
        }
        TEST_MINE_STALL.set(false);
        wait_for(120, || {
            let blocks_processed = coord_channel
                .lock()
                .expect("Mutex poisoned")
                .get_stacks_blocks_processed();
            Ok(blocks_processed >= blocks_processed_before + 7)
        })
        .expect("Timed out waiting for interim blocks to be mined");

        let mined_after = test_observer::get_mined_nakamoto_blocks();
        let mined_blocks: Vec<_> = mined_after.iter().skip(mined_before.len()).collect();
        let total_nmb_txs = mined_after.iter().map(|b| b.tx_events.len()).sum::<usize>();
        let nmb_mined_blocks = mined_blocks.len();
        debug!(
            "Mined a total of {total_nmb_txs} transactions across {nmb_mined_blocks} mined blocks"
        );
        let mut last_tx_count = None;
        for (i, block) in mined_blocks.into_iter().enumerate() {
            let tx_count = block.tx_events.len();
            if let Some(count) = last_tx_count {
                assert!(
                    tx_count <= count,
                    "Expected fewer txs to be mined each block. Last block: {count}, Current block: {tx_count}"
                );
            };
            last_tx_count = Some(tx_count);

            // All but the last transaction should hit the soft limit
            for (j, tx_event) in block.tx_events.iter().enumerate() {
                if let TransactionEvent::Success(TransactionSuccessEvent {
                    soft_limit_reached,
                    ..
                }) = tx_event
                {
                    if i == nmb_mined_blocks - 1 || j != block.tx_events.len() - 1 {
                        assert!(
                            !soft_limit_reached,
                            "Expected tx to not hit the soft limit in the very last block or in any txs but the last in all other blocks"
                        );
                    } else {
                        assert!(soft_limit_reached, "Expected tx to hit the soft limit.");
                    }
                }
            }
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
fn consensus_hash_event_dispatcher() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    conf.connection_options.auth_token = Some(password.clone());
    conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let stacker_sk = setup_stacker(&mut conf);
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    let send_amt = 100;
    let send_fee = 180;
    conf.add_initial_balance(
        PrincipalData::from(sender_addr).to_string(),
        send_amt + send_fee,
    );
    conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);

    // only subscribe to the block proposal events
    test_observer::spawn();
    test_observer::register(&mut conf, &[EventKeyType::AnyEvent]);

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
    let mut signers = TestSigners::new(vec![signer_sk]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("------------------------- Reached Epoch 3.0 -------------------------");

    blind_signer(&conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    let burnchain = conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
    let expected_consensus_hash = format!("0x{}", tip.consensus_hash);

    let burn_blocks = test_observer::get_burn_blocks();
    let burn_block = burn_blocks.last().unwrap();
    assert_eq!(
        burn_block.get("consensus_hash").unwrap().as_str().unwrap(),
        expected_consensus_hash
    );

    let stacks_blocks = test_observer::get_blocks();
    for block in stacks_blocks.iter() {
        if block.get("block_height").unwrap().as_u64().unwrap() == tip.stacks_block_height {
            assert_eq!(
                block.get("consensus_hash").unwrap().as_str().unwrap(),
                expected_consensus_hash
            );
        }
    }

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();

    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}

/// Miner wins sortition at Bitcoin height N
/// Relayer processes sortition N
/// Miner wins sortition at Bitcoin height N+1
/// Transactions that depend on the burn view get submitted to the mempool
/// A flash block at height N+2 happens before the miner can publish its block-found for N+1
/// The miner mines these transactions with a burn view for height N+2
/// Result: the miner issues a tenure-extend from N+1 with burn view for N+2
#[test]
#[ignore]
fn test_tenure_extend_from_flashblocks() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut account_keys: Vec<_> = (0..11)
        .map(|i| StacksPrivateKey::from_seed(&[6, 6, 6, i as u8]))
        .collect();
    let initial_balances: Vec<_> = account_keys
        .iter()
        .map(|privk| (to_addr(privk), 1_000_000))
        .collect();

    let deployer_sk = account_keys.pop().unwrap();
    let deployer_addr = tests::to_addr(&deployer_sk);

    let mut signer_test: SignerTest<SpawnedSigner> = SignerTest::new_with_config_modifications(
        1,
        initial_balances,
        |_| {},
        |_config| {},
        None,
        None,
    );
    signer_test.boot_to_epoch_3();

    let naka_conf = signer_test.running_nodes.conf.clone();

    let http_origin = format!("http://{}", &naka_conf.node.rpc_bind);
    let btc_regtest_controller = &mut signer_test.running_nodes.btc_regtest_controller;
    let coord_channel = signer_test.running_nodes.coord_channel.clone();
    let counters = signer_test.running_nodes.counters.clone();

    let tx_fee = 1_000;

    let burnchain = naka_conf.get_burnchain();
    let sortdb = burnchain.open_sortition_db(true).unwrap();

    for _ in 0..3 {
        next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();
    }

    let burn_view_contract = r#"
(define-data-var my-var uint u0)
(define-data-var my-counter uint u0)

(define-public (f) 
   (begin
      (var-set my-var burn-block-height)
      (if (is-eq u0 (mod burn-block-height u2))
        (var-set my-counter (+ u1 (var-get my-counter)))
        (var-set my-counter (+ u2 (var-get my-counter))))
      (print burn-block-height)
      (ok 1)
   )
)

(begin (f))
"#
    .to_string();

    let contract_tx = make_contract_publish(
        &deployer_sk,
        0,
        tx_fee,
        naka_conf.burnchain.chain_id,
        "burn-view-contract",
        &burn_view_contract,
    );
    submit_tx(&http_origin, &contract_tx);

    wait_for(120, || {
        let sender_nonce = get_account(&naka_conf.node.data_url, &deployer_addr).nonce;
        Ok(sender_nonce > 0)
    })
    .expect("Timed out waiting for interim blocks to be mined");

    next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    // stall miner and relayer

    // make tenure
    next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    // prevent the miner from sending another block-commit
    counters.naka_skip_commit_op.set(true);

    let info_before = get_chain_info(&naka_conf);

    // mine another Bitcoin block right away, since it will contain a block-commit
    btc_regtest_controller.bootstrap_chain(1);

    wait_for(120, || {
        let info = get_chain_info(&naka_conf);
        Ok(info.burn_block_height > info_before.burn_block_height
            && info.stacks_tip_height > info_before.stacks_tip_height)
    })
    .unwrap();

    let (canonical_stacks_tip_ch, _) =
        SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
    let election_tip =
        SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &canonical_stacks_tip_ch)
            .unwrap()
            .unwrap();
    let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

    // Stacks chain tip originates from the tenure started at the burnchain tip
    assert!(sort_tip.sortition);
    assert_eq!(sort_tip.consensus_hash, election_tip.consensus_hash);

    // stop the relayer thread from starting a miner thread, and stop the miner thread from mining
    TEST_MINE_STALL.set(true);
    TEST_MINER_THREAD_STALL.set(true);

    // mine another Bitcoin block right away, and force it to be a flash block
    btc_regtest_controller.bootstrap_chain(1);

    let miner_directives_before = counters.naka_miner_directives.load(Ordering::SeqCst);

    // unblock the relayer so it can process the flash block sortition.
    // Given the above, this will be an `Extend` tenure.
    TEST_MINER_THREAD_STALL.set(false);

    wait_for(60, || {
        let cur_sort_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(cur_sort_tip.block_height > sort_tip.block_height)
    })
    .unwrap();

    let (new_canonical_stacks_tip_ch, _) =
        SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
    let election_tip =
        SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &new_canonical_stacks_tip_ch)
            .unwrap()
            .unwrap();
    let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

    // this was a flash block -- no sortition
    assert!(!sort_tip.sortition);
    // canonical stacks tip burn view has not advanced
    assert_eq!(new_canonical_stacks_tip_ch, canonical_stacks_tip_ch);
    // the sortition that elected the ongoing tenure is not the canonical sortition tip
    assert_ne!(sort_tip.consensus_hash, election_tip.consensus_hash);

    let mut accounts_before = vec![];
    let mut sent_txids = vec![];

    // fill mempool with transactions that depend on the burn view
    for sender_sk in account_keys.iter() {
        let sender_addr = tests::to_addr(sender_sk);
        let account = loop {
            let Ok(account) = get_account_result(&http_origin, &sender_addr) else {
                debug!("follower_bootup: Failed to load miner account");
                thread::sleep(Duration::from_millis(100));
                continue;
            };
            break account;
        };

        // Fill up the mempool with contract calls
        let contract_tx = make_contract_call(
            sender_sk,
            account.nonce,
            tx_fee,
            naka_conf.burnchain.chain_id,
            &deployer_addr,
            "burn-view-contract",
            "f",
            &[],
        );
        let txid = submit_tx(&http_origin, &contract_tx);
        sent_txids.push(format!("0x{}", &txid.to_string()));
        accounts_before.push(account);
    }

    // unstall miner thread and allow block-commits again
    counters.naka_skip_commit_op.set(false);
    TEST_MINE_STALL.set(false);

    // wait for the miner directive to be processed
    wait_for(60, || {
        Ok(counters.naka_miner_directives.load(Ordering::SeqCst) > miner_directives_before)
    })
    .unwrap();

    // wait for all of the aforementioned transactions to get mined
    wait_for(120, || {
        // check account nonces from the sent transactions
        for (sender_sk, account_before) in account_keys.iter().zip(accounts_before.iter()) {
            let sender_addr = tests::to_addr(sender_sk);
            let account = loop {
                let Ok(account) = get_account_result(&http_origin, &sender_addr) else {
                    thread::sleep(Duration::from_millis(100));
                    continue;
                };
                break account;
            };

            if account.nonce > account_before.nonce {
                continue;
            }
            return Ok(false);
        }
        Ok(true)
    })
    .unwrap();

    // transactions are all mined, and all reflect the flash block's burn view.
    // we had a tenure-extend as well.
    let mut blocks = test_observer::get_blocks();
    blocks.sort_by_key(|block| block["block_height"].as_u64().unwrap());

    let mut included_txids = HashSet::new();
    let mut has_extend = false;
    for block in blocks.iter() {
        for tx in block.get("transactions").unwrap().as_array().unwrap() {
            let txid_str = tx.get("txid").unwrap().as_str().unwrap().to_string();
            included_txids.insert(txid_str);

            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();

            if let TransactionPayload::TenureChange(payload) = &parsed.payload {
                if payload.cause == TenureChangeCause::Extended {
                    has_extend = true;
                }
            }
        }
    }

    assert!(has_extend);

    let expected_txids: HashSet<_> = sent_txids.clone().into_iter().collect();
    for expected_txid in expected_txids.iter() {
        if !included_txids.contains(expected_txid) {
            panic!("Missing {}", expected_txid);
        }
    }

    // mine one additional tenure, to verify that we're on track
    next_block_and_mine_commit(btc_regtest_controller, 60, &naka_conf, &counters).unwrap();

    // boot a follower. it should reach the chain tip
    info!("----- BEGIN FOLLOWR BOOTUP ------");

    // see if we can boot a follower off of this node now
    let mut follower_conf = naka_conf.clone();
    follower_conf.node.miner = false;
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &naka_conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    let rpc_port = gen_random_port();
    let p2p_port = gen_random_port();

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{localhost}:{rpc_port}");
    follower_conf.node.p2p_bind = format!("{localhost}:{p2p_port}");
    follower_conf.node.data_url = format!("http://{localhost}:{rpc_port}");
    follower_conf.node.p2p_address = format!("{localhost}:{p2p_port}");
    follower_conf.node.pox_sync_sample_secs = 30;

    let node_info = get_chain_info(&naka_conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            naka_conf.node.p2p_bind
        ),
        naka_conf.burnchain.chain_id,
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

    wait_for(300, || {
        let miner_info = get_chain_info_result(&naka_conf).unwrap();
        let Ok(info) = get_chain_info_result(&follower_conf) else {
            sleep_ms(1000);
            return Ok(false);
        };
        debug!(
            "Miner tip is {}/{}; follower tip is {}/{}",
            &miner_info.stacks_tip_consensus_hash,
            &miner_info.stacks_tip,
            &info.stacks_tip_consensus_hash,
            &info.stacks_tip
        );
        Ok(miner_info.stacks_tip == info.stacks_tip
            && miner_info.stacks_tip_consensus_hash == info.stacks_tip_consensus_hash)
    })
    .unwrap();

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();

    follower_coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    follower_run_loop_stopper.store(false, Ordering::SeqCst);

    follower_thread.join().unwrap();
}

/// Mine a smart contract transaction with a call to `from-consensus-buff?` that would decode to an
/// invalid Principal. Verify that this transaction is dropped from the mempool.
#[test]
#[ignore]
fn mine_invalid_principal_from_consensus_buff() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = naka_neon_integration_conf(None);
    let password = "12345".to_string();
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    conf.connection_options.auth_token = Some(password.clone());
    conf.miner.wait_on_interim_blocks = Duration::from_secs(1);
    let stacker_sk = setup_stacker(&mut conf);
    let signer_sk = Secp256k1PrivateKey::random();
    let signer_addr = tests::to_addr(&signer_sk);
    let sender_sk = Secp256k1PrivateKey::random();
    // setup sender + recipient for some test stx transfers
    // these are necessary for the interim blocks to get mined at all
    let sender_addr = tests::to_addr(&sender_sk);
    conf.add_initial_balance(PrincipalData::from(sender_addr).to_string(), 1000000);
    conf.add_initial_balance(PrincipalData::from(signer_addr).to_string(), 100000);

    test_observer::spawn();
    test_observer::register(&mut conf, &[EventKeyType::AnyEvent]);

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
        naka_mined_blocks: mined_blocks,
        ..
    } = run_loop.counters();

    let coord_channel = run_loop.coordinator_channels();

    let run_loop_thread = thread::spawn(move || run_loop.start(None, 0));
    let mut signers = TestSigners::new(vec![signer_sk]);
    wait_for_runloop(&blocks_processed);
    boot_to_epoch_3(
        &conf,
        &blocks_processed,
        &[stacker_sk],
        &[signer_sk],
        &mut Some(&mut signers),
        &mut btc_regtest_controller,
    );

    info!("------------------------- Reached Epoch 3.0 -------------------------");

    blind_signer(&conf, &signers, proposals_submitted);

    wait_for_first_naka_block_commit(60, &commits_submitted);

    // submit faulty contract
    let contract = "(print (from-consensus-buff? principal 0x062011deadbeef11ababffff11deadbeef11ababffff0461626364))";

    let contract_tx_bytes = make_contract_publish(
        &sender_sk,
        0,
        1024,
        conf.burnchain.chain_id,
        "contract",
        contract,
    );
    submit_tx(&http_origin, &contract_tx_bytes);

    let contract_tx =
        StacksTransaction::consensus_deserialize(&mut &contract_tx_bytes[..]).unwrap();

    // mine one more block
    let blocks_before = mined_blocks.load(Ordering::SeqCst);
    let blocks_processed_before = coord_channel
        .lock()
        .expect("Mutex poisoned")
        .get_stacks_blocks_processed();
    let commits_before = commits_submitted.load(Ordering::SeqCst);
    next_block_and(&mut btc_regtest_controller, 60, || {
        let blocks_count = mined_blocks.load(Ordering::SeqCst);
        let blocks_processed = coord_channel
            .lock()
            .expect("Mutex poisoned")
            .get_stacks_blocks_processed();
        Ok(blocks_count > blocks_before
            && blocks_processed > blocks_processed_before
            && commits_submitted.load(Ordering::SeqCst) > commits_before)
    })
    .unwrap();

    let dropped_txs = test_observer::get_memtx_drops();

    // we identified and dropped the offending tx as problematic
    debug!("dropped_txs: {:?}", &dropped_txs);
    assert_eq!(dropped_txs.len(), 1);
    assert_eq!(dropped_txs[0].0, format!("0x{}", &contract_tx.txid()));
    assert_eq!(dropped_txs[0].1.as_str(), "Problematic");

    coord_channel
        .lock()
        .expect("Mutex poisoned")
        .stop_chains_coordinator();
    run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
}
