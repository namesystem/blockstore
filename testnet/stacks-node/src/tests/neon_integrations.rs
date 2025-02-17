use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{mpsc, Arc};
use std::time::{Duration, Instant};
use std::{cmp, env, fs, io, thread};

use clarity::vm::ast::stack_depth_checker::AST_CALL_STACK_DEPTH_BUFFER;
use clarity::vm::ast::ASTRules;
use clarity::vm::costs::ExecutionCost;
use clarity::vm::types::serialization::SerializationError;
use clarity::vm::types::PrincipalData;
use clarity::vm::{ClarityName, ClarityVersion, ContractName, Value, MAX_CALL_STACK_DEPTH};
use rand::Rng;
use rusqlite::params;
use serde::Deserialize;
use serde_json::json;
use stacks::burnchains::bitcoin::address::{BitcoinAddress, LegacyBitcoinAddressType};
use stacks::burnchains::bitcoin::BitcoinNetworkType;
use stacks::burnchains::db::BurnchainDB;
use stacks::burnchains::{Address, Burnchain, PoxConstants, Txid};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::operations::{
    BlockstackOperationType, DelegateStxOp, PreStxOp, StackStxOp, TransferStxOp,
    VoteForAggregateKeyOp,
};
use stacks::chainstate::burn::ConsensusHash;
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::chainstate::stacks::address::PoxAddress;
use stacks::chainstate::stacks::boot::POX_4_NAME;
use stacks::chainstate::stacks::db::StacksChainState;
use stacks::chainstate::stacks::miner::{
    signal_mining_blocked, signal_mining_ready, TransactionErrorEvent, TransactionEvent,
    TransactionSuccessEvent,
};
use stacks::chainstate::stacks::{
    StacksBlock, StacksBlockHeader, StacksMicroblock, StacksMicroblockHeader, StacksPrivateKey,
    StacksPublicKey, StacksTransaction, TransactionContractCall, TransactionPayload,
};
use stacks::clarity_cli::vm_execute as execute;
use stacks::cli;
use stacks::codec::StacksMessageCodec;
use stacks::config::{EventKeyType, EventObserverConfig, FeeEstimatorName, InitialBalance};
use stacks::core::mempool::MemPoolWalkTxTypes;
use stacks::core::{
    self, EpochList, StacksEpoch, StacksEpochId, BLOCK_LIMIT_MAINNET_20, BLOCK_LIMIT_MAINNET_205,
    BLOCK_LIMIT_MAINNET_21, CHAIN_ID_TESTNET, HELIUM_BLOCK_LIMIT_20, PEER_VERSION_EPOCH_1_0,
    PEER_VERSION_EPOCH_2_0, PEER_VERSION_EPOCH_2_05, PEER_VERSION_EPOCH_2_1,
    PEER_VERSION_EPOCH_2_2, PEER_VERSION_EPOCH_2_3, PEER_VERSION_EPOCH_2_4, PEER_VERSION_EPOCH_2_5,
    PEER_VERSION_TESTNET,
};
use stacks::net::api::getaccount::AccountEntryResponse;
use stacks::net::api::getcontractsrc::ContractSrcResponse;
use stacks::net::api::getinfo::RPCPeerInfoData;
use stacks::net::api::getpoxinfo::RPCPoxInfoData;
use stacks::net::api::getsortition::SortitionInfo;
use stacks::net::api::gettransaction_unconfirmed::UnconfirmedTransactionResponse;
use stacks::net::api::postblock::StacksBlockAcceptedData;
use stacks::net::api::postfeerate::RPCFeeEstimateResponse;
use stacks::net::api::posttransaction::PostTransactionRequestBody;
use stacks::net::atlas::{
    AtlasConfig, AtlasDB, GetAttachmentResponse, GetAttachmentsInvResponse,
    MAX_ATTACHMENT_INV_PAGES_PER_REQUEST,
};
use stacks::types::PublicKey;
use stacks::util_lib::boot::{boot_code_addr, boot_code_id};
use stacks::util_lib::db::{query_row_columns, query_rows, u64_to_sql};
use stacks::util_lib::signed_structured_data::pox4::{
    make_pox_4_signer_key_signature, Pox4SignatureTopic,
};
use stacks_common::address::AddressHashMode;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksAddress, StacksBlockId,
};
use stacks_common::types::StacksPublicKeyBuffer;
use stacks_common::util::hash::{bytes_to_hex, hex_bytes, to_hex, Hash160};
use stacks_common::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks_common::util::{get_epoch_time_ms, get_epoch_time_secs, sleep_ms};

use super::bitcoin_regtest::BitcoinCoreController;
use super::{
    make_contract_call, make_contract_publish, make_contract_publish_microblock_only,
    make_microblock, make_stacks_transfer, make_stacks_transfer_mblock_only, to_addr, ADDR_4, SK_1,
    SK_2, SK_3,
};
use crate::burnchains::bitcoin_regtest_controller::{self, addr2str, BitcoinRPCRequest, UTXO};
use crate::neon_node::RelayerThread;
use crate::operations::BurnchainOpSigner;
use crate::stacks_common::types::PrivateKey;
use crate::syncctl::PoxSyncWatchdogComms;
use crate::tests::gen_random_port;
use crate::tests::nakamoto_integrations::{get_key_for_cycle, wait_for};
use crate::util::hash::{MerkleTree, Sha512Trunc256Sum};
use crate::util::secp256k1::MessageSignature;
use crate::{neon, BitcoinRegtestController, BurnchainController, Config, ConfigFile, Keychain};

fn inner_neon_integration_test_conf(seed: Option<Vec<u8>>) -> (Config, StacksAddress) {
    let mut conf = super::new_test_conf();

    // tests can override this, but these tests run with epoch 2.05 by default
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1000,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1000,
            end_height: 1000000 - 1,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 1000000 - 1,
            end_height: 9223372036854775807,
            block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));

    let seed = seed.unwrap_or(conf.node.seed.clone());
    conf.node.seed = seed;

    let keychain = Keychain::default(conf.node.seed.clone());

    conf.node.miner = true;
    conf.node.wait_time_for_microblocks = 500;
    conf.burnchain.burn_fee_cap = 20000;

    conf.burnchain.mode = "neon".into();
    conf.burnchain.username = Some("neon-tester".into());
    conf.burnchain.password = Some("neon-tester-pass".into());
    conf.burnchain.peer_host = "127.0.0.1".into();
    conf.burnchain.local_mining_public_key =
        Some(keychain.generate_op_signer().get_public_key().to_hex());
    conf.burnchain.commit_anchor_block_within = 0;

    // test to make sure config file parsing is correct
    let mut cfile = ConfigFile::xenon();
    cfile.node.as_mut().map(|node| node.bootstrap_node.take());

    if let Some(burnchain) = cfile.burnchain.as_mut() {
        burnchain.peer_host = Some("127.0.0.1".to_string());
    }

    let magic_bytes = Config::from_config_file(cfile, false)
        .unwrap()
        .burnchain
        .magic_bytes;
    assert_eq!(magic_bytes.as_bytes(), b"T2");
    conf.burnchain.magic_bytes = magic_bytes;
    conf.burnchain.poll_time_secs = 1;
    conf.node.pox_sync_sample_secs = 0;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    // if there's just one node, then this must be true for tests to pass
    conf.miner.wait_for_block_download = false;

    conf.node.mine_microblocks = true;
    conf.miner.microblock_attempt_time_ms = 2_000;
    conf.node.microblock_frequency = 0;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_blocks = 1_000;

    let miner_account = keychain.origin_address(conf.is_mainnet()).unwrap();

    (conf, miner_account)
}

pub fn neon_integration_test_conf() -> (Config, StacksAddress) {
    inner_neon_integration_test_conf(None)
}

pub fn neon_integration_test_conf_with_seed(seed: Vec<u8>) -> (Config, StacksAddress) {
    inner_neon_integration_test_conf(Some(seed))
}

pub mod test_observer {
    use std::collections::HashSet;
    use std::convert::Infallible;
    use std::ops::{Bound, RangeBounds};
    use std::sync::Mutex;
    use std::thread;

    use stacks::chainstate::stacks::boot::RewardSet;
    use stacks::chainstate::stacks::events::StackerDBChunksEvent;
    use stacks::chainstate::stacks::StacksTransaction;
    use stacks::codec::StacksMessageCodec;
    use stacks::config::{EventKeyType, EventObserverConfig};
    use stacks::net::api::postblock_proposal::BlockValidateResponse;
    use stacks::util::hash::hex_bytes;
    use stacks_common::types::chainstate::StacksBlockId;
    use warp::Filter;
    use {tokio, warp};

    use crate::event_dispatcher::{MinedBlockEvent, MinedMicroblockEvent, MinedNakamotoBlockEvent};
    use crate::Config;

    pub const EVENT_OBSERVER_PORT: u16 = 50303;

    pub static NEW_BLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
    pub static MINED_BLOCKS: Mutex<Vec<MinedBlockEvent>> = Mutex::new(Vec::new());
    pub static MINED_MICROBLOCKS: Mutex<Vec<MinedMicroblockEvent>> = Mutex::new(Vec::new());
    pub static MINED_NAKAMOTO_BLOCKS: Mutex<Vec<MinedNakamotoBlockEvent>> = Mutex::new(Vec::new());
    pub static NEW_MICROBLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
    pub static NEW_STACKERDB_CHUNKS: Mutex<Vec<StackerDBChunksEvent>> = Mutex::new(Vec::new());
    pub static BURN_BLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
    pub static MEMTXS: Mutex<Vec<String>> = Mutex::new(Vec::new());
    pub static MEMTXS_DROPPED: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());
    pub static ATTACHMENTS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
    pub static PROPOSAL_RESPONSES: Mutex<Vec<BlockValidateResponse>> = Mutex::new(Vec::new());
    pub static STACKER_SETS: Mutex<Vec<(StacksBlockId, u64, RewardSet)>> = Mutex::new(Vec::new());

    async fn handle_proposal_response(
        response: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        info!("Proposal response received"; "response" => %response);
        PROPOSAL_RESPONSES.lock().unwrap().push(
            serde_json::from_value(response)
                .expect("Failed to deserialize JSON into BlockValidateResponse"),
        );
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_burn_block(
        burn_block: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut blocks = BURN_BLOCKS.lock().unwrap();
        blocks.push(burn_block);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_block(block: serde_json::Value) -> Result<impl warp::Reply, Infallible> {
        let mut blocks = NEW_BLOCKS.lock().unwrap();
        blocks.push(block);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_microblocks(
        microblocks: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut microblock_events = NEW_MICROBLOCKS.lock().unwrap();
        microblock_events.push(microblocks);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_stackerdb_chunks(
        chunks: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        debug!(
            "signer_runloop: got stackerdb chunks: {}",
            serde_json::to_string(&chunks).unwrap()
        );
        let event: StackerDBChunksEvent = serde_json::from_value(chunks).unwrap();
        let mut stackerdb_chunks = NEW_STACKERDB_CHUNKS.lock().unwrap();
        stackerdb_chunks.push(event);

        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mined_block(block: serde_json::Value) -> Result<impl warp::Reply, Infallible> {
        let mut mined_blocks = MINED_BLOCKS.lock().unwrap();
        // assert that the mined transaction events have string-y txids
        block
            .as_object()
            .expect("Expected JSON object for mined block event")
            .get("tx_events")
            .expect("Expected tx_events key in mined block event")
            .as_array()
            .expect("Expected tx_events key to be an array in mined block event")
            .iter()
            .for_each(|txevent| {
                let txevent_obj = txevent.as_object().expect("TransactionEvent should be object");
                let inner_obj = if let Some(inner_obj) = txevent_obj.get("Success") {
                    inner_obj
                } else if let Some(inner_obj) = txevent_obj.get("ProcessingError") {
                    inner_obj
                } else if let Some(inner_obj) = txevent_obj.get("Skipped") {
                    inner_obj
                } else {
                    panic!("TransactionEvent object should have one of Success, ProcessingError, or Skipped")
                };
                inner_obj
                    .as_object()
                    .expect("TransactionEvent should be an object")
                    .get("txid")
                    .expect("Should have txid key")
                    .as_str()
                    .expect("Expected txid to be a string");
            });

        mined_blocks.push(serde_json::from_value(block).unwrap());
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_pox_stacker_set(
        stacker_set: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut stacker_sets = STACKER_SETS.lock().unwrap();
        let block_id = stacker_set
            .as_object()
            .expect("Expected JSON object for stacker set event")
            .get("block_id")
            .expect("Expected block_id field")
            .as_str()
            .expect("Expected string for block id")
            .to_string();
        let block_id = StacksBlockId::from_hex(&block_id)
            .expect("Failed to parse block id field as StacksBlockId hex");
        let cycle_number = stacker_set
            .as_object()
            .expect("Expected JSON object for stacker set event")
            .get("cycle_number")
            .expect("Expected field")
            .as_u64()
            .expect("Expected u64 for cycle number");
        let stacker_set = serde_json::from_value(
            stacker_set
                .as_object()
                .expect("Expected JSON object for stacker set event")
                .get("stacker_set")
                .expect("Expected field")
                .clone(),
        )
        .expect("Failed to parse stacker set object");
        stacker_sets.push((block_id, cycle_number, stacker_set));
        Ok(warp::http::StatusCode::OK)
    }

    /// Called by the process listening to events on a mined microblock event. The event is added
    /// to the mutex-guarded vector `MINED_MICROBLOCKS`.
    async fn handle_mined_microblock(
        tx_event: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut mined_txs = MINED_MICROBLOCKS.lock().unwrap();
        mined_txs.push(serde_json::from_value(tx_event).unwrap());
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mined_nakamoto_block(
        block: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut mined_blocks = MINED_NAKAMOTO_BLOCKS.lock().unwrap();
        // assert that the mined transaction events have string-y txids
        block
            .as_object()
            .expect("Expected JSON object for mined nakamoto block event")
            .get("tx_events")
            .expect("Expected tx_events key in mined nakamoto block event")
            .as_array()
            .expect("Expected tx_events key to be an array in mined nakamoto block event")
            .iter()
            .for_each(|txevent| {
                let txevent_obj = txevent.as_object().expect("TransactionEvent should be object");
                let inner_obj = if let Some(inner_obj) = txevent_obj.get("Success") {
                    inner_obj
                } else if let Some(inner_obj) = txevent_obj.get("ProcessingError") {
                    inner_obj
                } else if let Some(inner_obj) = txevent_obj.get("Skipped") {
                    inner_obj
                } else if let Some(inner_obj) = txevent_obj.get("Problematic") {
                    inner_obj
                } else {
                    panic!("TransactionEvent object should have one of Success, ProcessingError, Skipped, or Problematic. Had keys: {:?}", txevent_obj.keys().map(|x| x.to_string()).collect::<Vec<_>>());
                };
                inner_obj
                    .as_object()
                    .expect("TransactionEvent should be an object")
                    .get("txid")
                    .expect("Should have txid key")
                    .as_str()
                    .expect("Expected txid to be a string");
            });

        mined_blocks.push(serde_json::from_value(block).unwrap());
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mempool_txs(txs: serde_json::Value) -> Result<impl warp::Reply, Infallible> {
        let new_rawtxs = txs
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string());
        let mut memtxs = MEMTXS.lock().unwrap();
        for new_tx in new_rawtxs {
            memtxs.push(new_tx);
        }
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mempool_drop_txs(
        txs: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let dropped_txids = txs
            .get("dropped_txids")
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string());
        let reason = txs.get("reason").unwrap().as_str().unwrap().to_string();

        let mut memtxs = MEMTXS_DROPPED.lock().unwrap();
        for new_tx in dropped_txids {
            memtxs.push((new_tx, reason.clone()));
        }
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_attachments(
        attachments: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let new_attachments = attachments.as_array().unwrap();
        let mut attachments = ATTACHMENTS.lock().unwrap();
        for new_attachment in new_attachments {
            attachments.push(new_attachment.clone());
        }
        Ok(warp::http::StatusCode::OK)
    }

    pub fn get_stacker_sets() -> Vec<(StacksBlockId, u64, RewardSet)> {
        STACKER_SETS.lock().unwrap().clone()
    }

    pub fn get_memtxs() -> Vec<String> {
        MEMTXS.lock().unwrap().clone()
    }

    pub fn get_memtx_drops() -> Vec<(String, String)> {
        MEMTXS_DROPPED.lock().unwrap().clone()
    }

    pub fn get_blocks() -> Vec<serde_json::Value> {
        NEW_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_microblocks() -> Vec<serde_json::Value> {
        NEW_MICROBLOCKS.lock().unwrap().clone()
    }

    pub fn get_burn_blocks() -> Vec<serde_json::Value> {
        BURN_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_attachments() -> Vec<serde_json::Value> {
        ATTACHMENTS.lock().unwrap().clone()
    }

    pub fn get_mined_blocks() -> Vec<MinedBlockEvent> {
        MINED_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_mined_microblocks() -> Vec<MinedMicroblockEvent> {
        MINED_MICROBLOCKS.lock().unwrap().clone()
    }

    pub fn get_mined_nakamoto_blocks() -> Vec<MinedNakamotoBlockEvent> {
        MINED_NAKAMOTO_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_stackerdb_chunks() -> Vec<StackerDBChunksEvent> {
        NEW_STACKERDB_CHUNKS.lock().unwrap().clone()
    }

    pub fn get_proposal_responses() -> Vec<BlockValidateResponse> {
        PROPOSAL_RESPONSES.lock().unwrap().clone()
    }

    /// each path here should correspond to one of the paths listed in `event_dispatcher.rs`
    async fn serve(port: u16) {
        let new_blocks = warp::path!("new_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_block);
        let mempool_txs = warp::path!("new_mempool_tx")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mempool_txs);
        let mempool_drop_txs = warp::path!("drop_mempool_tx")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mempool_drop_txs);
        let new_burn_blocks = warp::path!("new_burn_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_burn_block);
        let new_attachments = warp::path!("attachments" / "new")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_attachments);
        let new_microblocks = warp::path!("new_microblocks")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_microblocks);
        let mined_blocks = warp::path!("mined_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mined_block);
        let mined_nakamoto_blocks = warp::path!("mined_nakamoto_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mined_nakamoto_block);
        let mined_microblocks = warp::path!("mined_microblock")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mined_microblock);
        let new_stackerdb_chunks = warp::path!("stackerdb_chunks")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_stackerdb_chunks);
        let block_proposals = warp::path!("proposal_response")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_proposal_response);
        let stacker_sets = warp::path!("new_pox_set")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_pox_stacker_set);

        info!("Spawning event-observer warp server");
        warp::serve(
            new_blocks
                .or(mempool_txs)
                .or(mempool_drop_txs)
                .or(new_burn_blocks)
                .or(new_attachments)
                .or(new_microblocks)
                .or(mined_blocks)
                .or(mined_microblocks)
                .or(mined_nakamoto_blocks)
                .or(new_stackerdb_chunks)
                .or(block_proposals)
                .or(stacker_sets),
        )
        .run(([127, 0, 0, 1], port))
        .await
    }

    pub fn spawn() {
        clear();
        thread::spawn(|| {
            let rt = tokio::runtime::Runtime::new().expect("Failed to initialize tokio");
            rt.block_on(serve(EVENT_OBSERVER_PORT));
        });
    }

    pub fn spawn_at(port: u16) {
        clear();
        thread::spawn(move || {
            let rt = tokio::runtime::Runtime::new().expect("Failed to initialize tokio");
            rt.block_on(serve(port));
        });
    }

    pub fn clear() {
        NEW_BLOCKS.lock().unwrap().clear();
        MINED_BLOCKS.lock().unwrap().clear();
        MINED_MICROBLOCKS.lock().unwrap().clear();
        NEW_MICROBLOCKS.lock().unwrap().clear();
        NEW_STACKERDB_CHUNKS.lock().unwrap().clear();
        BURN_BLOCKS.lock().unwrap().clear();
        MEMTXS.lock().unwrap().clear();
        MEMTXS_DROPPED.lock().unwrap().clear();
        ATTACHMENTS.lock().unwrap().clear();
        PROPOSAL_RESPONSES.lock().unwrap().clear();
    }

    /// Parse the StacksTransactions from a block (does not include burn ops or phantom txs)
    ///  panics on any failures to parse
    pub fn parse_transactions(block: &serde_json::Value) -> Vec<StacksTransaction> {
        block
            .get("transactions")
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|tx_json| {
                // Filter out burn ops
                if let Some(burnchain_op_val) = tx_json.get("burnchain_op") {
                    if !burnchain_op_val.is_null() {
                        return None;
                    }
                }
                // Filter out phantom txs
                let tx_hex = tx_json.get("raw_tx").unwrap().as_str().unwrap();
                let tx_bytes = hex_bytes(&tx_hex[2..]).unwrap();
                let tx =
                    StacksTransaction::consensus_deserialize(&mut tx_bytes.as_slice()).unwrap();
                if tx.is_phantom() {
                    return None;
                }
                Some(tx)
            })
            .collect()
    }

    /// Get missing burn blocks for a given height range
    /// Returns Ok(..) if lookup is sucessful, whether there are missing blocks or not
    pub fn get_missing_burn_blocks(range: impl RangeBounds<u64>) -> Result<Vec<u64>, String> {
        // Get set of all burn block heights
        let burn_block_heights = get_blocks()
            .into_iter()
            .map(|x| x.get("burn_block_height").unwrap().as_u64().unwrap())
            .collect::<HashSet<_>>();

        let start = match range.start_bound() {
            Bound::Unbounded => return Err("Unbounded ranges not supported".into()),
            Bound::Included(&x) => x,
            Bound::Excluded(&x) => x.saturating_add(1),
        };

        let end = match range.end_bound() {
            Bound::Unbounded => return Err("Unbounded ranges not supported".into()),
            Bound::Included(&x) => x,
            Bound::Excluded(&x) => x.saturating_sub(1),
        };

        // Find indexes in range for which we don't have burn block in set
        let missing = (start..=end)
            .filter(|i| !burn_block_heights.contains(i))
            .collect();

        Ok(missing)
    }

    /// Similar to `missing_burn_blocks()` but returns `Err(..)` if blocks are missing
    pub fn contains_burn_block_range(range: impl RangeBounds<u64> + Clone) -> Result<(), String> {
        let missing = self::get_missing_burn_blocks(range.clone())?;

        if missing.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "Missing the following burn blocks from {:?} to {:?}: {missing:?}",
                range.start_bound(),
                range.end_bound()
            ))
        }
    }

    pub fn register(config: &mut Config, event_keys: &[EventKeyType]) {
        config.events_observers.insert(EventObserverConfig {
            endpoint: format!("localhost:{EVENT_OBSERVER_PORT}"),
            events_keys: event_keys.to_vec(),
            timeout_ms: 1000,
            lossy: false,
        });
    }

    pub fn register_any(config: &mut Config) {
        self::register(config, &[EventKeyType::AnyEvent]);
    }
}

const PANIC_TIMEOUT_SECS: u64 = 600;

/// Returns `false` on a timeout, true otherwise.
pub fn next_block_and_wait(
    btc_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
) -> bool {
    next_block_and_wait_with_timeout(btc_controller, blocks_processed, PANIC_TIMEOUT_SECS)
}

/// Returns `false` on a timeout, true otherwise.
pub fn next_block_and_wait_with_timeout(
    btc_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
    timeout: u64,
) -> bool {
    let current = blocks_processed.load(Ordering::SeqCst);
    info!(
        "Issuing block at {}, waiting for bump ({current})",
        get_epoch_time_secs()
    );
    btc_controller.build_next_block(1);
    let start = Instant::now();
    while blocks_processed.load(Ordering::SeqCst) <= current {
        if start.elapsed() > Duration::from_secs(timeout) {
            error!("Timed out waiting for block to process, trying to continue test");
            return false;
        }
        thread::sleep(Duration::from_millis(100));
    }
    info!(
        "Block bumped at {} ({})",
        get_epoch_time_secs(),
        blocks_processed.load(Ordering::SeqCst)
    );
    true
}

/// Returns `false` on a timeout, true otherwise.
pub fn next_block_and_iterate(
    btc_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
    iteration_delay_ms: u64,
) -> bool {
    let current = blocks_processed.load(Ordering::SeqCst);
    eprintln!(
        "Issuing block at {}, waiting for bump ({current})",
        get_epoch_time_secs()
    );
    btc_controller.build_next_block(1);
    let start = Instant::now();
    while blocks_processed.load(Ordering::SeqCst) <= current {
        if start.elapsed() > Duration::from_secs(PANIC_TIMEOUT_SECS) {
            error!("Timed out waiting for block to process, trying to continue test");
            return false;
        }
        thread::sleep(Duration::from_millis(iteration_delay_ms));
        btc_controller.build_next_block(1);
    }
    eprintln!(
        "Block bumped at {} ({})",
        get_epoch_time_secs(),
        blocks_processed.load(Ordering::SeqCst)
    );
    true
}

/// This function will call `next_block_and_wait` until the burnchain height underlying `BitcoinRegtestController`
/// reaches *exactly* `target_height`.
///
/// Returns `false` if `next_block_and_wait` times out.
pub fn run_until_burnchain_height(
    btc_regtest_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
    target_height: u64,
    conf: &Config,
) -> bool {
    let tip_info = get_chain_info(conf);
    let mut current_height = tip_info.burn_block_height;

    while current_height < target_height {
        eprintln!(
            "run_until_burnchain_height: Issuing block at {}, current_height burnchain height is ({current_height})",
            get_epoch_time_secs(),
        );
        let next_result = next_block_and_wait(btc_regtest_controller, blocks_processed);
        if !next_result {
            return false;
        }
        let Ok(tip_info) = get_chain_info_result(conf) else {
            sleep_ms(1000);
            continue;
        };
        current_height = tip_info.burn_block_height;
    }

    assert_eq!(current_height, target_height);
    true
}

pub fn wait_for_runloop(blocks_processed: &Arc<AtomicU64>) {
    let start = Instant::now();
    while blocks_processed.load(Ordering::SeqCst) == 0 {
        if start.elapsed() > Duration::from_secs(PANIC_TIMEOUT_SECS) {
            panic!("Timed out waiting for run loop to start");
        }
        thread::sleep(Duration::from_millis(100));
    }
}

/// Wait for at least one microblock to be mined, up to a given timeout (in seconds).
/// Returns true if the microblock was mined; false if we timed out.
pub fn wait_for_microblocks(microblocks_processed: &Arc<AtomicU64>, timeout: u64) -> bool {
    let mut current = microblocks_processed.load(Ordering::SeqCst);
    let start = Instant::now();
    info!("Waiting for next microblock (current = {current})");
    loop {
        let now = microblocks_processed.load(Ordering::SeqCst);
        if now == 0 && current != 0 {
            // wrapped around -- a new epoch started
            info!("New microblock epoch started while waiting (originally {current})");
            current = 0;
        }

        if now > current {
            break;
        }

        if start.elapsed() > Duration::from_secs(timeout) {
            warn!("Timed out waiting for microblocks to process ({timeout})");
            return false;
        }

        thread::sleep(Duration::from_millis(100));
    }
    info!("Next microblock acknowledged");
    true
}

/// returns Txid string upon success
pub fn submit_tx_fallible(http_origin: &str, tx: &[u8]) -> Result<String, String> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/transactions");
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx.to_vec())
        .send()
        .unwrap();
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx[..])
                .unwrap()
                .txid()
                .to_string()
        );
        Ok(res)
    } else {
        Err(res.text().unwrap())
    }
}

/// returns Txid string
pub fn submit_tx(http_origin: &str, tx: &[u8]) -> String {
    submit_tx_fallible(http_origin, tx).unwrap_or_else(|e| {
        eprintln!("Submit tx error: {e}");
        panic!("");
    })
}

pub fn get_unconfirmed_tx(http_origin: &str, txid: &Txid) -> Option<String> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/transactions/unconfirmed/{txid}");
    let res = client.get(&path).send().unwrap();

    if res.status().is_success() {
        let res: UnconfirmedTransactionResponse = res.json().unwrap();
        Some(res.tx)
    } else {
        None
    }
}

pub fn submit_block(
    http_origin: &str,
    consensus_hash: &ConsensusHash,
    block: &[u8],
) -> StacksBlockAcceptedData {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/blocks/upload/{consensus_hash}");
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(block.to_owned())
        .send()
        .unwrap();

    if res.status().is_success() {
        let res: StacksBlockAcceptedData = res.json().unwrap();
        assert_eq!(
            res.stacks_block_id,
            StacksBlockId::new(
                consensus_hash,
                &StacksBlock::consensus_deserialize(&mut &block[..])
                    .unwrap()
                    .block_hash()
            )
        );
        res
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }
}

pub fn submit_microblock(http_origin: &str, mblock: &[u8]) -> BlockHeaderHash {
    let client = reqwest::blocking::Client::new();
    let microblock = StacksMicroblock::consensus_deserialize(&mut &mblock[..]).unwrap();
    let path = format!("{http_origin}/v2/microblocks/{}", microblock.block_hash());
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(mblock.to_owned())
        .send()
        .unwrap();

    if res.status().is_success() {
        let res: BlockHeaderHash = res.json().unwrap();
        assert_eq!(
            res,
            StacksMicroblock::consensus_deserialize(&mut &mblock[..])
                .unwrap()
                .block_hash()
        );
        res
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }
}

pub fn get_block(http_origin: &str, block_id: &StacksBlockId) -> Option<StacksBlock> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/blocks/{block_id}");
    let res = client.get(&path).send().unwrap();

    if res.status().is_success() {
        let res: Vec<u8> = res.bytes().unwrap().to_vec();
        let block = StacksBlock::consensus_deserialize(&mut &res[..]).unwrap();
        Some(block)
    } else {
        None
    }
}

pub fn get_chain_info_result(conf: &Config) -> Result<RPCPeerInfoData, reqwest::Error> {
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let client = reqwest::blocking::Client::new();

    // get the canonical chain tip
    let path = format!("{http_origin}/v2/info");
    client.get(&path).send()?.json::<RPCPeerInfoData>()
}

pub fn get_chain_info_opt(conf: &Config) -> Option<RPCPeerInfoData> {
    get_chain_info_result(conf).ok()
}

pub fn get_chain_info(conf: &Config) -> RPCPeerInfoData {
    get_chain_info_result(conf).unwrap()
}

pub fn get_tip_anchored_block(conf: &Config) -> (ConsensusHash, StacksBlock) {
    let tip_info = get_chain_info(conf);

    // get the canonical chain tip
    let stacks_tip = tip_info.stacks_tip;
    let stacks_tip_consensus_hash = tip_info.stacks_tip_consensus_hash;

    let stacks_id_tip =
        StacksBlockHeader::make_index_block_hash(&stacks_tip_consensus_hash, &stacks_tip);

    // get the associated anchored block
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/blocks/{stacks_id_tip}");
    let block_bytes = client.get(&path).send().unwrap().bytes().unwrap();
    let block = StacksBlock::consensus_deserialize(&mut block_bytes.as_ref()).unwrap();

    (stacks_tip_consensus_hash, block)
}

#[derive(Deserialize, Debug)]
struct ReadOnlyResponse {
    #[serde(rename = "okay")]
    _okay: bool,
    #[serde(rename = "result")]
    result_hex: String,
}

impl ReadOnlyResponse {
    pub fn result(&self) -> Result<Value, SerializationError> {
        Value::try_deserialize_hex_untyped(&self.result_hex)
    }
}

pub fn call_read_only(
    conf: &Config,
    principal: &StacksAddress,
    contract: &str,
    function: &str,
    args: Vec<&Value>,
) -> Value {
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let client = reqwest::blocking::Client::new();

    info!("Call read only: {contract}.{function}({args:?})");

    let path = format!("{http_origin}/v2/contracts/call-read/{principal}/{contract}/{function}");

    let serialized_args = args
        .iter()
        .map(|arg| arg.serialize_to_hex().unwrap())
        .collect::<Vec<String>>();

    let body = json!({
        "arguments": serialized_args,
        "sender": principal.to_string(),
    });
    let response: ReadOnlyResponse = client
        .post(path)
        .header("Content-Type", "application/json")
        .body(body.to_string())
        .send()
        .unwrap()
        .json()
        .unwrap();
    response.result().unwrap()
}

fn find_microblock_privkey(
    conf: &Config,
    pubkey_hash: &Hash160,
    max_tries: u64,
) -> Option<StacksPrivateKey> {
    let mut keychain = Keychain::default(conf.node.seed.clone());
    for ix in 0..max_tries {
        // the first rotation occurs at 203.
        let privk = keychain.make_microblock_secret_key(203 + ix, &(203 + ix).to_be_bytes());
        let pubkh = Hash160::from_node_public_key(&StacksPublicKey::from_private(&privk));
        if pubkh == *pubkey_hash {
            return Some(privk);
        }
    }
    None
}

/// Returns true iff `b` is within `0.1%` of `a`.
fn is_close_f64(a: f64, b: f64) -> bool {
    let error = (a - b).abs() / a.abs();
    error < 0.001
}

#[test]
#[ignore]
fn bitcoind_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, miner_account) = neon_integration_test_conf();
    let prom_port = gen_random_port();
    let localhost = "127.0.0.1";
    let prom_bind = format!("{localhost}:{prom_port}");
    conf.node.prometheus_bind = Some(prom_bind.clone());

    conf.burnchain.max_rbf = 1000000;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:

    eprintln!("Miner account: {miner_account}");

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(4_000);

    let burn_blocks_observed = test_observer::get_burn_blocks();
    let burn_blocks_with_burns: Vec<_> = burn_blocks_observed
        .into_iter()
        .filter(|block| block.get("burn_amount").unwrap().as_u64().unwrap() > 0)
        .collect();
    assert!(
        !burn_blocks_with_burns.is_empty(),
        "Burn block sortitions {} should be >= 1",
        burn_blocks_with_burns.len()
    );

    // query for prometheus metrics
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{prom_bind}");
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        assert!(res.contains("stacks_node_computed_miner_commitment_high 0"));
        assert!(res.contains("stacks_node_computed_miner_commitment_low 20000"));
        assert!(res.contains("stacks_node_computed_relative_miner_score 100"));
        assert!(res.contains("stacks_node_miner_current_median_commitment_high 0"));
        assert!(res.contains("stacks_node_miner_current_median_commitment_low 20000"));
        assert!(res.contains("stacks_node_active_miners_total 1"));

        assert!(res.contains("stacks_node_last_block_read_count 0"));
        assert!(res.contains("stacks_node_last_block_read_length 0"));
        assert!(res.contains("stacks_node_last_block_write_count 0"));
        assert!(res.contains("stacks_node_last_block_write_length 0"));
        assert!(res.contains("stacks_node_last_block_runtime 0"));
        assert!(res.contains("stacks_node_last_block_transaction_count 1"));

        assert!(res.contains("stacks_node_last_mined_block_read_count 0"));
        assert!(res.contains("stacks_node_last_mined_block_read_length 0"));
        assert!(res.contains("stacks_node_last_mined_block_write_count 0"));
        assert!(res.contains("stacks_node_last_mined_block_write_length 0"));
        assert!(res.contains("stacks_node_last_mined_block_runtime 0"));
        assert!(res.contains("stacks_node_last_mined_block_transaction_count 1"));
    }
    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
/// Test that the RBF/ongoing_ops mechanism can detect that a submitted
/// tx has been confirmed even if the burnchaindb doesn't parse it.
/// This test forces the neon_node to submit a block commit with bad
///  magic bytes, and then checks if mining can continue afterwards.
fn confirm_unparsed_ongoing_ops() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, miner_account) = neon_integration_test_conf();
    conf.node.wait_time_for_blocks = 1000;
    conf.burnchain.pox_reward_length = Some(500);
    conf.burnchain.max_rbf = 1000000;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // this block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second bitcoin block will contain the first mined Stacks block, and then issue a 2nd valid commit
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // now, let's alter the miner's magic bytes
    bitcoin_regtest_controller::TEST_MAGIC_BYTES
        .lock()
        .unwrap()
        .replace([b'Z', b'Z']);

    // let's trigger another mining loop: this should create an invalid block commit.
    // this bitcoin block will contain the valid commit created before (so, a second stacks block)
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // reset the miner's magic bytes
    bitcoin_regtest_controller::TEST_MAGIC_BYTES
        .lock()
        .unwrap()
        .take()
        .unwrap();

    // trigger another mining loop: this will mine the invalid block commit into a bitcoin block
    //  if the block wasn't created in 25 seconds, just timeout -- the test will fail
    //  at the final checks
    // in correct behavior, this will create a 3rd valid block commit
    next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 25);

    // trigger another mining loop: this will mine the last valid block commit. after this,
    //  the node *should* see 3 stacks blocks.
    next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 25);

    // query the miner's account nonce

    eprintln!("Miner account: {miner_account}");

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(
        account.nonce, 3,
        "Miner should have mined 3 coinbases -- one should be invalid"
    );

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn most_recent_utxo_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, _) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut miner_signer = Keychain::default(conf.node.seed).generate_op_signer();
    let pubkey = miner_signer.get_public_key();
    let utxos_before = btc_regtest_controller.get_all_utxos(&pubkey);

    let mut last_utxo: Option<UTXO> = None;
    let mut smallest_utxo: Option<UTXO> = None; // smallest non-dust UTXO
    let mut biggest_utxo: Option<UTXO> = None;
    for utxo in utxos_before.iter() {
        if let Some(last) = last_utxo {
            if utxo.confirmations < last.confirmations {
                last_utxo = Some(utxo.clone());
            } else {
                last_utxo = Some(last);
            }
        } else {
            last_utxo = Some(utxo.clone());
        }

        if let Some(smallest) = smallest_utxo {
            if utxo.amount > 5500 && utxo.amount < smallest.amount {
                smallest_utxo = Some(utxo.clone());
            } else {
                smallest_utxo = Some(smallest);
            }
        } else {
            smallest_utxo = Some(utxo.clone());
        }

        if let Some(biggest) = biggest_utxo {
            if utxo.amount > biggest.amount {
                biggest_utxo = Some(utxo.clone());
            } else {
                biggest_utxo = Some(biggest);
            }
        } else {
            biggest_utxo = Some(utxo.clone());
        }
    }

    let last_utxo = last_utxo.unwrap();
    let smallest_utxo = smallest_utxo.unwrap();
    let mut biggest_utxo = biggest_utxo.unwrap();

    eprintln!("Last-spent UTXO is {last_utxo:?}");
    eprintln!("Smallest UTXO is {smallest_utxo:?}");
    eprintln!("Biggest UTXO is {biggest_utxo:?}");

    assert_eq!(last_utxo, smallest_utxo);
    assert_ne!(biggest_utxo, last_utxo);
    assert_ne!(biggest_utxo, smallest_utxo);

    // third block will be the second mined Stacks block, and mining it should *not* spend the
    // biggest UTXO, but should spend the *smallest non-dust* UTXO
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let utxos_after = btc_regtest_controller.get_all_utxos(&pubkey);

    // last UTXO was spent, which would also have been the smallest.
    let mut has_biggest = false;
    for utxo in utxos_after.into_iter() {
        assert_ne!(utxo, last_utxo);
        assert_ne!(utxo, smallest_utxo);

        // don't care about confirmations here
        biggest_utxo.confirmations = utxo.confirmations;
        if utxo == biggest_utxo {
            has_biggest = true;
        }
    }

    // biggest UTXO is *not* spent
    assert!(has_biggest);

    channel.stop_chains_coordinator();
}

pub fn get_balance<F: std::fmt::Display>(http_origin: &str, account: &F) -> u128 {
    get_account(http_origin, account).balance
}

#[derive(Debug)]
pub struct Account {
    pub balance: u128,
    pub locked: u128,
    pub nonce: u64,
}

pub fn get_account_result<F: std::fmt::Display>(
    http_origin: &str,
    account: &F,
) -> Result<Account, reqwest::Error> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/accounts/{account}?proof=0");
    let res = client.get(&path).send()?.json::<AccountEntryResponse>()?;
    debug!("Account response: {res:#?}");
    Ok(Account {
        balance: u128::from_str_radix(&res.balance[2..], 16).unwrap(),
        locked: u128::from_str_radix(&res.locked[2..], 16).unwrap(),
        nonce: res.nonce,
    })
}

pub fn get_account<F: std::fmt::Display>(http_origin: &str, account: &F) -> Account {
    get_account_result(http_origin, account).unwrap()
}

pub fn get_sortition_info(conf: &Config) -> SortitionInfo {
    let client = reqwest::blocking::Client::new();
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let path = format!("{http_origin}/v3/sortitions");
    let mut resp: Vec<_> = client.get(&path).send().unwrap().json().unwrap();
    resp.pop().unwrap()
}

pub fn get_sortition_info_ch(conf: &Config, ch: &ConsensusHash) -> SortitionInfo {
    let client = reqwest::blocking::Client::new();
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let path = format!("{http_origin}/v3/sortitions/consensus/{ch}");
    let mut resp: Vec<_> = client.get(&path).send().unwrap().json().unwrap();
    resp.pop().unwrap()
}

pub fn get_neighbors(conf: &Config) -> Option<serde_json::Value> {
    let client = reqwest::blocking::Client::new();
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let path = format!("{http_origin}/v2/neighbors");
    client.get(&path).send().ok()?.json().ok()
}

pub fn get_pox_info(http_origin: &str) -> Option<RPCPoxInfoData> {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/pox");
    client.get(&path).send().ok()?.json::<RPCPoxInfoData>().ok()
}

fn get_chain_tip(http_origin: &str) -> (ConsensusHash, BlockHeaderHash) {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/info");
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<serde_json::Value>()
        .unwrap();
    (
        ConsensusHash::from_hex(
            res.get("stacks_tip_consensus_hash")
                .unwrap()
                .as_str()
                .unwrap(),
        )
        .unwrap(),
        BlockHeaderHash::from_hex(res.get("stacks_tip").unwrap().as_str().unwrap()).unwrap(),
    )
}

fn get_chain_tip_height(http_origin: &str) -> u64 {
    let client = reqwest::blocking::Client::new();
    let path = format!("{http_origin}/v2/info");
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();

    res.stacks_tip_height
}

pub fn get_contract_src(
    http_origin: &str,
    contract_addr: StacksAddress,
    contract_name: String,
    use_latest_tip: bool,
) -> Result<String, String> {
    let client = reqwest::blocking::Client::new();
    let query_string = if use_latest_tip {
        "?tip=latest".to_string()
    } else {
        "".to_string()
    };
    let path =
        format!("{http_origin}/v2/contracts/source/{contract_addr}/{contract_name}{query_string}");
    let res = client.get(&path).send().unwrap();

    if res.status().is_success() {
        let contract_src_res = res.json::<ContractSrcResponse>().unwrap();
        Ok(contract_src_res.source)
    } else {
        let err_str = res.text().unwrap();
        Err(err_str)
    }
}

#[test]
#[ignore]
fn deep_contract() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let stack_limit = (AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1) as usize;
    let exceeds_stack_depth_list = format!(
        "{}u1 {}",
        "(list ".repeat(stack_limit + 1),
        ")".repeat(stack_limit + 1)
    );

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ,
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();

    let publish = make_contract_publish(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        "test-publish",
        &exceeds_stack_depth_list,
    );
    submit_tx(&http_origin, &publish);

    test_observer::clear();

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    let mut included_smart_contract = false;
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = parsed.payload {
                included_smart_contract = true;
            }
        }
    }

    assert!(
        !included_smart_contract,
        "No smart contract publish transaction should be included"
    );

    test_observer::clear();
}

#[test]
#[ignore]
fn bad_microblock_pubkey() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // fault injection
    env::set_var(
        "STACKS_MICROBLOCK_PUBKEY_HASH",
        "0000000000000000000000000000000000000000",
    );
    for _i in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }
    env::set_var("STACKS_MICROBLOCK_PUBKEY_HASH", "");

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert!(blocks.len() >= 5);
    assert!(blocks.len() <= 6);

    channel.stop_chains_coordinator();
    test_observer::clear();
}

#[test]
#[ignore]
fn liquid_ustx_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // the contract that we'll test the costs of
    let caller_src = "
    (define-public (execute)
       (ok stx-liquid-supply))
    ";

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ,
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();

    let publish = make_contract_publish(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        "caller",
        caller_src,
    );

    let replaced_txid = submit_tx(&http_origin, &publish);

    let publish = make_contract_publish(
        &spender_sk,
        0,
        1100,
        conf.burnchain.chain_id,
        "caller",
        caller_src,
    );
    submit_tx(&http_origin, &publish);

    let dropped_txs = test_observer::get_memtx_drops();
    assert_eq!(dropped_txs.len(), 1);
    assert_eq!(&dropped_txs[0].1, "ReplaceByFee");
    assert_eq!(&dropped_txs[0].0, &format!("0x{replaced_txid}"));

    // mine 1 burn block for the miner to issue the next block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // mine next burn block for the miner to win
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let call_tx = make_contract_call(
        &spender_sk,
        1,
        1000,
        conf.burnchain.chain_id,
        &spender_addr,
        "caller",
        "execute",
        &[],
    );

    submit_tx(&http_origin, &call_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                let liquid_ustx = parsed.expect_result_ok().unwrap().expect_u128().unwrap();
                assert!(liquid_ustx > 0, "Should be more liquid ustx than 0");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");
}

#[test]
#[ignore]
fn lockup_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query an account that unlocked STX
    // Looking at chainstate-test.txt,
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,1
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,3
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,3
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s -> SN3Z4MMRJ29FVZB38FGYPE94N1D8ZGF55R7YWH00A
    let recipient_addr_str = "SN3Z4MMRJ29FVZB38FGYPE94N1D8ZGF55R7YWH00A";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // block #1 should be unlocking STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &recipient), 13888888889);
    let blocks = test_observer::get_blocks();
    let chain_tip = blocks.last().unwrap();

    let events = chain_tip.get("events").unwrap().as_array().unwrap();
    let mut found = false;
    for event in events.iter() {
        if event.get("type").unwrap().as_str().unwrap() == "stx_mint_event" {
            let payload = event.get("stx_mint_event").unwrap().as_object().unwrap();
            let address = payload.get("recipient").unwrap().as_str().unwrap();
            let amount = payload.get("amount").unwrap().as_str().unwrap();
            if address == recipient_addr_str && amount == "13888888889" {
                found = true;
            }
        }
    }
    assert!(found);

    // block #2 won't unlock STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // block #3 should be unlocking STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &recipient), 13888888889 * 3);

    // now let's ensure that the last block received by the event observer contains the lockup receipt
    let blocks = test_observer::get_blocks();
    let chain_tip = blocks.last().unwrap();

    let events = chain_tip.get("events").unwrap().as_array().unwrap();
    assert_eq!(events.len(), 2);
    for event in events {
        assert_eq!(
            event.get("type").unwrap().as_str().unwrap(),
            "stx_mint_event"
        );
    }

    test_observer::clear();
}

#[test]
#[ignore]
fn stx_transfer_btc_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stx_addr: StacksAddress = to_addr(&spender_sk);
    let spender_addr: PrincipalData = spender_stx_addr.into();
    let _spender_btc_addr = BitcoinAddress::from_bytes_legacy(
        BitcoinNetworkType::Regtest,
        LegacyBitcoinAddressType::PublicKeyHash,
        &spender_stx_addr.bytes().0,
    )
    .unwrap();

    let spender_2_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_2_stx_addr: StacksAddress = to_addr(&spender_2_sk);
    let spender_2_addr: PrincipalData = spender_2_stx_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_2_addr.clone(),
        amount: 100300,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    test_observer::clear();

    // let's query the spender's account:
    assert_eq!(get_balance(&http_origin, &spender_addr), 100300);

    // okay, let's send a pre-stx op.
    let pre_stx_op = PreStxOp {
        output: spender_stx_addr,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch2_05,
                BlockstackOperationType::PreStx(pre_stx_op),
                &mut miner_signer,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // let's fire off our transfer op.
    let recipient_sk = StacksPrivateKey::random();
    let recipient_addr = to_addr(&recipient_sk);
    let transfer_stx_op = TransferStxOp {
        sender: spender_stx_addr,
        recipient: recipient_addr,
        transfered_ustx: 100_000,
        memo: vec![],
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut spender_signer = BurnchainOpSigner::new(spender_sk, false);

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch2_05,
                BlockstackOperationType::TransferStx(transfer_stx_op),
                &mut spender_signer,
                1
            )
            .is_ok(),
        "Transfer operation should submit successfully"
    );
    // should be elected in the same block as the transfer, so balances should be unchanged.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &spender_addr), 100300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 0);

    // this block should process the transfer
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 100_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 100_300);

    // now let's do a pre-stx-op and a transfer op in the same burnchain block...
    // NOTE: bitcoind really doesn't want to return the utxo from the first op for some reason,
    //    so we have to get a little creative...

    // okay, let's send a pre-stx op.
    let pre_stx_op = PreStxOp {
        output: spender_2_stx_addr,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();

    let pre_stx_tx = btc_regtest_controller
        .submit_manual(
            StacksEpochId::Epoch2_05,
            BlockstackOperationType::PreStx(pre_stx_op),
            &mut miner_signer,
            None,
        )
        .expect("Pre-stx operation should submit successfully");

    let transfer_stx_utxo = UTXO {
        txid: pre_stx_tx.txid(),
        vout: 1,
        script_pub_key: pre_stx_tx.output[1].script_pubkey.clone(),
        amount: pre_stx_tx.output[1].value,
        confirmations: 0,
    };

    // let's fire off our transfer op.
    let transfer_stx_op = TransferStxOp {
        sender: spender_2_stx_addr,
        recipient: recipient_addr,
        transfered_ustx: 100_000,
        memo: vec![],
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut spender_signer = BurnchainOpSigner::new(spender_2_sk, false);

    btc_regtest_controller
        .submit_manual(
            StacksEpochId::Epoch2_05,
            BlockstackOperationType::TransferStx(transfer_stx_op),
            &mut spender_signer,
            Some(transfer_stx_utxo),
        )
        .expect("Transfer operation should submit successfully");

    // should be elected in the same block as the transfer, so balances should be unchanged.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 100_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 100_300);

    // should process the transfer
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 200_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 300);

    let mut found_btc_tx = false;
    let blocks = test_observer::get_blocks();
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                let burnchain_op = tx.get("burnchain_op").unwrap().as_object().unwrap();
                if !burnchain_op.contains_key("transfer_stx") {
                    panic!("unexpected btc transaction type");
                }
                found_btc_tx = true;
            }
        }
    }
    assert!(found_btc_tx);

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn stx_delegate_btc_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stx_addr: StacksAddress = to_addr(&spender_sk);
    let spender_addr: PrincipalData = spender_stx_addr.into();

    let recipient_sk = StacksPrivateKey::random();
    let recipient_addr = to_addr(&recipient_sk);
    let pox_pubkey = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey).to_bytes());

    let (mut conf, _miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });
    conf.initial_balances.push(InitialBalance {
        address: recipient_addr.into(),
        amount: 300,
    });

    // update epoch info so that Epoch 2.1 takes effect
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(3);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    // reward cycle length = 5, so 3 reward cycle slots + 2 prepare-phase burns
    let reward_cycle_len = 5;
    let prepare_phase_len = 2;
    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        2,
        5,
        15,
        (16 * reward_cycle_len - 1).into(),
        (17 * reward_cycle_len).into(),
        u32::MAX,
        u32::MAX,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants;

    let mut btc_regtest_controller =
        BitcoinRegtestController::with_burnchain(conf.clone(), None, Some(burnchain_config), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    test_observer::clear();

    // Mine a few more blocks so that Epoch 2.1 (and thus pox-2) can take effect.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // okay, let's send a pre-stx op.
    let pre_stx_op = PreStxOp {
        output: spender_stx_addr,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch21,
                BlockstackOperationType::PreStx(pre_stx_op),
                &mut miner_signer,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's fire off our delegate op.
    let del_stx_op = DelegateStxOp {
        sender: spender_stx_addr,
        delegate_to: recipient_addr,
        reward_addr: None,
        delegated_ustx: 100_000,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
        until_burn_height: None,
    };

    let mut spender_signer = BurnchainOpSigner::new(spender_sk, false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch21,
                BlockstackOperationType::DelegateStx(del_stx_op),
                &mut spender_signer,
                1
            )
            .is_ok(),
        "Delegate operation should submit successfully"
    );

    // the second block should process the delegation, after which the balaces should be unchanged
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 100300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 300);

    // send a delegate-stack-stx transaction
    let sort_height = channel.get_sortitions_processed();
    let tx = make_contract_call(
        &recipient_sk,
        0,
        293,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "delegate-stack-stx",
        &[
            Value::Principal(spender_addr),
            Value::UInt(100_000),
            execute(
                &format!("{{ hashbytes: 0x{pox_pubkey_hash}, version: 0x00 }}"),
                ClarityVersion::Clarity2,
            )
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    // push the stacking transaction
    submit_tx(&http_origin, &tx);

    // let's mine until the next reward cycle starts ...
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // check the locked amount for the spender account
    let account = get_account(&http_origin, &spender_stx_addr);
    assert_eq!(account.locked, 100_000);

    let mut delegate_stack_stx_found = false;
    let mut delegate_stx_found = false;
    let blocks = test_observer::get_blocks();
    for block in blocks.iter() {
        let events = block.get("events").unwrap().as_array().unwrap();
        for event in events.iter() {
            let event_type = event.get("type").unwrap().as_str().unwrap();
            if event_type == "contract_event" {
                let contract_event = event.get("contract_event").unwrap().as_object().unwrap();

                // Check that it is a print event
                let sub_type = contract_event.get("topic").unwrap().as_str().unwrap();
                assert_eq!(sub_type, "print");

                // Ensure that the function name is as expected
                // This verifies that there were print events for delegate-stack-stx and delegate-stx
                let name_field =
                    &contract_event["value"]["Response"]["data"]["Tuple"]["data_map"]["name"];
                let name_data = name_field["Sequence"]["String"]["ASCII"]["data"]
                    .as_array()
                    .unwrap();
                let ascii_vec = name_data
                    .iter()
                    .map(|num| num.as_u64().unwrap() as u8)
                    .collect();
                let name = String::from_utf8(ascii_vec).unwrap();
                if name == "delegate-stack-stx" {
                    delegate_stack_stx_found = true;
                } else if name == "delegate-stx" {
                    delegate_stx_found = true;
                }
            }
        }
    }
    assert!(delegate_stx_found);
    assert!(delegate_stack_stx_found);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn stack_stx_burn_op_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stx_addr_1: StacksAddress = to_addr(&spender_sk_1);
    let spender_addr_1: PrincipalData = spender_stx_addr_1.into();

    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_stx_addr_2: StacksAddress = to_addr(&spender_sk_2);

    let recipient_sk = StacksPrivateKey::random();
    let recipient_addr = to_addr(&recipient_sk);

    let (mut conf, _miner_account) = neon_integration_test_conf();

    let first_bal = 6_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);
    let second_bal = 2_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: first_bal,
    });
    conf.initial_balances.push(InitialBalance {
        address: recipient_addr.into(),
        amount: second_bal,
    });

    // update epoch info so that Epoch 2.1 takes effect
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2,
            end_height: 3,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch22,
            start_height: 3,
            end_height: 4,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_2,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch23,
            start_height: 4,
            end_height: 5,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_3,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch24,
            start_height: 5,
            end_height: 6,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_4,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch25,
            start_height: 6,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_5,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(3);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    // reward cycle length = 5, so 3 reward cycle slots + 2 prepare-phase burns
    let reward_cycle_len = 5;
    let prepare_phase_len = 2;
    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        2,
        5,
        15,
        (16 * reward_cycle_len - 1).into(),
        (17 * reward_cycle_len).into(),
        u32::MAX,
        u32::MAX,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants;

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    test_observer::clear();

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Bootstrapped to 2.5, submitting stack-stx and pre-stx op...");

    let signer_sk_1 = spender_sk_1;
    let signer_sk_2 = spender_sk_2;
    let signer_pk_1 = StacksPublicKey::from_private(&signer_sk_1);

    let pox_addr = PoxAddress::Standard(spender_stx_addr_1, Some(AddressHashMode::SerializeP2PKH));

    let mut block_height = channel.get_sortitions_processed();

    let signer_pk_bytes = signer_pk_1.to_bytes_compressed();

    // Submitting 2 pre-stx operations
    let mut miner_signer_1 = Keychain::default(conf.node.seed.clone()).generate_op_signer();
    let pre_stx_op_1 = PreStxOp {
        output: spender_stx_addr_1,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                BlockstackOperationType::PreStx(pre_stx_op_1),
                &mut miner_signer_1,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    let mut miner_signer_2 = Keychain::default(conf.node.seed.clone()).generate_op_signer();
    let pre_stx_op_2 = PreStxOp {
        output: spender_stx_addr_2,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                BlockstackOperationType::PreStx(pre_stx_op_2),
                &mut miner_signer_2,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );
    info!("Submitted 2 pre-stx ops at block {block_height}, mining a few blocks...");

    let reward_cycle = burnchain_config
        .block_height_to_reward_cycle(block_height)
        .unwrap()
        + 1;

    let lock_period = 6;
    let topic = Pox4SignatureTopic::StackStx;
    let auth_id: u32 = 1;

    info!(
        "Submitting set-signer-key-authorization";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
    );

    let set_signer_key_auth_tx = make_contract_call(
        &signer_sk_1,
        0,
        500,
        conf.burnchain.chain_id,
        &boot_code_addr(false),
        POX_4_NAME,
        "set-signer-key-authorization",
        &[
            Value::Tuple(pox_addr.as_clarity_tuple().unwrap()),
            Value::UInt(lock_period),
            Value::UInt(reward_cycle.into()),
            Value::string_ascii_from_bytes(topic.get_name_str().into()).unwrap(),
            Value::buff_from(signer_pk_bytes.clone()).unwrap(),
            Value::Bool(true),
            Value::UInt(u128::MAX),
            Value::UInt(auth_id.into()),
        ],
    );

    // push the stacking transaction
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    submit_tx(&http_origin, &set_signer_key_auth_tx);

    // Wait a few blocks to be registered
    for _i in 0..3 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        block_height = channel.get_sortitions_processed();
    }

    let reward_cycle = burnchain_config
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    let signer_key: StacksPublicKeyBuffer = signer_pk_bytes.as_slice().into();

    info!(
        "Submitting stack stx op";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
    );

    // `stacked_ustx` should be large enough to avoid ERR_STACKING_THRESHOLD_NOT_MET from Clarity
    let stack_stx_op_with_some_signer_key = BlockstackOperationType::StackStx(StackStxOp {
        sender: spender_stx_addr_1,
        reward_addr: pox_addr.clone(),
        stacked_ustx: 10000000000000,
        num_cycles: 6,
        signer_key: Some(signer_key),
        max_amount: Some(u128::MAX),
        auth_id: Some(auth_id),
        // to be filled in
        vtxindex: 0,
        txid: Txid([0u8; 32]),
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash::zero(),
    });

    let mut spender_signer_1 = BurnchainOpSigner::new(signer_sk_1, false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                stack_stx_op_with_some_signer_key,
                &mut spender_signer_1,
                1
            )
            .is_ok(),
        "Stack STX operation with some signer key should submit successfully"
    );

    let stack_stx_op_with_no_signer_key = BlockstackOperationType::StackStx(StackStxOp {
        sender: spender_stx_addr_2,
        reward_addr: pox_addr,
        stacked_ustx: 10000000000000,
        num_cycles: 6,
        signer_key: None,
        max_amount: None,
        auth_id: None,
        // to be filled in
        vtxindex: 0,
        txid: Txid([0u8; 32]),
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash::zero(),
    });

    let mut spender_signer_2 = BurnchainOpSigner::new(signer_sk_2, false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                stack_stx_op_with_no_signer_key,
                &mut spender_signer_2,
                1
            )
            .is_ok(),
        "Stack STX operation with no signer key should submit successfully"
    );

    info!("Submitted 2 stack STX ops at height {block_height}, mining a few blocks...");

    // the second block should process the vote, after which the balaces should be unchanged
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

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
                assert_eq!(signer_key_found, signer_key.to_hex());

                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
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

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn vote_for_aggregate_key_burn_op_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stx_addr: StacksAddress = to_addr(&spender_sk);
    let spender_addr: PrincipalData = spender_stx_addr.into();

    let pox_pubkey = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let _pox_pubkey_hash = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey).to_bytes());

    let (mut conf, _miner_account) = neon_integration_test_conf();

    let first_bal = 6_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);
    let stacked_bal = 1_000_000_000 * u128::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr,
        amount: first_bal,
    });

    // update epoch info so that Epoch 2.1 takes effect
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2,
            end_height: 3,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch22,
            start_height: 3,
            end_height: 4,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_2,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch23,
            start_height: 4,
            end_height: 5,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_3,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch24,
            start_height: 5,
            end_height: 6,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_4,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch25,
            start_height: 6,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_5,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(3);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    // reward cycle length = 5, so 3 reward cycle slots + 2 prepare-phase burns
    let reward_cycle_len = 5;
    let prepare_phase_len = 2;
    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        2,
        5,
        15,
        (16 * reward_cycle_len - 1).into(),
        (17 * reward_cycle_len).into(),
        u32::MAX,
        u32::MAX,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants;

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    test_observer::clear();

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Bootstrapped to 2.5, submitting stack-stx and pre-stx op...");

    // setup stack-stx tx

    let signer_sk = spender_sk;
    let signer_pk = StacksPublicKey::from_private(&signer_sk);

    let pox_addr = PoxAddress::Standard(spender_stx_addr, Some(AddressHashMode::SerializeP2PKH));

    let mut block_height = btc_regtest_controller.get_headers_height();

    let reward_cycle = burnchain_config
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    let signature = make_pox_4_signer_key_signature(
        &pox_addr,
        &signer_sk,
        reward_cycle.into(),
        &Pox4SignatureTopic::StackStx,
        CHAIN_ID_TESTNET,
        12,
        u128::MAX,
        1,
    )
    .unwrap();

    let signer_pk_bytes = signer_pk.to_bytes_compressed();

    let stacking_tx = make_contract_call(
        &spender_sk,
        0,
        500,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-4",
        "stack-stx",
        &[
            Value::UInt(stacked_bal),
            Value::Tuple(pox_addr.as_clarity_tuple().unwrap()),
            Value::UInt(block_height.into()),
            Value::UInt(12),
            Value::some(Value::buff_from(signature.to_rsv()).unwrap()).unwrap(),
            Value::buff_from(signer_pk_bytes.clone()).unwrap(),
            Value::UInt(u128::MAX),
            Value::UInt(1),
        ],
    );

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();
    let pre_stx_op = PreStxOp {
        output: spender_stx_addr,
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                BlockstackOperationType::PreStx(pre_stx_op),
                &mut miner_signer,
                1
            )
            .is_ok(),
        "Pre-stx operation should submit successfully"
    );

    // push the stacking transaction
    submit_tx(&http_origin, &stacking_tx);

    info!("Submitted stack-stx and pre-stx op at block {block_height}, mining a few blocks...");

    // Wait a few blocks to be registered
    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        block_height = btc_regtest_controller.get_headers_height();
    }

    let reward_cycle = burnchain_config
        .block_height_to_reward_cycle(block_height)
        .unwrap();

    let signer_key: StacksPublicKeyBuffer = signer_pk_bytes.as_slice().into();

    let aggregate_pk = Secp256k1PublicKey::new();
    let aggregate_key: StacksPublicKeyBuffer = aggregate_pk.to_bytes_compressed().as_slice().into();

    let signer_index = 0;

    info!(
        "Submitting vote for aggregate key op";
        "block_height" => block_height,
        "reward_cycle" => reward_cycle,
        "signer_index" => %signer_index,
    );

    let vote_for_aggregate_key_op =
        BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
            signer_key,
            signer_index,
            sender: spender_stx_addr,
            round: 0,
            reward_cycle,
            aggregate_key,
            // to be filled in
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        });

    let mut spender_signer = BurnchainOpSigner::new(signer_sk, false);
    assert!(
        btc_regtest_controller
            .submit_operation(
                StacksEpochId::Epoch25,
                vote_for_aggregate_key_op,
                &mut spender_signer,
                1
            )
            .is_ok(),
        "Vote for aggregate key operation should submit successfully"
    );

    info!("Submitted vote for aggregate key op at height {block_height}, mining a few blocks...");

    // the second block should process the vote, after which the vote should be processed
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut vote_for_aggregate_key_found = false;
    let blocks = test_observer::get_blocks();
    for block in blocks.iter() {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                debug!("Found a burn op: {:?}", tx);
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
                let signer_key = vote_obj.get("signer_key").unwrap().as_str().unwrap();
                assert_eq!(to_hex(&signer_pk_bytes), signer_key);

                vote_for_aggregate_key_found = true;
            }
        }
    }
    assert!(
        vote_for_aggregate_key_found,
        "Expected vote for aggregate key op"
    );

    // Check that the correct key was set
    let saved_key = get_key_for_cycle(reward_cycle, false, &conf.node.rpc_bind)
        .expect("Expected to be able to check key is set after voting")
        .expect("Expected aggregate key to be set");

    assert_eq!(saved_key, aggregate_key.as_bytes().to_vec());

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn bitcoind_resubmission_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr,
        amount: 100300,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // next block, issue a commit
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's figure out the current chain tip
    let chain_tip = get_chain_tip(&http_origin);

    // HACK: this test relies on manually inserting a bad microblock into the chain state.
    //  this behavior is not guaranteed to continue to work like this, so at some point this
    //  test will need to be updated to handle that.
    {
        let (mut chainstate, _) = StacksChainState::open(
            false,
            conf.burnchain.chain_id,
            &conf.get_chainstate_path_str(),
            None,
        )
        .unwrap();
        let mut tx = chainstate.db_tx_begin().unwrap();

        let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);

        let ublock_privk =
            find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024)
                .unwrap();

        let garbage_tx = make_stacks_transfer_mblock_only(
            &spender_sk,
            0,
            100,
            conf.burnchain.chain_id,
            &PrincipalData::from(StacksAddress::burn_address(false)),
            1000,
        );
        let mut garbage_block = StacksMicroblock::first_unsigned(
            &chain_tip.1,
            vec![StacksTransaction::consensus_deserialize(&mut garbage_tx.as_slice()).unwrap()],
        );
        garbage_block.header.prev_block = BlockHeaderHash([3; 32]);
        garbage_block.header.sequence = 1;
        garbage_block.sign(&ublock_privk).unwrap();

        eprintln!("Minting microblock at {}/{}", &chain_tip.0, &chain_tip.1);
        StacksChainState::store_staging_microblock(
            &mut tx,
            &consensus_hash,
            &stacks_block.header.block_hash(),
            &garbage_block,
        )
        .unwrap();
        tx.commit().unwrap();
    }

    thread::sleep(Duration::from_secs(30));

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let burnchain_db = BurnchainDB::open(
        &btc_regtest_controller
            .get_burnchain()
            .get_burnchaindb_path(),
        false,
    )
    .unwrap();

    let burn_tip = burnchain_db.get_canonical_chain_tip().unwrap();
    let last_burn_block =
        BurnchainDB::get_burnchain_block(burnchain_db.conn(), &burn_tip.block_hash).unwrap();

    assert_eq!(
        last_burn_block.ops.len(),
        1,
        "Should only have ONE operation in the last burn block"
    );

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn bitcoind_forking_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, miner_account) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {sort_height}");

    while sort_height < 210 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }
    // let's query the miner's account nonce:

    eprintln!("Miner account: {miner_account}");

    let account = get_account(&http_origin, &miner_account);

    // N.B. rewards mature after 2 confirmations...
    assert_eq!(account.balance, 4 * (1_000_000_000 + 20_400_000));
    assert_eq!(account.nonce, 7);

    // okay, let's figure out the burn block we want to fork away.
    let burn_header_hash_to_fork = btc_regtest_controller.get_block_hash(206);
    btc_regtest_controller.invalidate_block(&burn_header_hash_to_fork);
    btc_regtest_controller.build_next_block(5);

    thread::sleep(Duration::from_secs(50));
    eprintln!("Wait for block off of shallow fork");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);

    // N.B. rewards mature after 2 confirmations...
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 2);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);

    // N.B. rewards mature after 2 confirmations...
    assert_eq!(account.balance, 0);
    // but we're able to keep on mining
    assert_eq!(account.nonce, 3);

    // Let's create another fork, deeper
    let burn_header_hash_to_fork = btc_regtest_controller.get_block_hash(206);
    eprintln!("Instigate 10-block deep fork");
    btc_regtest_controller.invalidate_block(&burn_header_hash_to_fork);
    btc_regtest_controller.build_next_block(10);

    thread::sleep(Duration::from_secs(50));
    eprintln!("Wait for block off of deep fork");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 3);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);

    // but we're able to keep on mining
    assert!(account.nonce >= 3);

    eprintln!("End of test");
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn should_fix_2771() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, _miner_account) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {sort_height}");

    while sort_height < 210 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    // okay, let's figure out the burn block we want to fork away.
    let reorg_height = 208;
    warn!("Will trigger re-org at block {reorg_height}");
    let burn_header_hash_to_fork = btc_regtest_controller.get_block_hash(reorg_height);
    btc_regtest_controller.invalidate_block(&burn_header_hash_to_fork);
    btc_regtest_controller.build_next_block(1);
    thread::sleep(Duration::from_secs(5));

    // The test here consists in producing a canonical chain with 210 blocks.
    // Once done, we invalidate the block 208, and instead of rebuilding directly
    // a longer fork with N blocks (as done in the bitcoind_forking_test)
    // we slowly add some more blocks.
    // Without the patch, this behavior ends up crashing the node with errors like:
    // WARN [1626791307.078061] [src/chainstate/coordinator/mod.rs:535] [chains-coordinator] ChainsCoordinator: could not retrieve  block burnhash=40bdbf0dda349642bdf4dd30dd31af4f0c9979ce12a7c17485245d0a6ddd970b
    // WARN [1626791307.078098] [src/chainstate/coordinator/mod.rs:308] [chains-coordinator] Error processing new burn block: NonContiguousBurnchainBlock(UnknownBlock(40bdbf0dda349642bdf4dd30dd31af4f0c9979ce12a7c17485245d0a6ddd970b))
    // And the burnchain db ends up in the same state we ended up while investigating 2771.
    // With this patch, the node is able to entirely register this new canonical fork, and then able to make progress and finish successfully.
    for _i in 0..3 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(30));
    }

    channel.stop_chains_coordinator();
}

/// Returns a StacksMicroblock with the given transactions, sequence, and parent block that is
/// signed with the given private key.
fn make_signed_microblock(
    block_privk: &StacksPrivateKey,
    txs: Vec<StacksTransaction>,
    parent_block: BlockHeaderHash,
    seq: u16,
) -> StacksMicroblock {
    let mut rng = rand::thread_rng();

    let txid_vecs: Vec<_> = txs.iter().map(|tx| tx.txid().as_bytes().to_vec()).collect();
    let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
    let tx_merkle_root = merkle_tree.root();

    let mut mblock = StacksMicroblock {
        header: StacksMicroblockHeader {
            version: rng.gen(),
            sequence: seq,
            prev_block: parent_block,
            tx_merkle_root,
            signature: MessageSignature([0u8; 65]),
        },
        txs,
    };
    mblock.sign(block_privk).unwrap();
    mblock
}

#[test]
#[ignore]
fn microblock_fork_poison_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();
    let second_spender_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let second_spender_addr: PrincipalData = to_addr(&second_spender_sk).into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });
    conf.initial_balances.push(InitialBalance {
        address: second_spender_addr.clone(),
        amount: 10000,
    });

    // we'll manually post a forked stream to the node
    conf.node.mine_microblocks = false;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 1_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.node.wait_time_for_blocks = 1_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();
    let miner_status = run_loop.get_miner_status();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(10_000);

    // turn off the miner for now, so we can ensure both of these get accepted and preprocessed
    // before we try and mine an anchor block that confirms them
    eprintln!("Disable miner");
    signal_mining_blocked(miner_status.clone());
    sleep_ms(10_000);

    // our first spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    // our second spender
    let account = get_account(&http_origin, &second_spender_addr);
    assert_eq!(account.balance, 10000);
    assert_eq!(account.nonce, 0);

    info!("Test microblock");

    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1000,
    );
    let unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &unconfirmed_tx_bytes[..]).unwrap();
    let second_unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
        &second_spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1500,
    );
    let second_unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &second_unconfirmed_tx_bytes[..]).unwrap();

    // TODO (hack) instantiate the sortdb in the burnchain
    let _ = btc_regtest_controller.sortdb_mut();

    // put each into a microblock
    let (first_microblock, second_microblock) = {
        let tip_info = get_chain_info(&conf);
        let stacks_tip = tip_info.stacks_tip;

        let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);
        let tip_hash =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &stacks_block.block_hash());
        let privk =
            find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024)
                .unwrap();
        let (mut chainstate, _) = StacksChainState::open(
            false,
            CHAIN_ID_TESTNET,
            &conf.get_chainstate_path_str(),
            None,
        )
        .unwrap();

        chainstate
            .reload_unconfirmed_state(
                &btc_regtest_controller
                    .sortdb_ref()
                    .index_handle_at_block(&chainstate, &tip_hash)
                    .unwrap(),
                tip_hash,
            )
            .unwrap();
        let iconn = btc_regtest_controller
            .sortdb_ref()
            .index_handle_at_block(&chainstate, &tip_hash)
            .unwrap();
        let first_microblock = make_microblock(
            &privk,
            &mut chainstate,
            &iconn,
            consensus_hash,
            stacks_block,
            vec![unconfirmed_tx],
        );

        eprintln!(
            "Created first microblock: {}: {first_microblock:?}",
            &first_microblock.block_hash()
        );

        // NOTE: this microblock conflicts because it has the same parent as the first microblock,
        // even though it's seq is different.
        let second_microblock =
            make_signed_microblock(&privk, vec![second_unconfirmed_tx], stacks_tip, 1);

        eprintln!(
            "Created second conflicting microblock: {}: {second_microblock:?}",
            &second_microblock.block_hash()
        );
        (first_microblock, second_microblock)
    };

    let mut microblock_bytes = vec![];
    first_microblock
        .consensus_serialize(&mut microblock_bytes)
        .unwrap();

    // post the first microblock
    let path = format!("{http_origin}/v2/microblocks");
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &first_microblock.block_hash()));

    let mut second_microblock_bytes = vec![];
    second_microblock
        .consensus_serialize(&mut second_microblock_bytes)
        .unwrap();

    // post the second microblock
    let path = format!("{http_origin}/v2/microblocks");
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(second_microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &second_microblock.block_hash()));

    eprintln!("Wait 10s and re-enable miner");
    sleep_ms(10_000);

    // resume mining
    eprintln!("Enable miner");
    signal_mining_ready(miner_status);
    sleep_ms(10_000);

    eprintln!("Attempt to mine poison-microblock");
    let mut found = false;
    for _i in 0..10 {
        if found {
            break;
        }
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let blocks = test_observer::get_blocks();
        for block in blocks.iter() {
            let transactions = block.get("transactions").unwrap().as_array().unwrap();
            for tx in transactions.iter() {
                let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
                if raw_tx == "0x00" {
                    continue;
                }
                let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
                let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();

                if let TransactionPayload::PoisonMicroblock(..) = &parsed.payload {
                    found = true;
                    break;
                }
            }
        }
    }

    assert!(
        found,
        "Did not find poison microblock tx in any mined block"
    );

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn microblock_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();
    let second_spender_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let second_spender_addr: PrincipalData = to_addr(&second_spender_sk).into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    conf.miner.wait_for_block_download = false;
    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });
    conf.initial_balances.push(InitialBalance {
        address: second_spender_addr.clone(),
        amount: 10000,
    });

    conf.node.mine_microblocks = true;
    conf.node.microblock_frequency = 1_000;
    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    info!("Miner account: {miner_account}");
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our first spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    // and our second spender
    let account = get_account(&http_origin, &second_spender_addr);
    assert_eq!(account.balance, 10000);
    assert_eq!(account.nonce, 0);

    // okay, let's push a transaction that is marked microblock only!
    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let tx = make_stacks_transfer_mblock_only(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1000,
    );
    submit_tx(&http_origin, &tx);

    info!("Try to mine a microblock-only tx");

    // now let's mine a couple blocks, and then check the sender's nonce.
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(10_000);

    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.
    info!("Wait for second block");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(10_000);

    // I guess let's push another block for good measure?
    info!("Wait for third block");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(10_000);

    info!("Test microblock");

    // microblock must have bumped our nonce
    // and our spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 1);

    // push another two transactions that are marked microblock only
    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
        &spender_sk,
        1,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1000,
    );
    let unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &unconfirmed_tx_bytes[..]).unwrap();
    let second_unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
        &second_spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1500,
    );
    let second_unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &second_unconfirmed_tx_bytes[..]).unwrap();

    // TODO (hack) instantiate the sortdb in the burnchain
    let _ = btc_regtest_controller.sortdb_mut();

    // put each into a microblock
    let (first_microblock, second_microblock) = {
        let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);
        let tip_hash =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &stacks_block.block_hash());
        let privk =
            find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024)
                .unwrap();
        let (mut chainstate, _) = StacksChainState::open(
            false,
            CHAIN_ID_TESTNET,
            &conf.get_chainstate_path_str(),
            None,
        )
        .unwrap();

        chainstate
            .reload_unconfirmed_state(
                &btc_regtest_controller
                    .sortdb_ref()
                    .index_handle_at_block(&chainstate, &tip_hash)
                    .unwrap(),
                tip_hash,
            )
            .unwrap();
        let iconn = btc_regtest_controller
            .sortdb_ref()
            .index_handle_at_block(&chainstate, &tip_hash)
            .unwrap();
        let first_microblock = make_microblock(
            &privk,
            &mut chainstate,
            &iconn,
            consensus_hash,
            stacks_block,
            vec![unconfirmed_tx],
        );

        eprintln!(
            "Created first microblock: {}: {first_microblock:?}",
            &first_microblock.block_hash()
        );
        /*
        let second_microblock =
            make_signed_microblock(&privk, vec![second_unconfirmed_tx], stacks_tip, 1);
        */
        let second_microblock = make_signed_microblock(
            &privk,
            vec![second_unconfirmed_tx],
            first_microblock.block_hash(),
            1,
        );
        eprintln!(
            "Created second microblock: {}: {second_microblock:?}",
            &second_microblock.block_hash()
        );
        (first_microblock, second_microblock)
    };

    let mut microblock_bytes = vec![];
    first_microblock
        .consensus_serialize(&mut microblock_bytes)
        .unwrap();

    // post the first microblock
    let path = format!("{http_origin}/v2/microblocks");
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &first_microblock.block_hash()));

    eprintln!("\n\nBegin testing\nmicroblock: {first_microblock:?}\n\n");

    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 98300);

    let mut second_microblock_bytes = vec![];
    second_microblock
        .consensus_serialize(&mut second_microblock_bytes)
        .unwrap();

    // post the second microblock
    let path = format!("{http_origin}/v2/microblocks");
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(second_microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &second_microblock.block_hash()));

    sleep_ms(5_000);

    let mut iter_count = 0;
    let tip_info = loop {
        let tip_info = get_chain_info(&conf);
        eprintln!("{:#?}", tip_info);
        match tip_info.unanchored_tip {
            None => {
                iter_count += 1;
                assert!(
                    iter_count < 10,
                    "Hit retry count while waiting for net module to process pushed microblock"
                );
                sleep_ms(5_000);
                continue;
            }
            Some(_tip) => break tip_info,
        }
    };

    assert!(tip_info.stacks_tip_height >= 3);
    let stacks_tip = tip_info.stacks_tip;
    let stacks_tip_consensus_hash = tip_info.stacks_tip_consensus_hash;
    let stacks_id_tip =
        StacksBlockHeader::make_index_block_hash(&stacks_tip_consensus_hash, &stacks_tip);

    // todo - pipe in the PoxSyncWatchdog to the RunLoop struct to avoid flakiness here
    // wait at least two p2p refreshes so it can produce the microblock
    for i in 0..30 {
        info!(
            "wait {} more seconds for microblock miner to find our transaction...",
            30 - i
        );
        sleep_ms(1000);
    }

    // check event observer for new microblock event (expect at least 2)
    let mut microblock_events = test_observer::get_microblocks();
    assert!(microblock_events.len() >= 2);

    // this microblock should correspond to `second_microblock`
    let microblock = microblock_events.pop().unwrap();
    let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
    assert_eq!(transactions.len(), 1);
    let tx_sequence = transactions[0]
        .get("microblock_sequence")
        .unwrap()
        .as_u64()
        .unwrap();
    assert_eq!(tx_sequence, 1);
    let microblock_hash = transactions[0]
        .get("microblock_hash")
        .unwrap()
        .as_str()
        .unwrap();
    assert_eq!(
        microblock_hash[2..],
        format!("{}", second_microblock.header.block_hash())
    );
    let microblock_associated_hash = microblock
        .get("parent_index_block_hash")
        .unwrap()
        .as_str()
        .unwrap();
    let index_block_hash_bytes = hex_bytes(&microblock_associated_hash[2..]).unwrap();
    assert_eq!(
        StacksBlockId::from_vec(&index_block_hash_bytes),
        Some(stacks_id_tip)
    );
    // make sure we have stats for the burn block
    let _burn_block_hash = microblock.get("burn_block_hash").unwrap().as_str().unwrap();
    let _burn_block_height = microblock
        .get("burn_block_height")
        .unwrap()
        .as_u64()
        .unwrap();
    let _burn_block_timestamp = microblock
        .get("burn_block_timestamp")
        .unwrap()
        .as_u64()
        .unwrap();

    // this microblock should correspond to the first microblock that was posted
    let microblock = microblock_events.pop().unwrap();
    let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
    assert_eq!(transactions.len(), 1);
    let tx_sequence = transactions[0]
        .get("microblock_sequence")
        .unwrap()
        .as_u64()
        .unwrap();
    assert_eq!(tx_sequence, 0);

    // check mempool tx events
    let memtx_events = test_observer::get_memtxs();
    assert_eq!(memtx_events.len(), 1);
    assert_eq!(&memtx_events[0], &format!("0x{}", &bytes_to_hex(&tx)));

    // let's make sure the returned blocks all point at each other.
    let blocks_observed = test_observer::get_blocks();
    // we at least mined 5 blocks
    assert!(
        blocks_observed.len() >= 3,
        "Blocks observed {} should be >= 3",
        blocks_observed.len()
    );
    assert_eq!(blocks_observed.len() as u64, tip_info.stacks_tip_height + 1);

    let burn_blocks_observed = test_observer::get_burn_blocks();
    let burn_blocks_with_burns: Vec<_> = burn_blocks_observed
        .into_iter()
        .filter(|block| block.get("burn_amount").unwrap().as_u64().unwrap() > 0)
        .collect();
    assert!(
        burn_blocks_with_burns.len() >= 3,
        "Burn block sortitions {} should be >= 3",
        burn_blocks_with_burns.len()
    );
    for burn_block in burn_blocks_with_burns {
        eprintln!("{burn_block}");
    }

    let mut prior = None;
    for block in blocks_observed.iter() {
        let parent_index_hash = block
            .get("parent_index_block_hash")
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();
        let my_index_hash = block
            .get("index_block_hash")
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();
        if let Some(ref previous_index_hash) = prior {
            assert_eq!(&parent_index_hash, previous_index_hash);
        }

        // make sure we have a burn_block_hash, burn_block_height and miner_txid

        let _burn_block_hash = block.get("burn_block_hash").unwrap().as_str().unwrap();

        let _burn_block_height = block.get("burn_block_height").unwrap().as_u64().unwrap();

        let _miner_txid = block.get("miner_txid").unwrap().as_str().unwrap();

        // make sure we have stats for the previous burn block
        let _parent_burn_block_hash = block
            .get("parent_burn_block_hash")
            .unwrap()
            .as_str()
            .unwrap();

        let _parent_burn_block_height = block
            .get("parent_burn_block_height")
            .unwrap()
            .as_u64()
            .unwrap();

        let _parent_burn_block_timestamp = block
            .get("parent_burn_block_timestamp")
            .unwrap()
            .as_u64()
            .unwrap();

        prior = Some(my_index_hash);
    }

    // we can query unconfirmed state from the microblock we announced
    let path = format!(
        "{http_origin}/v2/accounts/{spender_addr}?proof=0&tip={}",
        &tip_info.unanchored_tip.unwrap()
    );

    eprintln!("{path:?}");

    let mut iter_count = 0;
    let res = loop {
        let http_resp = client.get(&path).send().unwrap();

        info!("{:?}", http_resp);

        match http_resp.json::<AccountEntryResponse>() {
            Ok(x) => break x,
            Err(e) => {
                warn!("Failed to query {path}; will try again. Err = {e:?}");
                iter_count += 1;
                assert!(iter_count < 10, "Retry limit reached querying account");
                sleep_ms(1000);
                continue;
            }
        };
    };

    info!("Account Response = {res:#?}");
    assert_eq!(res.nonce, 2);
    assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 96300);

    // limited by chaining
    for next_nonce in 2..5 {
        // verify that the microblock miner can automatically pick up transactions
        debug!("Try to send unconfirmed tx from {spender_addr} to {recipient} nonce {next_nonce}");
        let unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
            &spender_sk,
            next_nonce,
            1000,
            conf.burnchain.chain_id,
            &recipient.into(),
            1000,
        );

        let path = format!("{http_origin}/v2/transactions");
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(unconfirmed_tx_bytes.clone())
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &unconfirmed_tx_bytes[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
            eprintln!("Sent {res}");
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // wait at least two p2p refreshes
        // so it can produce the microblock
        for i in 0..30 {
            debug!(
                "wait {} more seconds for microblock miner to find our transaction...",
                30 - i
            );
            sleep_ms(1000);
        }

        // we can query _new_ unconfirmed state from the microblock we announced
        let path = format!(
            "{http_origin}/v2/accounts/{spender_addr}?proof=0&tip={}",
            &tip_info.unanchored_tip.unwrap()
        );

        let res_text = client.get(&path).send().unwrap().text().unwrap();

        eprintln!("text of {path}\n{res_text}");

        let res = client
            .get(&path)
            .send()
            .unwrap()
            .json::<AccountEntryResponse>()
            .unwrap();
        eprintln!("{path:?}");
        eprintln!("{res:#?}");

        // advanced!
        assert_eq!(res.nonce, next_nonce + 1);
        assert_eq!(
            u128::from_str_radix(&res.balance[2..], 16).unwrap(),
            (96300 - 2000 * (next_nonce - 1)) as u128
        );
    }

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn filter_low_fee_tx_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sks: Vec<_> = (0..10).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, _) = neon_integration_test_conf();
    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    let txs: Vec<_> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            let recipient = StacksAddress::from_string(ADDR_4).unwrap();

            if ix < 5 {
                // low-fee
                make_stacks_transfer(
                    spender_sk,
                    0,
                    1000 + (ix as u64),
                    conf.burnchain.chain_id,
                    &recipient.into(),
                    1000,
                )
            } else {
                // high-fee
                make_stacks_transfer(
                    spender_sk,
                    0,
                    2000 + (ix as u64),
                    conf.burnchain.chain_id,
                    &recipient.into(),
                    1000,
                )
            }
        })
        .collect();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    for tx in txs.iter() {
        submit_tx(&http_origin, tx);
    }

    // mine a couple more blocks
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // First five accounts have a transaction. The miner will consider low fee transactions,
    //  but rank by estimated fee rate.
    // Last five accounts have transaction
    for spender_addr in &spender_addrs {
        let account = get_account(&http_origin, spender_addr);
        assert_eq!(account.nonce, 1);
    }

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn filter_long_runtime_tx_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sks: Vec<_> = (0..10).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, _) = neon_integration_test_conf();
    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    // ...but none of them will be mined since we allot zero ms to do so
    conf.miner.first_attempt_time_ms = 0;
    conf.miner.subsequent_attempt_time_ms = 0;

    let txs: Vec<_> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            let recipient = StacksAddress::from_string(ADDR_4).unwrap();
            make_stacks_transfer(
                spender_sk,
                0,
                1000 + (ix as u64),
                conf.burnchain.chain_id,
                &recipient.into(),
                1000,
            )
        })
        .collect();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    for tx in txs.iter() {
        submit_tx(&http_origin, tx);
    }

    // mine a couple more blocks
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // no transactions mined
    for spender_addr in &spender_addrs {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
    }

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn miner_submit_twice() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::random();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();
    let contract_content = "
       (define-public (foo (a int))
         (ok (* 2 (+ a 1))))
       (define-private (bar)
         (foo 56))
    ";

    let (mut conf, _) = neon_integration_test_conf();
    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 1049230,
    });

    conf.node.mine_microblocks = false;
    // one should be mined in first attempt, and two should be in second attempt
    conf.miner.first_attempt_time_ms = 20;
    conf.miner.subsequent_attempt_time_ms = 30_000;

    let tx_1 = make_contract_publish(
        &spender_sk,
        0,
        50_000,
        conf.burnchain.chain_id,
        "first-contract",
        contract_content,
    );
    let tx_2 = make_contract_publish(
        &spender_sk,
        1,
        50_000,
        conf.burnchain.chain_id,
        "second-contract",
        contract_content,
    );

    // note: this test depends on timing of how long it takes to assemble a block,
    //  but it won't flake if the miner behaves correctly: a correct miner should
    //  always be able to mine both transactions by the end of this test. an incorrect
    //  miner may sometimes pass this test though, if they can successfully mine a
    //  2-transaction block in 20 ms *OR* if they are slow enough that they mine a
    //  0-transaction block in that time (because this would trigger a re-attempt, which
    //  is exactly what this test is measuring).
    //
    // The "fixed" behavior is the corner case where a miner did a "first attempt", which
    //  included 1 or more transaction, but they could have made a second attempt with
    //  more transactions.

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    submit_tx(&http_origin, &tx_1);
    submit_tx(&http_origin, &tx_2);

    // mine a couple more blocks
    // waiting enough time between them that a second attempt could be made.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    thread::sleep(Duration::from_secs(15));
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // 1 transaction mined
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 2);

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn size_check_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut giant_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        giant_contract.push(' ');
    }

    let spender_sks: Vec<_> = (0..10).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    // make a bunch of txs that will only fit one per block.
    let txs: Vec<_> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                make_contract_publish(
                    spender_sk,
                    0,
                    1049230,
                    conf.burnchain.chain_id,
                    "large-0",
                    &giant_contract,
                )
            } else {
                let tx = make_contract_publish_microblock_only(
                    spender_sk,
                    0,
                    1049230,
                    conf.burnchain.chain_id,
                    "large-0",
                    &giant_contract,
                );
                let parsed_tx = StacksTransaction::consensus_deserialize(&mut &tx[..]).unwrap();
                debug!("Mine transaction {} in a microblock", &parsed_tx.txid());
                tx
            }
        })
        .collect();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5000;
    conf.node.microblock_frequency = 5000;
    conf.miner.microblock_attempt_time_ms = 120_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 1049230);
    }

    for tx in txs.iter() {
        // okay, let's push a bunch of transactions that can only fit one per block!
        submit_tx(&http_origin, tx);
    }

    let mut micro_block_txs = 0;
    let mut anchor_block_txs = 0;

    for i in 0..100 {
        // now let's mine a couple blocks, and then check the sender's nonce.
        //  at the end of mining three blocks, there should be _at least one_ transaction from the microblock
        //  only set that got mined (since the block before this one was empty, a microblock can
        //  be added),
        //  and a number of transactions from equal to the number anchor blocks will get mined.
        //
        // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        // this one will contain the sortition from above anchor block,
        //    which *should* have also confirmed the microblock.
        sleep_ms(10_000 * i);

        micro_block_txs = 0;
        anchor_block_txs = 0;

        // let's figure out how many micro-only and anchor-only txs got accepted
        //   by examining our account nonces:
        for (ix, spender_addr) in spender_addrs.iter().enumerate() {
            let res = get_account(&http_origin, &spender_addr);
            if res.nonce == 1 {
                if ix % 2 == 0 {
                    anchor_block_txs += 1;
                } else {
                    micro_block_txs += 1;
                }
            } else if res.nonce != 0 {
                panic!("Spender address nonce incremented past 1");
            }

            debug!("Spender {ix},{spender_addr}: {res:?}");
        }

        eprintln!("anchor_block_txs: {anchor_block_txs}, micro_block_txs: {micro_block_txs}");

        if anchor_block_txs >= 2 && micro_block_txs >= 2 {
            break;
        }
    }

    assert!(anchor_block_txs >= 2);
    assert!(micro_block_txs >= 2);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// if a microblock consumes the majority of the block budget, then _only_ a microblock will be
// mined for an epoch.
#[test]
#[ignore]
fn size_overflow_unconfirmed_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // stuff a gigantic contract into the anchored block
    let mut giant_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        giant_contract.push(' ');
    }

    // small-sized contracts for microblocks
    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        small_contract.push(' ');
    }

    let spender_sks: Vec<_> = (0..5).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                // almost fills a whole block
                vec![make_contract_publish(
                    spender_sk,
                    0,
                    1100000,
                    conf.burnchain.chain_id,
                    "large-0",
                    &giant_contract,
                )]
            } else {
                let mut ret = vec![];
                for i in 0..25 {
                    let tx = make_contract_publish_microblock_only(
                        spender_sk,
                        i as u64,
                        1100000,
                        conf.burnchain.chain_id,
                        &format!("small-{i}"),
                        &small_contract,
                    );
                    ret.push(tx);
                }
                ret
            }
        })
        .collect();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5_000;
    conf.node.microblock_frequency = 5_000;
    conf.miner.microblock_attempt_time_ms = 120_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    for tx_batch in txs.iter() {
        for tx in tx_batch.iter() {
            // okay, let's push a bunch of transactions that can only fit one per block!
            submit_tx(&http_origin, tx);
        }
    }

    while wait_for_microblocks(&microblocks_processed, 120) {
        info!("Waiting for microblocks to no longer be processed");
    }

    // now let's mine a couple blocks, and then check the sender's nonce.
    //  at the end of mining three blocks, there should be _two_ transactions from the microblock
    //  only set that got mined (since the block before this one was empty, a microblock can
    //  be added),
    //  and _two_ transactions from the two anchor blocks that got mined (and processed)
    //
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.

    while wait_for_microblocks(&microblocks_processed, 120) {
        info!("Waiting for microblocks to no longer be processed");
    }

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    sleep_ms(30_000);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 4); // genesis block + 3 blocks

    let mut max_big_txs_per_block = 0;
    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_block = 0;
    let mut total_big_txs_per_microblock = 0;

    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_anchored_txs = 0;
        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc, ..) = parsed.payload {
                if tsc.name.to_string().contains("large-") {
                    num_big_anchored_txs += 1;
                    total_big_txs_per_block += 1;
                } else if tsc.name.to_string().contains("small") {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }

        if num_big_anchored_txs > max_big_txs_per_block {
            max_big_txs_per_block = num_big_anchored_txs;
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {max_big_txs_per_microblock}, max_big_txs_per_block: {max_big_txs_per_block}, total_big_txs_per_block: {total_big_txs_per_block}, total_big_txs_per_microblock: {total_big_txs_per_microblock}"
    );

    assert!(max_big_txs_per_block > 0);
    assert!(max_big_txs_per_microblock > 0);
    assert!(total_big_txs_per_block > 0);
    assert!(total_big_txs_per_microblock > 0);

    // can't have too many
    assert!(max_big_txs_per_microblock <= 3);
    assert!(max_big_txs_per_block <= 1);

    // NOTE: last-mined blocks aren't counted by the observer
    assert!(total_big_txs_per_block <= 2);
    assert!(total_big_txs_per_microblock <= 3);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// mine a stream of microblocks, and verify that the miner won't let us overflow the size
#[test]
#[ignore]
fn size_overflow_unconfirmed_stream_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..((1024 * 1024 + 500) / 3) {
        small_contract.push(' ');
    }

    let spender_sks: Vec<_> = (0..20).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 1000;
    conf.node.microblock_frequency = 1000;
    conf.miner.microblock_attempt_time_ms = 120_000;
    conf.node.max_microblocks = 65536;
    conf.burnchain.max_rbf = 1000000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    let txs: Vec<_> = spender_sks
        .iter()
        .map(|spender_sk| {
            make_contract_publish_microblock_only(
                spender_sk,
                0,
                600000,
                conf.burnchain.chain_id,
                "small",
                &small_contract,
            )
        })
        .collect();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    let mut ctr = 0;
    while ctr < txs.len() {
        submit_tx(&http_origin, &txs[ctr]);
        if !wait_for_microblocks(&microblocks_processed, 60) {
            // we time out if we *can't* mine any more microblocks
            break;
        }
        ctr += 1;
    }

    // should be able to fit 5 transactions in, in 5 microblocks
    assert_eq!(ctr, 5);
    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("First confirmed microblock stream!");

    microblocks_processed.store(0, Ordering::SeqCst);

    while ctr < txs.len() {
        submit_tx(&http_origin, &txs[ctr]);
        ctr += 1;
    }
    wait_for_microblocks(&microblocks_processed, 60);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("Second confirmed microblock stream!");

    wait_for_microblocks(&microblocks_processed, 60);

    // confirm it
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // this test can sometimes miss a mine block event.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert!(blocks.len() >= 5, "Should have produced at least 5 blocks");

    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_microblock = 0;

    // NOTE: this only counts the number of txs per stream, not in each microblock
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc, ..) = parsed.payload {
                if tsc.name.to_string().contains("small") {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {max_big_txs_per_microblock}, total_big_txs_per_microblock: {total_big_txs_per_microblock}"
    );

    assert_eq!(max_big_txs_per_microblock, 5);
    assert!(total_big_txs_per_microblock >= 10);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// Mine a too-long microblock stream, and verify that the anchored block miner truncates it down to
// the longest prefix of the stream that can be mined.
#[test]
#[ignore]
fn size_overflow_unconfirmed_invalid_stream_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // create microblock streams that are too big
    env::set_var(core::FAULT_DISABLE_MICROBLOCKS_BYTES_CHECK, "1");
    env::set_var(core::FAULT_DISABLE_MICROBLOCKS_COST_CHECK, "1");

    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..((1024 * 1024 + 500) / 8) {
        small_contract.push(' ');
    }

    let spender_sks: Vec<_> = (0..25).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5_000;
    conf.node.microblock_frequency = 1_000;
    conf.miner.microblock_attempt_time_ms = 120_000;
    conf.node.max_microblocks = 65536;
    conf.burnchain.max_rbf = 1000000;

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .map(|spender_sk| {
            make_contract_publish_microblock_only(
                spender_sk,
                0,
                1149230,
                conf.burnchain.chain_id,
                "small",
                &small_contract,
            )
        })
        .collect();

    let mut epochs = EpochList::new(&*core::STACKS_EPOCHS_REGTEST);
    epochs[StacksEpochId::Epoch20].block_limit = core::BLOCK_LIMIT_MAINNET_20;
    conf.burnchain.epochs = Some(epochs);

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    let mut ctr = 0;
    for _i in 0..6 {
        submit_tx(&http_origin, &txs[ctr]);
        if !wait_for_microblocks(&microblocks_processed, 60) {
            break;
        }
        ctr += 1;
    }

    // confirm that we were able to use the fault-injection to *mine* 6 microblocks
    assert_eq!(ctr, 6);
    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("First confirmed microblock stream!");

    // confirm it
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 4); // genesis block + 3 blocks

    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_microblock = 0;

    // NOTE: this only counts the number of txs per stream, not in each microblock
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc, ..) = parsed.payload {
                if tsc.name.to_string().contains("small") {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {max_big_txs_per_microblock}, total_big_txs_per_microblock: {total_big_txs_per_microblock}"
    );

    assert_eq!(max_big_txs_per_microblock, 3);
    assert!(total_big_txs_per_microblock <= 6);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn runtime_overflow_unconfirmed_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sks: Vec<_> = (0..4).map(|_| StacksPrivateKey::random()).collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();
    let spender_addrs_c32: Vec<StacksAddress> = spender_sks.iter().map(to_addr).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 15000;
    conf.miner.microblock_attempt_time_ms = 120_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    let mut epochs = EpochList::new(&*core::STACKS_EPOCHS_REGTEST);
    epochs[StacksEpochId::Epoch20].block_limit = core::BLOCK_LIMIT_MAINNET_20;
    conf.burnchain.epochs = Some(epochs);

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                // almost fills a whole block
                vec![make_contract_publish(
                    spender_sk,
                    0,
                    1049230,
                    conf.burnchain.chain_id,
                    &format!("large-{ix}"),
                    &format!("
                        ;; a single one of these transactions consumes over half the runtime budget
                        (define-constant BUFF_TO_BYTE (list
                           0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f
                           0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19 0x1a 0x1b 0x1c 0x1d 0x1e 0x1f
                           0x20 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0x28 0x29 0x2a 0x2b 0x2c 0x2d 0x2e 0x2f
                           0x30 0x31 0x32 0x33 0x34 0x35 0x36 0x37 0x38 0x39 0x3a 0x3b 0x3c 0x3d 0x3e 0x3f
                           0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47 0x48 0x49 0x4a 0x4b 0x4c 0x4d 0x4e 0x4f
                           0x50 0x51 0x52 0x53 0x54 0x55 0x56 0x57 0x58 0x59 0x5a 0x5b 0x5c 0x5d 0x5e 0x5f
                           0x60 0x61 0x62 0x63 0x64 0x65 0x66 0x67 0x68 0x69 0x6a 0x6b 0x6c 0x6d 0x6e 0x6f
                           0x70 0x71 0x72 0x73 0x74 0x75 0x76 0x77 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
                           0x80 0x81 0x82 0x83 0x84 0x85 0x86 0x87 0x88 0x89 0x8a 0x8b 0x8c 0x8d 0x8e 0x8f
                           0x90 0x91 0x92 0x93 0x94 0x95 0x96 0x97 0x98 0x99 0x9a 0x9b 0x9c 0x9d 0x9e 0x9f
                           0xa0 0xa1 0xa2 0xa3 0xa4 0xa5 0xa6 0xa7 0xa8 0xa9 0xaa 0xab 0xac 0xad 0xae 0xaf
                           0xb0 0xb1 0xb2 0xb3 0xb4 0xb5 0xb6 0xb7 0xb8 0xb9 0xba 0xbb 0xbc 0xbd 0xbe 0xbf
                           0xc0 0xc1 0xc2 0xc3 0xc4 0xc5 0xc6 0xc7 0xc8 0xc9 0xca 0xcb 0xcc 0xcd 0xce 0xcf
                           0xd0 0xd1 0xd2 0xd3 0xd4 0xd5 0xd6 0xd7 0xd8 0xd9 0xda 0xdb 0xdc 0xdd 0xde 0xdf
                           0xe0 0xe1 0xe2 0xe3 0xe4 0xe5 0xe6 0xe7 0xe8 0xe9 0xea 0xeb 0xec 0xed 0xee 0xef
                           0xf0 0xf1 0xf2 0xf3 0xf4 0xf5 0xf6 0xf7 0xf8 0xf9 0xfa 0xfb 0xfc 0xfd 0xfe 0xff
                        ))
                        (define-private (crash-me-folder (input (buff 1)) (ctr uint))
                            (begin
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (+ u1 ctr)
                            )
                        )
                        (define-public (crash-me (name (string-ascii 128)))
                            (begin
                                (fold crash-me-folder BUFF_TO_BYTE u0)
                                (print name)
                                (ok u0)
                            )
                        )
                        (begin
                            (crash-me \"large-contract-{}-{ix}\"))
                        ",
                        &spender_addrs_c32[ix]
                    )
                )]
            } else {
                let mut ret = vec![];
                for i in 0..1 {
                    let tx = make_contract_publish_microblock_only(
                        spender_sk,
                        i as u64,
                        210000,
                        conf.burnchain.chain_id,
                        &format!("small-{ix}-{i}"),
                        &format!("
                            ;; a single one of these transactions consumes over half the runtime budget
                            (define-constant BUFF_TO_BYTE (list
                               0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f
                               0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19 0x1a 0x1b 0x1c 0x1d 0x1e 0x1f
                               0x20 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0x28 0x29 0x2a 0x2b 0x2c 0x2d 0x2e 0x2f
                               0x30 0x31 0x32 0x33 0x34 0x35 0x36 0x37 0x38 0x39 0x3a 0x3b 0x3c 0x3d 0x3e 0x3f
                               0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47 0x48 0x49 0x4a 0x4b 0x4c 0x4d 0x4e 0x4f
                               0x50 0x51 0x52 0x53 0x54 0x55 0x56 0x57 0x58 0x59 0x5a 0x5b 0x5c 0x5d 0x5e 0x5f
                               0x60 0x61 0x62 0x63 0x64 0x65 0x66 0x67 0x68 0x69 0x6a 0x6b 0x6c 0x6d 0x6e 0x6f
                               0x70 0x71 0x72 0x73 0x74 0x75 0x76 0x77 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
                               0x80 0x81 0x82 0x83 0x84 0x85 0x86 0x87 0x88 0x89 0x8a 0x8b 0x8c 0x8d 0x8e 0x8f
                               0x90 0x91 0x92 0x93 0x94 0x95 0x96 0x97 0x98 0x99 0x9a 0x9b 0x9c 0x9d 0x9e 0x9f
                               0xa0 0xa1 0xa2 0xa3 0xa4 0xa5 0xa6 0xa7 0xa8 0xa9 0xaa 0xab 0xac 0xad 0xae 0xaf
                               0xb0 0xb1 0xb2 0xb3 0xb4 0xb5 0xb6 0xb7 0xb8 0xb9 0xba 0xbb 0xbc 0xbd 0xbe 0xbf
                               0xc0 0xc1 0xc2 0xc3 0xc4 0xc5 0xc6 0xc7 0xc8 0xc9 0xca 0xcb 0xcc 0xcd 0xce 0xcf
                               0xd0 0xd1 0xd2 0xd3 0xd4 0xd5 0xd6 0xd7 0xd8 0xd9 0xda 0xdb 0xdc 0xdd 0xde 0xdf
                               0xe0 0xe1 0xe2 0xe3 0xe4 0xe5 0xe6 0xe7 0xe8 0xe9 0xea 0xeb 0xec 0xed 0xee 0xef
                               0xf0 0xf1 0xf2 0xf3 0xf4 0xf5 0xf6 0xf7 0xf8 0xf9 0xfa 0xfb 0xfc 0xfd 0xfe 0xff
                            ))
                            (define-private (crash-me-folder (input (buff 1)) (ctr uint))
                                (begin
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (+ u1 ctr)
                                )
                            )
                            (define-public (crash-me (name (string-ascii 128)))
                                (begin
                                    (fold crash-me-folder BUFF_TO_BYTE u0)
                                    (print name)
                                    (ok u0)
                                )
                            )
                            (begin
                                (crash-me \"small-contract-{}-{ix}-{i}\"))
                            ", spender_addrs_c32[ix])
                    );
                    ret.push(tx);
                }
                ret
            }
        })
        .collect();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 1049230);
    }

    for tx_batch in txs.iter() {
        for tx in tx_batch.iter() {
            // okay, let's push a bunch of transactions that can only fit one per block!
            submit_tx(&http_origin, tx);
        }
    }

    debug!("Wait for 1st microblock to be mined");
    sleep_ms(150_000);

    // now let's mine a couple blocks, and then check the sender's nonce.
    //  at the end of mining three blocks, there should be _two_ transactions from the microblock
    //  only set that got mined (since the block before this one was empty, a microblock can
    //  be added),
    //  and _two_ transactions from the two anchor blocks that got mined (and processed)
    //
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.

    debug!("Wait for 2nd microblock to be mined");
    sleep_ms(150_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    debug!("Wait for 3nd microblock to be mined");
    sleep_ms(150_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 5); // genesis block + 4 blocks

    let mut max_big_txs_per_block = 0;
    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_in_blocks = 0;
    let mut total_big_txs_in_microblocks = 0;

    for block in blocks {
        eprintln!("block {block:?}");
        let transactions = block.get("transactions").unwrap().as_array().unwrap();

        let mut num_big_anchored_txs = 0;
        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            eprintln!("tx: {parsed:?}");
            if let TransactionPayload::SmartContract(tsc, ..) = parsed.payload {
                if tsc.name.to_string().contains("large-") {
                    num_big_anchored_txs += 1;
                    total_big_txs_in_blocks += 1;
                } else if tsc.name.to_string().contains("small") {
                    num_big_microblock_txs += 1;
                    total_big_txs_in_microblocks += 1;
                }
            }
        }

        if num_big_anchored_txs > max_big_txs_per_block {
            max_big_txs_per_block = num_big_anchored_txs;
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    info!(
        "max_big_txs_per_microblock: {max_big_txs_per_microblock}, max_big_txs_per_block: {max_big_txs_per_block}"
    );
    info!(
        "total_big_txs_in_microblocks: {total_big_txs_in_microblocks}, total_big_txs_in_blocks: {total_big_txs_in_blocks}"
    );

    // at most one big tx per block and at most one big tx per stream, always.
    assert_eq!(max_big_txs_per_microblock, 1);
    assert_eq!(max_big_txs_per_block, 1);

    // if the mblock stream has a big tx, the anchored block won't (and vice versa)
    // the changes for miner cost tracking (reset tracker between microblock and block, #2913)
    // altered this test so that one more big tx ends up in an anchored block and one fewer
    // ends up in a microblock
    assert_eq!(total_big_txs_in_blocks, 2);
    assert_eq!(total_big_txs_in_microblocks, 1);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn block_replay_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 5_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:

    info!("Miner account: {miner_account}");
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let tx = make_stacks_transfer(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1000,
    );
    submit_tx(&http_origin, &tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // try and push the mined block back at the node lots of times
    let (tip_consensus_hash, tip_block) = get_tip_anchored_block(&conf);
    let mut tip_block_bytes = vec![];
    tip_block.consensus_serialize(&mut tip_block_bytes).unwrap();

    for i in 0..1024 {
        let path = format!("{http_origin}/v2/blocks/upload/{tip_consensus_hash}");
        let res_text = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tip_block_bytes.clone())
            .send()
            .unwrap()
            .text()
            .unwrap();

        eprintln!("{i}: text of {path}\n{res_text}");
    }

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn cost_voting_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // let's make `<` free...
    let cost_definer_src = "
    (define-read-only (cost-definition-le (size uint))
       {
         runtime: u0, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })
    ";

    // the contract that we'll test the costs of
    let caller_src = "
    (define-public (execute-2 (a uint))
       (ok (< a a)))
    ";

    let power_vote_src = "
    (define-public (propose-vote-confirm)
      (let
        ((proposal-id (unwrap-panic (contract-call? 'ST000000000000000000002AMW42H.cost-voting submit-proposal
                            'ST000000000000000000002AMW42H.costs \"cost_le\"
                            .cost-definer \"cost-definition-le\")))
         (vote-amount (* u9000000000 u1000000)))
        (try! (contract-call? 'ST000000000000000000002AMW42H.cost-voting vote-proposal proposal-id vote-amount))
        (try! (contract-call? 'ST000000000000000000002AMW42H.cost-voting confirm-votes proposal-id))
        (ok proposal-id)))
    ";

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 1_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.burnchain.max_rbf = 10_000_000;
    conf.node.wait_time_for_blocks = 1_000;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ.clone(),
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let res = get_account(&http_origin, &miner_account);
    assert_eq!(res.balance, 0);
    assert_eq!(res.nonce, 1);

    // and our spender:
    let res = get_account(&http_origin, &spender_princ);
    assert_eq!(res.balance, spender_bal as u128);
    assert_eq!(res.nonce, 0);

    let transactions = vec![
        make_contract_publish(
            &spender_sk,
            0,
            1000,
            conf.burnchain.chain_id,
            "cost-definer",
            cost_definer_src,
        ),
        make_contract_publish(
            &spender_sk,
            1,
            1000,
            conf.burnchain.chain_id,
            "caller",
            caller_src,
        ),
        make_contract_publish(
            &spender_sk,
            2,
            1000,
            conf.burnchain.chain_id,
            "voter",
            power_vote_src,
        ),
    ];

    for tx in transactions.into_iter() {
        submit_tx(&http_origin, &tx);
    }

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let vote_tx = make_contract_call(
        &spender_sk,
        3,
        1000,
        conf.burnchain.chain_id,
        &spender_addr,
        "voter",
        "propose-vote-confirm",
        &[],
    );

    let call_le_tx = make_contract_call(
        &spender_sk,
        4,
        1000,
        conf.burnchain.chain_id,
        &spender_addr,
        "caller",
        "execute-2",
        &[Value::UInt(1)],
    );

    submit_tx(&http_origin, &vote_tx);
    submit_tx(&http_origin, &call_le_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    let mut exec_cost = ExecutionCost::ZERO;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute-2" {
                exec_cost =
                    serde_json::from_value(tx.get("execution_cost").cloned().unwrap()).unwrap();
            } else if contract_call.function_name.as_str() == "propose-vote-confirm" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                assert_eq!(parsed.to_string(), "(ok u0)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    // try to confirm the passed vote (this will fail)
    let confirm_proposal = make_contract_call(
        &spender_sk,
        5,
        1000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "cost-voting",
        "confirm-miners",
        &[Value::UInt(0)],
    );

    submit_tx(&http_origin, &confirm_proposal);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "confirm-miners" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                assert_eq!(parsed.to_string(), "(err 13)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    for _i in 0..58 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }

    // confirm the passed vote
    let confirm_proposal = make_contract_call(
        &spender_sk,
        6,
        1000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "cost-voting",
        "confirm-miners",
        &[Value::UInt(0)],
    );

    submit_tx(&http_origin, &confirm_proposal);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "confirm-miners" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                assert_eq!(parsed.to_string(), "(ok true)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    let call_le_tx = make_contract_call(
        &spender_sk,
        7,
        1000,
        conf.burnchain.chain_id,
        &spender_addr,
        "caller",
        "execute-2",
        &[Value::UInt(1)],
    );

    submit_tx(&http_origin, &call_le_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();

    let mut tested = false;
    let mut new_exec_cost = ExecutionCost::max_value();
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute-2" {
                new_exec_cost =
                    serde_json::from_value(tx.get("execution_cost").cloned().unwrap()).unwrap();
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    assert!(exec_cost.exceeds(&new_exec_cost));

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn mining_events_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let small_contract = "(define-public (f) (ok 1))".to_string();

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let addr = to_addr(&spender_sk);

    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let addr_2 = to_addr(&spender_sk_2);

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: addr.into(),
        amount: 10000000,
    });
    conf.initial_balances.push(InitialBalance {
        address: addr_2.into(),
        amount: 10000000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 1000;
    conf.node.microblock_frequency = 1000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    let tx = make_contract_publish(
        &spender_sk,
        0,
        600000,
        conf.burnchain.chain_id,
        "small",
        &small_contract,
    );
    let tx_2 = make_contract_publish(
        &spender_sk,
        1,
        610000,
        conf.burnchain.chain_id,
        "small",
        &small_contract,
    );
    let mb_tx = make_contract_publish_microblock_only(
        &spender_sk_2,
        0,
        620000,
        conf.burnchain.chain_id,
        "small",
        &small_contract,
    );

    test_observer::spawn();
    test_observer::register(
        &mut conf,
        &[
            EventKeyType::AnyEvent,
            EventKeyType::MinedBlocks,
            EventKeyType::MinedMicroblocks,
        ],
    );

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    submit_tx(&http_origin, &tx); // should succeed
    submit_tx(&http_origin, &tx_2); // should fail since it tries to publish contract with same name
    submit_tx(&http_origin, &mb_tx); // should be in microblock bc it is microblock only

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // check that the nonces have gone up
    let res = get_account(&http_origin, &addr);
    assert_eq!(res.nonce, 1);

    let res = get_account(&http_origin, &addr_2);
    assert_eq!(res.nonce, 1);

    // check mined microblock events
    let mined_microblock_events = test_observer::get_mined_microblocks();
    assert!(!mined_microblock_events.is_empty());

    // check tx events in the first microblock
    // 1 success: 1 contract publish, 2 error (on chain transactions)
    let microblock_tx_events = &mined_microblock_events[0].tx_events;
    assert_eq!(microblock_tx_events.len(), 1);

    // contract publish
    match &microblock_tx_events[0] {
        TransactionEvent::Success(TransactionSuccessEvent {
            result,
            fee,
            execution_cost,
            ..
        }) => {
            assert!(result
                .clone()
                .expect_result_ok()
                .unwrap()
                .expect_bool()
                .unwrap());
            assert_eq!(fee, &620000);
            assert_eq!(
                execution_cost,
                &ExecutionCost {
                    write_length: 35,
                    write_count: 2,
                    read_length: 1,
                    read_count: 1,
                    runtime: 311000
                }
            )
        }
        _ => panic!("unexpected event type"),
    }

    // check mined block events
    let mined_block_events = test_observer::get_mined_blocks();
    assert!(mined_block_events.len() >= 3);

    // check the tx events in the third mined block
    // 2 success: 1 coinbase tx event + 1 contract publish, 1 error (duplicate contract)
    let third_block_tx_events = &mined_block_events[2].tx_events;
    assert_eq!(third_block_tx_events.len(), 3);

    // coinbase event
    match &third_block_tx_events[0] {
        TransactionEvent::Success(TransactionSuccessEvent { txid, result, .. }) => {
            assert_eq!(
                txid.to_string(),
                "3e04ada5426332bfef446ba0a06d124aace4ade5c11840f541bf88e2e919faf6"
            );
            assert!(result
                .clone()
                .expect_result_ok()
                .unwrap()
                .expect_bool()
                .unwrap());
        }
        _ => panic!("unexpected event type"),
    }

    // contract publish event
    match &third_block_tx_events[1] {
        TransactionEvent::Success(TransactionSuccessEvent {
            result,
            fee,
            execution_cost,
            ..
        }) => {
            assert!(result
                .clone()
                .expect_result_ok()
                .unwrap()
                .expect_bool()
                .unwrap());
            assert_eq!(fee, &600000);
            assert_eq!(
                execution_cost,
                &ExecutionCost {
                    write_length: 35,
                    write_count: 2,
                    read_length: 1,
                    read_count: 1,
                    runtime: 311000
                }
            )
        }
        _ => panic!("unexpected event type"),
    }

    // dupe contract error event
    match &third_block_tx_events[2] {
        TransactionEvent::ProcessingError(TransactionErrorEvent { txid: _, error }) => {
            assert_eq!(
                error,
                "Duplicate contract 'ST3WM51TCWMJYGZS1QFMC28DH5YP86782YGR113C1.small'"
            );
        }
        _ => panic!("unexpected event type"),
    }

    test_observer::clear();
    channel.stop_chains_coordinator();
}

/// This test checks that the limit behavior in the miner works as expected for anchored block
/// building. When we first hit the block limit, the limit behavior switches to
/// `CONTRACT_LIMIT_HIT`, during which stx transfers are still allowed, and contract related
/// transactions are skipped.
/// Note: the test is sensitive to the order in which transactions are mined; it is written
/// expecting that transactions are traversed in the order tx_1, tx_2, tx_3, and tx_4.
#[test]
#[ignore]
fn block_limit_hit_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // 700 invocations
    let max_contract_src = format!(
         "(define-private (work) (begin {} 1))
         (define-private (times-100) (begin {} 1))
         (define-private (times-200) (begin (times-100) (times-100) 1))
         (define-private (times-500) (begin (times-200) (times-200) (times-100) 1))
         (times-500) (times-200)",
         (0..10)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") 2)",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" "),
         (0..10)
             .map(|_| "(work)".to_string())
             .collect::<Vec<String>>()
             .join(" "),
    );

    // 2900 invocations
    let oversize_contract_src = format!(
        "(define-private (work) (begin {} 1))
         (define-private (times-100) (begin {} 1))
         (define-private (times-200) (begin (times-100) (times-100) 1))
         (define-private (times-500) (begin (times-200) (times-200) (times-100) 1))
         (define-private (times-1000) (begin (times-500) (times-500) 1))
         (times-1000) (times-1000) (times-500) (times-200) (times-200)",
        (0..10)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") 2)",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" "),
        (0..10)
            .map(|_| "(work)".to_string())
            .collect::<Vec<String>>()
            .join(" "),
    );

    let spender_sk = StacksPrivateKey::random();
    let addr = to_addr(&spender_sk);
    let second_spender_sk = StacksPrivateKey::random();
    let second_spender_addr: PrincipalData = to_addr(&second_spender_sk).into();
    let third_spender_sk = StacksPrivateKey::random();
    let third_spender_addr: PrincipalData = to_addr(&third_spender_sk).into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: addr.into(),
        amount: 10_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: second_spender_addr.clone(),
        amount: 10_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: third_spender_addr.clone(),
        amount: 10_000_000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 1000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    // included in first block
    let tx = make_contract_publish(
        &spender_sk,
        0,
        555_000,
        conf.burnchain.chain_id,
        "over",
        &oversize_contract_src,
    );
    // contract limit hit; included in second block
    let tx_2 = make_contract_publish(
        &spender_sk,
        1,
        555_000,
        conf.burnchain.chain_id,
        "over-2",
        &oversize_contract_src,
    );
    // skipped over since contract limit was hit; included in second block
    let tx_3 = make_contract_publish(
        &second_spender_sk,
        0,
        150_000,
        conf.burnchain.chain_id,
        "max",
        &max_contract_src,
    );
    // included in first block
    let tx_4 = make_stacks_transfer(
        &third_spender_sk,
        0,
        180,
        conf.burnchain.chain_id,
        &PrincipalData::from(addr),
        100,
    );

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // submit all the transactions
    let txid_1 = submit_tx(&http_origin, &tx);
    let txid_2 = submit_tx(&http_origin, &tx_2);
    let txid_3 = submit_tx(&http_origin, &tx_3);
    let txid_4 = submit_tx(&http_origin, &tx_4);

    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(20_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(20_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(20_000);

    let res = get_account(&http_origin, &addr);
    assert_eq!(res.nonce, 2);

    let res = get_account(&http_origin, &second_spender_addr);
    assert_eq!(res.nonce, 1);

    let res = get_account(&http_origin, &third_spender_addr);
    assert_eq!(res.nonce, 1);

    let mined_block_events = test_observer::get_blocks();
    assert_eq!(mined_block_events.len(), 5);

    let tx_third_block = mined_block_events[3]
        .get("transactions")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(tx_third_block.len(), 3);
    let txid_1_exp = tx_third_block[1].get("txid").unwrap().as_str().unwrap();
    let txid_4_exp = tx_third_block[2].get("txid").unwrap().as_str().unwrap();
    assert_eq!(format!("0x{txid_1}"), txid_1_exp);
    assert_eq!(format!("0x{txid_4}"), txid_4_exp);

    let tx_fourth_block = mined_block_events[4]
        .get("transactions")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(tx_fourth_block.len(), 3);
    let txid_2_exp = tx_fourth_block[1].get("txid").unwrap().as_str().unwrap();
    let txid_3_exp = tx_fourth_block[2].get("txid").unwrap().as_str().unwrap();
    assert_eq!(format!("0x{txid_2}"), txid_2_exp);
    assert_eq!(format!("0x{txid_3}"), txid_3_exp);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

/// This test checks that the limit behavior in the miner works as expected during microblock
/// building. When we first hit the block limit, the limit behavior switches to
/// `CONTRACT_LIMIT_HIT`, during which stx transfers are still allowed, and contract related
/// transactions are skipped.
/// Note: the test is sensitive to the order in which transactions are mined; it is written
/// expecting that transactions are traversed in the order tx_1, tx_2, tx_3, and tx_4.
#[test]
#[ignore]
fn microblock_limit_hit_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let max_contract_src = format!(
        "(define-private (work) (begin {} 1))
         (define-private (times-100) (begin {} 1))
         (define-private (times-200) (begin (times-100) (times-100) 1))
         (define-private (times-500) (begin (times-200) (times-200) (times-100) 1))
         (times-500) (times-200)",
        (0..3)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") 2)",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" "),
        (0..3)
            .map(|_| "(work)".to_string())
            .collect::<Vec<String>>()
            .join(" "),
    );

    let oversize_contract_src = format!(
        "(define-private (work) (begin {} 1))
         (define-private (times-100) (begin {} 1))
         (define-private (times-200) (begin (times-100) (times-100) 1))
         (define-private (times-500) (begin (times-200) (times-200) (times-100) 1))
         (define-private (times-1000) (begin (times-500) (times-500) 1))
         (times-1000) (times-1000) (times-500) (times-200) (times-200)",
        (0..3)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") 2)",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" "),
        (0..3)
            .map(|_| "(work)".to_string())
            .collect::<Vec<String>>()
            .join(" "),
    );

    let spender_sk = StacksPrivateKey::random();
    let addr = to_addr(&spender_sk);
    let second_spender_sk = StacksPrivateKey::random();
    let second_spender_addr: PrincipalData = to_addr(&second_spender_sk).into();
    let third_spender_sk = StacksPrivateKey::random();
    let third_spender_addr: PrincipalData = to_addr(&third_spender_sk).into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: addr.into(),
        amount: 10_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: second_spender_addr.clone(),
        amount: 10_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: third_spender_addr.clone(),
        amount: 10_000_000,
    });

    conf.node.mine_microblocks = true;
    // conf.node.wait_time_for_microblocks = 30000;
    conf.node.wait_time_for_microblocks = 1000;
    conf.node.microblock_frequency = 1000;

    conf.miner.microblock_attempt_time_ms = i64::MAX as u64;
    conf.burnchain.max_rbf = 10_000_000;
    conf.node.wait_time_for_blocks = 1_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 10_000,
            block_limit: ExecutionCost {
                write_length: 150000000,
                write_count: 50000,
                read_length: 1000000000,
                read_count: 5000, // make read_count smaller so we hit the read_count limit with a smaller tx.
                runtime: 100_000_000_000,
            },
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 10_000,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // included in the first block
    let tx = make_contract_publish_microblock_only(
        &spender_sk,
        0,
        555_000,
        conf.burnchain.chain_id,
        "over",
        &oversize_contract_src,
    );
    // contract limit hit; included in second block
    let tx_2 = make_contract_publish_microblock_only(
        &spender_sk,
        1,
        555_000,
        conf.burnchain.chain_id,
        "over-2",
        &oversize_contract_src,
    );
    // skipped over since contract limit was hit; included in second block
    let tx_3 = make_contract_publish_microblock_only(
        &second_spender_sk,
        0,
        150_000,
        conf.burnchain.chain_id,
        "max",
        &max_contract_src,
    );
    // included in first block
    let tx_4 = make_stacks_transfer_mblock_only(
        &third_spender_sk,
        0,
        180,
        conf.burnchain.chain_id,
        &PrincipalData::from(addr),
        100,
    );

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // submit all the transactions
    let txid_1 = submit_tx(&http_origin, &tx);
    let txid_2 = submit_tx(&http_origin, &tx_2);
    let txid_3 = submit_tx(&http_origin, &tx_3);
    let txid_4 = submit_tx(&http_origin, &tx_4);

    eprintln!("transactions: {txid_1},{txid_2},{txid_3},{txid_4}");

    sleep_ms(50_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(50_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(50_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(50_000);

    loop {
        let res = get_account(&http_origin, &addr);
        if res.nonce < 2 {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sleep_ms(50_000);
        } else {
            break;
        }
    }

    let res = get_account(&http_origin, &addr);
    assert_eq!(res.nonce, 2);

    let res = get_account(&http_origin, &second_spender_addr);
    assert_eq!(res.nonce, 1);

    let res = get_account(&http_origin, &third_spender_addr);
    assert_eq!(res.nonce, 1);

    let mined_mblock_events = test_observer::get_microblocks();
    assert!(mined_mblock_events.len() >= 2);

    let tx_first_mblock = mined_mblock_events[0]
        .get("transactions")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(tx_first_mblock.len(), 2);
    let txid_1_exp = tx_first_mblock[0].get("txid").unwrap().as_str().unwrap();
    let txid_4_exp = tx_first_mblock[1].get("txid").unwrap().as_str().unwrap();
    assert_eq!(format!("0x{txid_1}"), txid_1_exp);
    assert_eq!(format!("0x{txid_4}"), txid_4_exp);

    let tx_second_mblock = mined_mblock_events[1]
        .get("transactions")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(tx_second_mblock.len(), 2);
    let txid_2_exp = tx_second_mblock[0].get("txid").unwrap().as_str().unwrap();
    let txid_3_exp = tx_second_mblock[1].get("txid").unwrap().as_str().unwrap();
    assert_eq!(format!("0x{txid_2}"), txid_2_exp);
    assert_eq!(format!("0x{txid_3}"), txid_3_exp);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn block_large_tx_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let small_contract_src = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        (0..700)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" ")
    );

    let oversize_contract_src = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        (0..3500)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" ")
    );

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);

    let (mut conf, miner_account) = neon_integration_test_conf();
    test_observer::spawn();
    test_observer::register_any(&mut conf);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.into(),
        amount: 10000000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 1000;

    conf.miner.microblock_attempt_time_ms = i64::MAX as u64;
    conf.burnchain.max_rbf = 10_000_000;
    conf.node.wait_time_for_blocks = 1_000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    // higher fee for tx means it will get mined first
    let tx = make_contract_publish(
        &spender_sk,
        0,
        671_000,
        conf.burnchain.chain_id,
        "small",
        &small_contract_src,
    );
    let tx_2 = make_contract_publish(
        &spender_sk,
        1,
        670_000,
        conf.burnchain.chain_id,
        "over",
        &oversize_contract_src,
    );

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 0);
    assert_eq!(account.balance, 10000000);

    let normal_txid = submit_tx(&http_origin, &tx);
    let huge_txid = submit_tx(&http_origin, &tx_2);

    eprintln!("Try to mine a too-big tx. Normal = {normal_txid}, TooBig = {huge_txid}");
    next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 1200);

    eprintln!("Finished trying to mine a too-big tx");

    let dropped_txs = test_observer::get_memtx_drops();
    assert_eq!(dropped_txs.len(), 1);
    assert_eq!(&dropped_txs[0].1, "TooExpensive");
    assert_eq!(&dropped_txs[0].0, &format!("0x{huge_txid}"));

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
#[allow(non_snake_case)]
fn microblock_large_tx_integration_test_FLAKY() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let small_contract_src = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        (0..700)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" ")
    );

    // publishing this contract takes up >80% of the read_count budget (which is 50000)
    let oversize_contract_src = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        (0..3500)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" ")
    );

    let spender_sk = StacksPrivateKey::random();
    let addr = to_addr(&spender_sk);

    let (mut conf, miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    conf.initial_balances.push(InitialBalance {
        address: addr.into(),
        amount: 10000000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 1000;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.burnchain.max_rbf = 10_000_000;
    conf.node.wait_time_for_blocks = 1_000;

    let tx = make_contract_publish_microblock_only(
        &spender_sk,
        0,
        150_000,
        conf.burnchain.chain_id,
        "small",
        &small_contract_src,
    );
    let tx_2 = make_contract_publish_microblock_only(
        &spender_sk,
        1,
        670_000,
        conf.burnchain.chain_id,
        "over",
        &oversize_contract_src,
    );

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    let account = get_account(&http_origin, &addr);
    assert_eq!(account.nonce, 0);
    assert_eq!(account.balance, 10000000);

    submit_tx(&http_origin, &tx);
    let huge_txid = submit_tx(&http_origin, &tx_2);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(20_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Check that the microblock contains the first tx.
    let microblock_events = test_observer::get_microblocks();
    assert!(!microblock_events.is_empty());

    let microblock = microblock_events[0].clone();
    let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
    assert_eq!(transactions.len(), 1);
    let status = transactions[0].get("status").unwrap().as_str().unwrap();
    assert_eq!(status, "success");

    // Check that the tx that triggered TransactionTooLargeError when being processed is dropped
    // from the mempool.
    let dropped_txs = test_observer::get_memtx_drops();
    assert_eq!(dropped_txs.len(), 1);
    assert_eq!(&dropped_txs[0].1, "TooExpensive");
    assert_eq!(&dropped_txs[0].0, &format!("0x{huge_txid}"));

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn pox_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::random();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let spender_2_sk = StacksPrivateKey::random();
    let spender_2_addr: PrincipalData = to_addr(&spender_2_sk).into();

    let spender_3_sk = StacksPrivateKey::random();
    let spender_3_addr: PrincipalData = to_addr(&spender_3_sk).into();

    let pox_pubkey = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey).to_bytes());

    let pox_2_pubkey = Secp256k1PublicKey::from_private(&StacksPrivateKey::random());
    let pox_2_pubkey_hash = bytes_to_hex(&Hash160::from_node_public_key(&pox_2_pubkey).to_bytes());

    let pox_2_address = BitcoinAddress::from_bytes_legacy(
        BitcoinNetworkType::Testnet,
        LegacyBitcoinAddressType::PublicKeyHash,
        &Hash160::from_node_public_key(&pox_2_pubkey).to_bytes(),
    )
    .unwrap();

    let (mut conf, miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    // required for testing post-sunset behavior
    conf.node.always_use_affirmation_maps = false;

    let first_bal = 6_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);
    let second_bal = 2_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);
    let third_bal = 2_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);
    let stacked_bal = 1_000_000_000 * u128::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: first_bal,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_2_addr,
        amount: second_bal,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_3_addr,
        amount: third_bal,
    });

    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 1_000;
    conf.burnchain.max_rbf = 10_000_000;
    conf.node.wait_time_for_blocks = 1_000;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    // reward cycle length = 15, so 10 reward cycle slots + 5 prepare-phase burns
    let reward_cycle_len = 15;
    let prepare_phase_len = 5;
    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        4 * prepare_phase_len / 5,
        5,
        15,
        (16 * reward_cycle_len - 1).into(),
        (17 * reward_cycle_len).into(),
        u32::MAX,
        u32::MAX,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants.clone();

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);
    let burnchain = burnchain_config.clone();

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let sort_height = channel.get_sortitions_processed();

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our potential spenders:
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, first_bal as u128);
    assert_eq!(account.nonce, 0);

    let pox_info = get_pox_info(&http_origin).unwrap();

    assert_eq!(&pox_info.contract_id, "ST000000000000000000002AMW42H.pox");
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 0);
    assert!(!pox_info.current_cycle.is_pox_active);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 0);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 210);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 205);
    assert_eq!(pox_info.next_cycle.min_increment_ustx, 1250710410920);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        Some(pox_constants.pox_rejection_fraction)
    );
    let reward_cycle = burnchain
        .block_height_to_reward_cycle(sort_height)
        .expect("Expected to be able to get reward cycle");
    assert_eq!(pox_info.reward_cycle_id, reward_cycle);
    assert_eq!(pox_info.current_cycle.id, reward_cycle);
    assert_eq!(pox_info.next_cycle.id, reward_cycle + 1);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.total_liquid_supply_ustx, 10005683287360023);
    assert_eq!(pox_info.next_reward_cycle_in, 6);

    let tx = make_contract_call(
        &spender_sk,
        0,
        260,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal),
            execute(
                &format!("{{ hashbytes: 0x{pox_pubkey_hash}, version: 0x00 }}"),
                ClarityVersion::Clarity1,
            )
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    // okay, let's push that stacking transaction!
    submit_tx(&http_origin, &tx);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {sort_height}");
    test_observer::clear();

    // now let's mine until the next reward cycle starts ...
    while sort_height < ((14 * pox_constants.reward_cycle_length) + 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    let pox_info = get_pox_info(&http_origin).unwrap();
    let reward_cycle = burnchain
        .block_height_to_reward_cycle(sort_height)
        .expect("Expected to be able to get reward cycle");

    assert_eq!(&pox_info.contract_id, "ST000000000000000000002AMW42H.pox");
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 1000000000000000);
    assert!(pox_info.pox_activation_threshold_ustx > 1500000000000000);
    assert!(!pox_info.current_cycle.is_pox_active);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 1000000000000000);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 225);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 220);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        Some(pox_constants.pox_rejection_fraction)
    );
    assert_eq!(pox_info.reward_cycle_id, reward_cycle);
    assert_eq!(pox_info.current_cycle.id, reward_cycle);
    assert_eq!(pox_info.next_cycle.id, reward_cycle + 1);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.next_reward_cycle_in, 14);

    let blocks_observed = test_observer::get_blocks();
    assert!(
        blocks_observed.len() >= 2,
        "Blocks observed {} should be >= 2",
        blocks_observed.len()
    );

    // look up the return value of our stacking operation...
    let mut tested = false;
    for block in blocks_observed.iter() {
        if tested {
            break;
        }
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
                eprintln!("{}", contract_call.function_name.as_str());
                if contract_call.function_name.as_str() == "stack-stx" {
                    let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                    let parsed = Value::try_deserialize_hex_untyped(&raw_result[2..]).unwrap();
                    // should unlock at height 300 (we're in reward cycle 13, lockup starts in reward cycle
                    // 14, and goes for 6 blocks, so we unlock in reward cycle 20, which with a reward
                    // cycle length of 15 blocks, is a burnchain height of 300)
                    assert_eq!(parsed.to_string(),
                               format!("(ok (tuple (lock-amount u1000000000000000) (stacker {spender_addr}) (unlock-burn-height u300)))"));
                    tested = true;
                }
            }
        }
    }

    assert!(tested, "Should have observed stack-stx transaction");

    // let's stack with spender 2 and spender 3...

    // now let's have sender_2 and sender_3 stack to pox spender_addr 2 in
    //  two different txs, and make sure that they sum together in the reward set.

    let tx = make_contract_call(
        &spender_2_sk,
        0,
        260,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal / 2),
            execute(
                &format!("{{ hashbytes: 0x{pox_2_pubkey_hash}, version: 0x00 }}"),
                ClarityVersion::Clarity1,
            )
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    // okay, let's push that stacking transaction!
    submit_tx(&http_origin, &tx);

    let tx = make_contract_call(
        &spender_3_sk,
        0,
        260,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal / 2),
            execute(
                &format!("{{ hashbytes: 0x{pox_2_pubkey_hash}, version: 0x00 }}"),
                ClarityVersion::Clarity1,
            )
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    submit_tx(&http_origin, &tx);

    // mine until the end of the current reward cycle.
    sort_height = channel.get_sortitions_processed();
    while sort_height < ((15 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    let pox_info = get_pox_info(&http_origin).unwrap();

    assert_eq!(&pox_info.contract_id, "ST000000000000000000002AMW42H.pox");
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 1000000000000000);
    assert!(!pox_info.current_cycle.is_pox_active);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 2000000000000000);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 225);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 220);
    assert_eq!(pox_info.next_cycle.blocks_until_prepare_phase, -4);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        Some(pox_constants.pox_rejection_fraction)
    );
    assert_eq!(pox_info.reward_cycle_id, 14);
    assert_eq!(pox_info.current_cycle.id, 14);
    assert_eq!(pox_info.next_cycle.id, 15);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.next_reward_cycle_in, 1);

    // we should have received _no_ Bitcoin commitments, because the pox participation threshold
    //   was not met!
    let utxos = btc_regtest_controller.get_all_utxos(&pox_pubkey);
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        0,
        "Should have received no outputs during PoX reward cycle"
    );

    // let's test the reward information in the observer
    test_observer::clear();

    // before sunset
    // mine until the end of the next reward cycle,
    //   the participation threshold now should be met.
    while sort_height < ((16 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    let pox_info = get_pox_info(&http_origin).unwrap();

    assert_eq!(&pox_info.contract_id, "ST000000000000000000002AMW42H.pox");
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 2000000000000000);
    assert!(pox_info.current_cycle.is_pox_active);
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 240);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 235);
    assert_eq!(pox_info.next_cycle.blocks_until_prepare_phase, -4);
    assert_eq!(pox_info.next_reward_cycle_in, 1);

    // we should have received _seven_ Bitcoin commitments, because our commitment was 7 * threshold
    let utxos = btc_regtest_controller.get_all_utxos(&pox_pubkey);

    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        7,
        "Should have received outputs during PoX reward cycle"
    );

    // we should have received _seven_ Bitcoin commitments to pox_2_pubkey, because our commitment was 7 * threshold
    //   note: that if the reward set "summing" isn't implemented, this recipient would only have received _6_ slots,
    //         because each `stack-stx` call only received enough to get 3 slot individually.
    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        7,
        "Should have received outputs during PoX reward cycle"
    );

    let burn_blocks = test_observer::get_burn_blocks();
    let mut recipient_slots: HashMap<String, u64> = HashMap::new();

    for block in burn_blocks.iter() {
        let reward_slot_holders = block
            .get("reward_slot_holders")
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string());
        for holder in reward_slot_holders {
            if let Some(current) = recipient_slots.get_mut(&holder) {
                *current += 1;
            } else {
                recipient_slots.insert(holder, 1);
            }
        }
    }

    let pox_1_address = BitcoinAddress::from_bytes_legacy(
        BitcoinNetworkType::Testnet,
        LegacyBitcoinAddressType::PublicKeyHash,
        &Hash160::from_node_public_key(&pox_pubkey).to_bytes(),
    )
    .unwrap();

    assert_eq!(recipient_slots.len(), 2);
    assert_eq!(
        recipient_slots.get(&format!("{pox_2_address}")).cloned(),
        Some(7u64)
    );
    assert_eq!(
        recipient_slots.get(&format!("{pox_1_address}")).cloned(),
        Some(7u64)
    );

    // get the canonical chain tip
    let tip_info = get_chain_info(&conf);

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 36);

    // now let's mine into the sunset
    while sort_height < ((17 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    // get the canonical chain tip
    let tip_info = get_chain_info(&conf);

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 51);

    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    // should receive more rewards during this cycle...
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        14,
        "Should have received more outputs during the sunsetting PoX reward cycle"
    );

    // and after sunset
    while sort_height < ((18 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    // should *not* receive more rewards during the after sunset cycle...
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        14,
        "Should have received no more outputs after sunset PoX reward cycle"
    );

    // should have progressed the chain, though!
    // get the canonical chain tip
    let tip_info = get_chain_info(&conf);

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 66);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[derive(Debug)]
enum Signal {
    BootstrapNodeReady,
    FollowerNodeReady,
    ReplicatingAttachmentsStartTest1,
    ReplicatingAttachmentsCheckTest1(u64),
    ReplicatingAttachmentsStartTest2,
    ReplicatingAttachmentsCheckTest2(u64),
}

#[test]
#[ignore]
fn atlas_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let user_1 = StacksPrivateKey::random();
    let initial_balance_user_1 = InitialBalance {
        address: to_addr(&user_1).into(),
        amount: 1_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS),
    };

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    let bootstrap_node_public_key = {
        let keychain = Keychain::default(conf_bootstrap_node.node.seed.clone());
        let mut pk = keychain.generate_op_signer().get_public_key();
        pk.set_compressed(true);
        pk.to_hex()
    };
    conf_bootstrap_node
        .initial_balances
        .push(initial_balance_user_1.clone());

    conf_bootstrap_node.node.always_use_affirmation_maps = false;

    // Prepare the config of the follower node
    let (mut conf_follower_node, _) = neon_integration_test_conf();
    let bootstrap_node_url = format!(
        "{}@{}",
        bootstrap_node_public_key, conf_bootstrap_node.node.p2p_bind
    );
    conf_follower_node.node.set_bootstrap_nodes(
        bootstrap_node_url,
        conf_follower_node.burnchain.chain_id,
        conf_follower_node.burnchain.peer_version,
    );
    conf_follower_node.node.miner = false;
    conf_follower_node
        .initial_balances
        .push(initial_balance_user_1.clone());
    conf_follower_node
        .events_observers
        .insert(EventObserverConfig {
            endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
            events_keys: vec![EventKeyType::AnyEvent],
            timeout_ms: 1000,
            lossy: false,
        });

    conf_follower_node.node.always_use_affirmation_maps = false;

    // Our 2 nodes will share the bitcoind node
    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let (bootstrap_node_tx, bootstrap_node_rx) = mpsc::channel();
    let (follower_node_tx, follower_node_rx) = mpsc::channel();

    let bootstrap_node_thread = thread::spawn(move || {
        let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());

        let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
            conf_bootstrap_node.clone(),
            None,
            Some(burnchain_config.clone()),
            None,
        );
        let http_origin = format!("http://{}", &conf_bootstrap_node.node.rpc_bind);

        btc_regtest_controller.bootstrap_chain(201);

        eprintln!("Chain bootstrapped...");

        let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
        let blocks_processed = run_loop.get_blocks_processed_arc();
        let client = reqwest::blocking::Client::new();
        let channel = run_loop.get_coordinator_channel().unwrap();

        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

        // give the run loop some time to start up!
        wait_for_runloop(&blocks_processed);

        // first block wakes up the run loop
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // first block will hold our VRF registration
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // second block will be the first mined Stacks block
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // Let's setup the follower now.
        follower_node_tx
            .send(Signal::BootstrapNodeReady)
            .expect("Unable to send signal");

        match bootstrap_node_rx.recv() {
            Ok(Signal::ReplicatingAttachmentsStartTest1) => {
                println!("Follower node is ready...");
            }
            _ => panic!("Bootstrap node could nod boot. Aborting test."),
        };

        // Let's publish a (1) namespace-preorder, (2) namespace-reveal and (3) name-import in this mempool

        // (define-public (namespace-preorder (hashed-salted-namespace (buff 20))
        //                            (stx-to-burn uint))
        let namespace = "passport";
        let salt = "some-salt";
        let salted_namespace = format!("{namespace}{salt}");
        let hashed_namespace = Hash160::from_data(salted_namespace.as_bytes());
        let tx_1 = make_contract_call(
            &user_1,
            0,
            260,
            conf_bootstrap_node.burnchain.chain_id,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "namespace-preorder",
            &[
                Value::buff_from(hashed_namespace.to_bytes().to_vec()).unwrap(),
                Value::UInt(1000000000),
            ],
        );

        let path = format!("{http_origin}/v2/transactions");
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tx_1.clone())
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &tx_1[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // (define-public (namespace-reveal (namespace (buff 20))
        //                                  (namespace-salt (buff 20))
        //                                  (p-func-base uint)
        //                                  (p-func-coeff uint)
        //                                  (p-func-b1 uint)
        //                                  (p-func-b2 uint)
        //                                  (p-func-b3 uint)
        //                                  (p-func-b4 uint)
        //                                  (p-func-b5 uint)
        //                                  (p-func-b6 uint)
        //                                  (p-func-b7 uint)
        //                                  (p-func-b8 uint)
        //                                  (p-func-b9 uint)
        //                                  (p-func-b10 uint)
        //                                  (p-func-b11 uint)
        //                                  (p-func-b12 uint)
        //                                  (p-func-b13 uint)
        //                                  (p-func-b14 uint)
        //                                  (p-func-b15 uint)
        //                                  (p-func-b16 uint)
        //                                  (p-func-non-alpha-discount uint)
        //                                  (p-func-no-vowel-discount uint)
        //                                  (lifetime uint)
        //                                  (namespace-import principal))
        let tx_2 = make_contract_call(
            &user_1,
            1,
            1000,
            conf_bootstrap_node.burnchain.chain_id,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "namespace-reveal",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1000),
                Value::Principal(initial_balance_user_1.address.clone()),
            ],
        );

        let path = format!("{http_origin}/v2/transactions");
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tx_2.clone())
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &tx_2[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // (define-public (name-import (namespace (buff 20))
        //                             (name (buff 48))
        //                             (zonefile-hash (buff 20)))
        let zonefile_hex = "facade00";
        let hashed_zonefile = Hash160::from_data(&hex_bytes(zonefile_hex).unwrap());
        let tx_3 = make_contract_call(
            &user_1,
            2,
            500,
            conf_bootstrap_node.burnchain.chain_id,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "name-import",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from("johndoe".as_bytes().to_vec()).unwrap(),
                Value::Principal(to_addr(&user_1).into()),
                Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
            ],
        );

        let body = {
            let content = PostTransactionRequestBody {
                tx: bytes_to_hex(&tx_3),
                attachment: Some(zonefile_hex.to_string()),
            };
            serde_json::to_vec(&json!(content)).unwrap()
        };

        let path = format!("{http_origin}/v2/transactions");
        let res = client
            .post(&path)
            .header("Content-Type", "application/json")
            .body(body)
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if !res.status().is_success() {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // From there, let's mine these transaction, and build more blocks.
        let mut sort_height = channel.get_sortitions_processed();
        let few_blocks = sort_height + 10;

        while sort_height < few_blocks {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {sort_height}");
        }

        // Then check that the follower is correctly replicating the attachment
        follower_node_tx
            .send(Signal::ReplicatingAttachmentsCheckTest1(sort_height))
            .expect("Unable to send signal");

        match bootstrap_node_rx.recv() {
            Ok(Signal::ReplicatingAttachmentsStartTest2) => {
                println!("Follower node is ready...");
            }
            _ => panic!("Bootstrap node could nod boot. Aborting test."),
        };

        // From there, let's mine these transaction, and build more blocks.
        let mut sort_height = channel.get_sortitions_processed();
        let few_blocks = sort_height + 10;

        while sort_height < few_blocks {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {sort_height}");
        }

        // Poll GET v2/attachments/<attachment-hash>
        for i in 1..10 {
            let mut attachments_did_sync = false;
            let mut timeout = 60;
            while !attachments_did_sync {
                let zonefile_hex = hex_bytes(&format!("facade0{i}")).unwrap();
                let hashed_zonefile = Hash160::from_data(&zonefile_hex);
                let path = format!("{http_origin}/v2/attachments/{}", hashed_zonefile.to_hex());
                let res = client
                    .get(&path)
                    .header("Content-Type", "application/json")
                    .send()
                    .unwrap();
                eprintln!("{res:#?}");
                if res.status().is_success() {
                    let attachment_response: GetAttachmentResponse = res.json().unwrap();
                    assert_eq!(attachment_response.attachment.content, zonefile_hex);
                    attachments_did_sync = true;
                } else {
                    timeout -= 1;
                    if timeout == 0 {
                        panic!("Failed syncing 9 attachments between 2 neon runloops within 60s (failed at {}) - Something is wrong", &to_hex(&zonefile_hex));
                    }
                    eprintln!("Attachment {} not sync'd yet", bytes_to_hex(&zonefile_hex));
                    thread::sleep(Duration::from_millis(1000));
                }
            }
        }

        // Then check that the follower is correctly replicating the attachment
        follower_node_tx
            .send(Signal::ReplicatingAttachmentsCheckTest2(sort_height))
            .expect("Unable to send signal");

        channel.stop_chains_coordinator();
    });

    // Start the attached observer
    test_observer::spawn();

    // The bootstrap node mined a few blocks and is ready, let's setup this node.
    match follower_node_rx.recv() {
        Ok(Signal::BootstrapNodeReady) => {
            println!("Booting follower node...");
        }
        _ => panic!("Bootstrap node could nod boot. Aborting test."),
    };

    let burnchain_config = Burnchain::regtest(&conf_follower_node.get_burn_db_path());
    let chain_id = conf_follower_node.burnchain.chain_id;
    let http_origin = format!("http://{}", &conf_follower_node.node.rpc_bind);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_follower_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // Follower node is ready, the bootstrap node will now handover
    bootstrap_node_tx
        .send(Signal::ReplicatingAttachmentsStartTest1)
        .expect("Unable to send signal");

    // The bootstrap node published and mined a transaction that includes an attachment.
    // Lets observe the attachments replication kicking in.
    let target_height = match follower_node_rx.recv() {
        Ok(Signal::ReplicatingAttachmentsCheckTest1(target_height)) => target_height,
        _ => panic!("Bootstrap node could nod boot. Aborting test."),
    };

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < target_height {
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
    }

    // Now wait for the node to sync the attachment
    let mut attachments_did_sync = false;
    let mut timeout = 60;
    while !attachments_did_sync {
        let zonefile_hex = "facade00";
        let hashed_zonefile = Hash160::from_data(&hex_bytes(zonefile_hex).unwrap());
        let path = format!("{http_origin}/v2/attachments/{}", hashed_zonefile.to_hex());
        let res = client
            .get(&path)
            .header("Content-Type", "application/json")
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if res.status().is_success() {
            eprintln!("Success syncing attachment - {}", res.text().unwrap());
            attachments_did_sync = true;
        } else {
            timeout -= 1;
            if timeout == 0 {
                panic!("Failed syncing 1 attachments between 2 neon runloops within 60s - Something is wrong");
            }
            eprintln!("Attachment {zonefile_hex} not sync'd yet");
            thread::sleep(Duration::from_millis(1000));
        }
    }

    // Test 2: 9 transactions are posted to the follower.
    // We want to make sure that the miner is able to
    // 1) mine these transactions
    // 2) retrieve the attachments staged on the follower node.
    // 3) ensure that the follower is also instantiating the attachments after
    // executing the transactions, once mined.
    let namespace = "passport";
    for i in 1..10 {
        let user = StacksPrivateKey::random();
        let zonefile_hex = format!("facade0{i}");
        let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());
        let name = format!("johndoe{i}");
        let tx = make_contract_call(
            &user_1,
            2 + i,
            500,
            chain_id,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "name-import",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                Value::Principal(to_addr(&user).into()),
                Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
            ],
        );

        let body = {
            let content = PostTransactionRequestBody {
                tx: bytes_to_hex(&tx),
                attachment: Some(zonefile_hex.to_string()),
            };
            serde_json::to_vec(&json!(content)).unwrap()
        };

        let path = format!("{http_origin}/v2/transactions");
        let res = client
            .post(&path)
            .header("Content-Type", "application/json")
            .body(body)
            .send()
            .unwrap();
        eprintln!("{res:#?}");
        if !res.status().is_success() {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }
    }

    bootstrap_node_tx
        .send(Signal::ReplicatingAttachmentsStartTest2)
        .expect("Unable to send signal");

    let target_height = match follower_node_rx.recv() {
        Ok(Signal::ReplicatingAttachmentsCheckTest2(target_height)) => target_height,
        _ => panic!("Bootstrap node could not boot. Aborting test."),
    };

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < target_height {
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
    }

    // Poll GET v2/attachments/<attachment-hash>
    for i in 1..10 {
        let mut attachments_did_sync = false;
        let mut timeout = 60;
        while !attachments_did_sync {
            let zonefile_hex = hex_bytes(&format!("facade0{i}")).unwrap();
            let hashed_zonefile = Hash160::from_data(&zonefile_hex);
            let path = format!("{http_origin}/v2/attachments/{}", hashed_zonefile.to_hex());
            let res = client
                .get(&path)
                .header("Content-Type", "application/json")
                .send()
                .unwrap();
            eprintln!("{res:#?}");
            if res.status().is_success() {
                let attachment_response: GetAttachmentResponse = res.json().unwrap();
                assert_eq!(attachment_response.attachment.content, zonefile_hex);
                attachments_did_sync = true;
            } else {
                timeout -= 1;
                if timeout == 0 {
                    panic!("Failed syncing 9 attachments between 2 neon runloops within 60s (failed at {}) - Something is wrong", &to_hex(&zonefile_hex));
                }
                eprintln!("Attachment {} not sync'd yet", bytes_to_hex(&zonefile_hex));
                thread::sleep(Duration::from_millis(1000));
            }
        }
    }

    // Ensure that we the attached sidecar was able to receive a total of 10 attachments
    // This last assertion is flacky for some reason, it does not worth bullying the CI or disabling this whole test
    // We're using an inequality as a best effort, to make sure that **some** attachments were received.
    assert!(!test_observer::get_attachments().is_empty());
    test_observer::clear();
    channel.stop_chains_coordinator();

    bootstrap_node_thread.join().unwrap();
}

#[test]
#[ignore]
fn antientropy_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let user_1 = StacksPrivateKey::random();
    let initial_balance_user_1 = InitialBalance {
        address: to_addr(&user_1).into(),
        amount: 1_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS),
    };

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    let bootstrap_node_public_key = {
        let keychain = Keychain::default(conf_bootstrap_node.node.seed.clone());
        let mut pk = keychain.generate_op_signer().get_public_key();
        pk.set_compressed(true);
        pk.to_hex()
    };
    conf_bootstrap_node
        .initial_balances
        .push(initial_balance_user_1.clone());
    conf_bootstrap_node.connection_options.antientropy_retry = 10; // move this along -- do anti-entropy protocol once every 10 seconds
    conf_bootstrap_node.connection_options.antientropy_public = true; // always push blocks, even if we're not NAT'ed
    conf_bootstrap_node.connection_options.max_block_push = 1000;
    conf_bootstrap_node.connection_options.max_microblock_push = 1000;

    conf_bootstrap_node.node.mine_microblocks = true;
    conf_bootstrap_node.miner.microblock_attempt_time_ms = 2_000;
    conf_bootstrap_node.node.wait_time_for_microblocks = 0;
    conf_bootstrap_node.node.microblock_frequency = 0;
    conf_bootstrap_node.miner.first_attempt_time_ms = 1_000_000;
    conf_bootstrap_node.miner.subsequent_attempt_time_ms = 1_000_000;
    conf_bootstrap_node.burnchain.max_rbf = 1000000;
    conf_bootstrap_node.node.wait_time_for_blocks = 1_000;

    conf_bootstrap_node.node.always_use_affirmation_maps = false;

    // Prepare the config of the follower node
    let (mut conf_follower_node, _) = neon_integration_test_conf();
    let bootstrap_node_url = format!(
        "{bootstrap_node_public_key}@{}",
        conf_bootstrap_node.node.p2p_bind
    );
    conf_follower_node.connection_options.disable_block_download = true;
    conf_follower_node.node.set_bootstrap_nodes(
        bootstrap_node_url,
        conf_follower_node.burnchain.chain_id,
        conf_follower_node.burnchain.peer_version,
    );
    conf_follower_node.node.miner = false;
    conf_follower_node
        .initial_balances
        .push(initial_balance_user_1);
    conf_follower_node
        .events_observers
        .insert(EventObserverConfig {
            endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
            events_keys: vec![EventKeyType::AnyEvent],
            timeout_ms: 1000,
            lossy: false,
        });

    conf_follower_node.node.mine_microblocks = true;
    conf_follower_node.miner.microblock_attempt_time_ms = 2_000;
    conf_follower_node.node.wait_time_for_microblocks = 0;
    conf_follower_node.node.microblock_frequency = 0;
    conf_follower_node.miner.first_attempt_time_ms = 1_000_000;
    conf_follower_node.miner.subsequent_attempt_time_ms = 1_000_000;
    conf_follower_node.burnchain.max_rbf = 1000000;
    conf_follower_node.node.wait_time_for_blocks = 1_000;

    conf_follower_node.node.always_use_affirmation_maps = false;

    // Our 2 nodes will share the bitcoind node
    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let (bootstrap_node_tx, bootstrap_node_rx) = mpsc::channel();
    let (follower_node_tx, follower_node_rx) = mpsc::channel();

    let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());
    let target_height = 3 + (3 * burnchain_config.pox_constants.reward_cycle_length);

    let bootstrap_node_thread = thread::spawn(move || {
        let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
            conf_bootstrap_node.clone(),
            None,
            Some(burnchain_config.clone()),
            None,
        );

        btc_regtest_controller.bootstrap_chain(201);

        eprintln!("Chain bootstrapped...");

        let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
        let blocks_processed = run_loop.get_blocks_processed_arc();
        let channel = run_loop.get_coordinator_channel().unwrap();

        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

        // give the run loop some time to start up!
        wait_for_runloop(&blocks_processed);

        // first block wakes up the run loop
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // first block will hold our VRF registration
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        for i in 0..(target_height - 3) {
            eprintln!("Mine block {i}");
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            let sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {sort_height}");
        }

        // Let's setup the follower now.
        follower_node_tx
            .send(Signal::BootstrapNodeReady)
            .expect("Unable to send signal");

        eprintln!("Bootstrap node informed follower that it's ready; waiting for acknowledgement");

        // wait for bootstrap node to terminate
        match bootstrap_node_rx.recv() {
            Ok(Signal::FollowerNodeReady) => {
                println!("Follower has finished");
            }
            Ok(x) => {
                panic!("Follower gave a bad signal: {x:?}");
            }
            Err(e) => {
                panic!("Failed to recv: {e:?}");
            }
        };

        channel.stop_chains_coordinator();
    });

    // Start the attached observer
    test_observer::spawn();

    // The bootstrap node mined a few blocks and is ready, let's setup this node.
    match follower_node_rx.recv() {
        Ok(Signal::BootstrapNodeReady) => {
            println!("Booting follower node...");
        }
        _ => panic!("Bootstrap node could not boot. Aborting test."),
    };

    let burnchain_config = Burnchain::regtest(&conf_follower_node.get_burn_db_path());
    let http_origin = format!("http://{}", &conf_follower_node.node.rpc_bind);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_follower_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    let thread_burnchain_config = burnchain_config.clone();
    thread::spawn(move || run_loop.start(Some(thread_burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < (target_height + 200) as u64 {
        eprintln!(
            "Follower sortition is {sort_height}, target is {}",
            target_height + 200
        );
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
        sleep_ms(1000);
    }

    eprintln!("Follower booted up; waiting for blocks");

    // wait for block height to reach target
    let mut tip_height = get_chain_tip_height(&http_origin);
    eprintln!(
        "Follower Stacks tip height is {tip_height}, wait until {tip_height} >= {target_height} - 3"
    );

    let btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf_follower_node.clone(),
        None,
        Some(burnchain_config),
        None,
    );

    let mut burnchain_deadline = get_epoch_time_secs() + 60;
    while tip_height < (target_height - 3) as u64 {
        sleep_ms(1000);
        tip_height = get_chain_tip_height(&http_origin);

        eprintln!("Follower Stacks tip height is {tip_height}");

        if burnchain_deadline < get_epoch_time_secs() {
            burnchain_deadline = get_epoch_time_secs() + 60;
            btc_regtest_controller.build_next_block(1);
        }
    }

    bootstrap_node_tx
        .send(Signal::FollowerNodeReady)
        .expect("Unable to send signal");
    bootstrap_node_thread.join().unwrap();

    eprintln!("Follower node finished");

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[allow(clippy::too_many_arguments)]
fn wait_for_mined(
    btc_regtest_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
    http_origin: &str,
    users: &[StacksPrivateKey],
    account_before_nonces: &[u64],
    batch_size: usize,
    batches: usize,
    index_block_hashes: &mut Vec<StacksBlockId>,
) {
    let mut all_mined_vec = vec![false; batches * batch_size];
    let mut account_after_nonces = vec![0; batches * batch_size];
    let mut all_mined = false;
    for _k in 0..10 {
        next_block_and_wait(btc_regtest_controller, blocks_processed);
        sleep_ms(10_000);

        let (ch, bhh) = get_chain_tip(http_origin);
        let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);

        if let Some(last_ibh) = index_block_hashes.last() {
            if *last_ibh != ibh {
                index_block_hashes.push(ibh);
                eprintln!("Tip is now {ibh}");
            }
        }

        for j in 0..batches * batch_size {
            let account_after = get_account(http_origin, &to_addr(&users[j]));
            let account_after_nonce = account_after.nonce;
            account_after_nonces[j] = account_after_nonce;

            if account_before_nonces[j] < account_after_nonce {
                all_mined_vec[j] = true;
            }
        }

        all_mined = all_mined_vec.iter().all(|elem| *elem);
        if all_mined {
            break;
        }
    }
    if !all_mined {
        panic!(
            "Failed to mine all transactions: nonces = {account_after_nonces:?}, expected {account_before_nonces:?} + {batch_size}"
        );
    }
}

#[test]
#[ignore]
fn atlas_stress_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut initial_balances = vec![];
    let mut users = vec![];

    let batches = 5;
    let batch_size = 20;

    for _i in 0..(2 * batches * batch_size + 1) {
        let user = StacksPrivateKey::random();
        let initial_balance_user = InitialBalance {
            address: to_addr(&user).into(),
            amount: 1_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS),
        };
        users.push(user);
        initial_balances.push(initial_balance_user);
    }

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    conf_bootstrap_node
        .initial_balances
        .append(&mut initial_balances.clone());

    conf_bootstrap_node.miner.first_attempt_time_ms = u64::MAX;
    conf_bootstrap_node.miner.subsequent_attempt_time_ms = u64::MAX;

    conf_bootstrap_node.node.mine_microblocks = true;
    conf_bootstrap_node.miner.microblock_attempt_time_ms = 2_000;
    conf_bootstrap_node.node.wait_time_for_microblocks = 0;
    conf_bootstrap_node.node.microblock_frequency = 0;
    conf_bootstrap_node.miner.first_attempt_time_ms = 1_000_000;
    conf_bootstrap_node.miner.subsequent_attempt_time_ms = 2_000_000;
    conf_bootstrap_node.burnchain.max_rbf = 1000000;
    conf_bootstrap_node.node.wait_time_for_blocks = 1_000;

    conf_bootstrap_node.node.always_use_affirmation_maps = false;

    let user_1 = users.pop().unwrap();
    let initial_balance_user_1 = initial_balances.pop().unwrap();

    // Start the attached observer
    test_observer::spawn();

    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf_bootstrap_node.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf_bootstrap_node.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut index_block_hashes = vec![];

    // Let's publish a (1) namespace-preorder, (2) namespace-reveal and (3) name-import in this mempool

    // (define-public (namespace-preorder (hashed-salted-namespace (buff 20))
    //                            (stx-to-burn uint))
    let namespace = "passport";
    let salt = "some-salt";
    let salted_namespace = format!("{namespace}{salt}");
    let hashed_namespace = Hash160::from_data(salted_namespace.as_bytes());
    let tx_1 = make_contract_call(
        &user_1,
        0,
        1000,
        conf_bootstrap_node.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-preorder",
        &[
            Value::buff_from(hashed_namespace.to_bytes().to_vec()).unwrap(),
            Value::UInt(1000000000),
        ],
    );

    let path = format!("{http_origin}/v2/transactions");
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_1.clone())
        .send()
        .unwrap();
    eprintln!("{res:#?}");
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx_1[..])
                .unwrap()
                .txid()
                .to_string()
        );
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    // (define-public (namespace-reveal (namespace (buff 20))
    //                                  (namespace-salt (buff 20))
    //                                  (p-func-base uint)
    //                                  (p-func-coeff uint)
    //                                  (p-func-b1 uint)
    //                                  (p-func-b2 uint)
    //                                  (p-func-b3 uint)
    //                                  (p-func-b4 uint)
    //                                  (p-func-b5 uint)
    //                                  (p-func-b6 uint)
    //                                  (p-func-b7 uint)
    //                                  (p-func-b8 uint)
    //                                  (p-func-b9 uint)
    //                                  (p-func-b10 uint)
    //                                  (p-func-b11 uint)
    //                                  (p-func-b12 uint)
    //                                  (p-func-b13 uint)
    //                                  (p-func-b14 uint)
    //                                  (p-func-b15 uint)
    //                                  (p-func-b16 uint)
    //                                  (p-func-non-alpha-discount uint)
    //                                  (p-func-no-vowel-discount uint)
    //                                  (lifetime uint)
    //                                  (namespace-import principal))
    let tx_2 = make_contract_call(
        &user_1,
        1,
        1000,
        conf_bootstrap_node.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-reveal",
        &[
            Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
            Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1000),
            Value::Principal(initial_balance_user_1.address),
        ],
    );

    let path = format!("{http_origin}/v2/transactions");
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_2.clone())
        .send()
        .unwrap();
    eprintln!("{:#?}", res);
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx_2[..])
                .unwrap()
                .txid()
                .to_string()
        );
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    let mut mined_namespace_reveal = false;
    for _j in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sleep_ms(10_000);

        let account_after = get_account(&http_origin, &to_addr(&user_1));
        if account_after.nonce == 2 {
            mined_namespace_reveal = true;
            break;
        }
    }
    assert!(
        mined_namespace_reveal,
        "Did not mine namespace preorder or reveal"
    );

    // make a _ton_ of name-imports
    for i in 0..batches {
        let account_before = get_account(&http_origin, &to_addr(&user_1));

        for j in 0..batch_size {
            // (define-public (name-import (namespace (buff 20))
            //                             (name (buff 48))
            //                             (zonefile-hash (buff 20)))
            let zonefile_hex = format!("facade00{:04x}{:04x}{:04x}", batch_size * i + j, i, j);
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            let tx_3 = make_contract_call(
                &user_1,
                2 + (batch_size * i + j) as u64,
                1000,
                conf_bootstrap_node.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-import",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(format!("johndoe{}", i * batch_size + j).as_bytes().to_vec())
                        .unwrap(),
                    Value::Principal(to_addr(&users[i * batch_size + j]).into()),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_3),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{http_origin}/v2/transactions");
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{res:#?}");
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        // wait for them all to be mined
        let mut all_mined = false;
        let account_after_nonce = 0;
        for _j in 0..10 {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sleep_ms(10_000);

            let (ch, bhh) = get_chain_tip(&http_origin);
            let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);
            index_block_hashes.push(ibh);

            let account_after = get_account(&http_origin, &to_addr(&user_1));
            let account_after_nonce = account_after.nonce;
            if account_before.nonce + (batch_size as u64) <= account_after_nonce {
                all_mined = true;
                break;
            }
        }
        assert!(
            all_mined,
            "Failed to mine all transactions: nonce = {account_after_nonce}, expected {}",
            account_before.nonce + (batch_size as u64)
        );
    }

    // launch namespace
    // (define-public (namespace-ready (namespace (buff 20)))
    let namespace = "passport";
    let tx_4 = make_contract_call(
        &user_1,
        2 + (batch_size as u64) * (batches as u64),
        1000,
        conf_bootstrap_node.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-ready",
        &[Value::buff_from(namespace.as_bytes().to_vec()).unwrap()],
    );

    let path = format!("{http_origin}/v2/transactions");
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_4)
        .send()
        .unwrap();
    eprintln!("{res:#?}");
    if !res.status().is_success() {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    let mut mined_namespace_ready = false;
    for _j in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sleep_ms(10_000);

        let (ch, bhh) = get_chain_tip(&http_origin);
        let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);
        index_block_hashes.push(ibh);

        let account_after = get_account(&http_origin, &to_addr(&user_1));
        if account_after.nonce == 2 + (batch_size as u64) * (batches as u64) {
            mined_namespace_ready = true;
            break;
        }
    }
    assert!(mined_namespace_ready, "Did not mine namespace ready");

    // make a _ton_ of preorders
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let fqn = format!("janedoe{j}.passport");
            let fqn_bytes = fqn.as_bytes().to_vec();
            let salt = format!("{:04x}", j);
            let salt_bytes = salt.as_bytes().to_vec();
            let mut hash_data = fqn_bytes.clone();
            hash_data.append(&mut salt_bytes.clone());

            let salted_hash = Hash160::from_data(&hash_data);

            let tx_5 = make_contract_call(
                &users[batches * batch_size + j],
                0,
                1000,
                conf_bootstrap_node.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-preorder",
                &[
                    Value::buff_from(salted_hash.0.to_vec()).unwrap(),
                    Value::UInt(500),
                ],
            );

            let path = format!("{http_origin}/v2/transactions");
            let res = client
                .post(&path)
                .header("Content-Type", "application/octet-stream")
                .body(tx_5.clone())
                .send()
                .unwrap();

            eprintln!(
                "sent preorder for {}:\n{res:#?}",
                &to_addr(&users[batches * batch_size + j])
            );
            if !res.status().is_success() {
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of registers
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{j}");
            let salt = format!("{j:04x}");

            let zonefile_hex = format!("facade01{j:04x}");
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            let tx_6 = make_contract_call(
                &users[batches * batch_size + j],
                1,
                1000,
                conf_bootstrap_node.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-register",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_6),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{http_origin}/v2/transactions");
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{res:#?}");
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of updates
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{j}");
            let zonefile_hex = format!("facade02{j:04x}");
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            let tx_7 = make_contract_call(
                &users[batches * batch_size + j],
                2,
                1000,
                conf_bootstrap_node.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-update",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_7),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{http_origin}/v2/transactions");
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{res:#?}");
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of renewals
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{j}");
            let zonefile_hex = format!("facade03{j:04x}");
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            let tx_8 = make_contract_call(
                &users[batches * batch_size + j],
                3,
                1000,
                conf_bootstrap_node.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-renewal",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::UInt(500),
                    Value::none(),
                    Value::some(Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap())
                        .unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_8),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{http_origin}/v2/transactions");
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{res:#?}");
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // find all attachment indexes and make sure we can get them
    let mut attachment_indexes = HashMap::new();
    let mut attachment_hashes = HashMap::new();
    {
        let atlasdb_path = conf_bootstrap_node.get_atlas_db_file_path();
        let atlasdb = AtlasDB::connect(AtlasConfig::new(false), &atlasdb_path, false).unwrap();
        for ibh in index_block_hashes.iter() {
            let indexes = query_rows::<u64, _>(
                &atlasdb.conn,
                "SELECT attachment_index FROM attachment_instances WHERE index_block_hash = ?1",
                &[ibh],
            )
            .unwrap();
            if !indexes.is_empty() {
                attachment_indexes.insert(*ibh, indexes.clone());
            }

            for index in indexes.iter() {
                let mut hashes = query_row_columns::<Hash160, _>(
                    &atlasdb.conn,
                    "SELECT content_hash FROM attachment_instances WHERE index_block_hash = ?1 AND attachment_index = ?2",
                    params![ibh, u64_to_sql(*index).unwrap()],
                    "content_hash")
                .unwrap();
                if !hashes.is_empty() {
                    assert_eq!(hashes.len(), 1);
                    attachment_hashes.insert((*ibh, *index), hashes.pop());
                }
            }
        }
    }
    eprintln!("attachment_indexes = {attachment_indexes:?}");

    let max_request_time_ms = 100;

    for (ibh, attachments) in attachment_indexes.iter() {
        let l = attachments.len();
        for i in 0..(l / MAX_ATTACHMENT_INV_PAGES_PER_REQUEST + 1) {
            if i * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST >= l {
                break;
            }

            let attachments_batch = attachments[i * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST
                ..cmp::min((i + 1) * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST, l)]
                .to_vec();
            let path = format!(
                "{http_origin}/v2/attachments/inv?index_block_hash={ibh}&pages_indexes={}",
                attachments_batch
                    .iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(",")
            );

            let attempts = 10;
            let ts_begin = get_epoch_time_ms();
            for _ in 0..attempts {
                let res = client.get(&path).send().unwrap();
                assert!(
                    res.status().is_success(),
                    "Bad response for `{path}`: `{:?}`",
                    res.text().unwrap()
                );
                let attachment_inv_response: GetAttachmentsInvResponse = res.json().unwrap();
                eprintln!("attachment inv response for {path}: {attachment_inv_response:?}");
            }
            let ts_end = get_epoch_time_ms();
            let total_time = ts_end.saturating_sub(ts_begin);
            eprintln!("Requested {path} {attempts} times in {total_time}ms");

            // requests should take no more than max_request_time_ms
            assert!(
                total_time < attempts * max_request_time_ms,
                "Atlas inventory request is too slow: {total_time} >= {attempts} * {max_request_time_ms}"
            );
        }

        for attachment in attachments.iter().take(l) {
            if *attachment == 0 {
                continue;
            }
            let content_hash = attachment_hashes
                .get(&(*ibh, *attachment))
                .cloned()
                .unwrap()
                .unwrap();

            let path = format!("{http_origin}/v2/attachments/{content_hash}");

            let attempts = 10;
            let ts_begin = get_epoch_time_ms();
            for _ in 0..attempts {
                let res = client.get(&path).send().unwrap();
                assert!(
                    res.status().is_success(),
                    "Bad response for `{path}`: `{:?}`",
                    res.text().unwrap()
                );
                let attachment_response: GetAttachmentResponse = res.json().unwrap();
                eprintln!("attachment response for {path}: {attachment_response:?}");
            }
            let ts_end = get_epoch_time_ms();
            let total_time = ts_end.saturating_sub(ts_begin);
            eprintln!("Requested {path} {attempts} times in {total_time}ms");

            // requests should take no more than max_request_time_ms
            assert!(
                total_time < attempts * max_request_time_ms,
                "Atlas chunk request is too slow: {total_time} >= {attempts} * {max_request_time_ms}"
            );
        }
    }

    test_observer::clear();
}

/// Run a fixed contract 20 times. Linearly increase the amount paid each time. The cost of the
/// contract should stay the same, and the fee rate paid should monotonically grow. The value
/// should grow faster for lower values of `window_size`, because a bigger window slows down the
/// growth.
fn fuzzed_median_fee_rate_estimation_test(window_size: u64, expected_final_value: f64) {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let max_contract_src = r#"
;; define counter variable
(define-data-var counter int 0)

;; increment method
(define-public (increment)
  (begin
    (var-set counter (+ (var-get counter) 1))
    (ok (var-get counter))))

  (define-public (increment-many)
    (begin
      (unwrap! (increment) (err u1))
      (unwrap! (increment) (err u1))
      (unwrap! (increment) (err u1))
      (unwrap! (increment) (err u1))
      (ok (var-get counter))))
    "#;

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);

    let (mut conf, _) = neon_integration_test_conf();

    // Set this estimator as special.
    conf.estimation.fee_estimator = Some(FeeEstimatorName::FuzzedWeightedMedianFeeRate);
    // Use randomness of 0 to keep test constant. Randomness is tested in unit tests.
    conf.estimation.fee_rate_fuzzer_fraction = 0f64;
    conf.estimation.fee_rate_window_size = window_size;

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.into(),
        amount: 10000000000,
    });
    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(200);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    wait_for_runloop(&blocks_processed);
    run_until_burnchain_height(&mut btc_regtest_controller, &blocks_processed, 210, &conf);

    submit_tx(
        &http_origin,
        &make_contract_publish(
            &spender_sk,
            0,
            110000,
            conf.burnchain.chain_id,
            "increment-contract",
            max_contract_src,
        ),
    );
    run_until_burnchain_height(&mut btc_regtest_controller, &blocks_processed, 212, &conf);

    // Loop 20 times. Each time, execute the same transaction, but increase the amount *paid*.
    // This will exercise the window size.
    let mut response_estimated_costs = vec![];
    let mut response_top_fee_rates = vec![];
    for i in 1..21 {
        submit_tx(
            &http_origin,
            &make_contract_call(
                &spender_sk,
                i,          // nonce
                i * 100000, // payment
                conf.burnchain.chain_id,
                &spender_addr,
                "increment-contract",
                "increment-many",
                &[],
            ),
        );
        run_until_burnchain_height(
            &mut btc_regtest_controller,
            &blocks_processed,
            212 + 2 * i,
            &conf,
        );

        {
            // Read from the fee estimation endpoin.
            let path = format!("{http_origin}/v2/fees/transaction");

            let tx_payload = TransactionPayload::ContractCall(TransactionContractCall {
                address: spender_addr,
                contract_name: ContractName::from("increment-contract"),
                function_name: ClarityName::from("increment-many"),
                function_args: vec![],
            });

            let payload_data = tx_payload.serialize_to_vec();
            let payload_hex = format!("0x{}", to_hex(&payload_data));

            let body = json!({ "transaction_payload": payload_hex.clone() });

            let client = reqwest::blocking::Client::new();
            let fee_rate_result = client
                .post(&path)
                .json(&body)
                .send()
                .expect("Should be able to post")
                .json::<RPCFeeEstimateResponse>()
                .expect("Failed to parse result into JSON");

            response_estimated_costs.push(fee_rate_result.estimated_cost_scalar);
            response_top_fee_rates.push(fee_rate_result.estimations.last().unwrap().fee_rate);
        }
    }

    // Wait two extra blocks to be sure.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(response_estimated_costs.len(), response_top_fee_rates.len());

    // Check that:
    // 1) The cost is always the same.
    // 2) Fee rate grows monotonically.
    for i in 1..response_estimated_costs.len() {
        let curr_cost = response_estimated_costs[i];
        let last_cost = response_estimated_costs[i - 1];
        assert_eq!(curr_cost, last_cost);

        let curr_rate = response_top_fee_rates[i];
        let last_rate = response_top_fee_rates[i - 1];
        assert!(curr_rate >= last_rate);
    }

    // Check the final value is near input parameter.
    assert!(is_close_f64(
        *response_top_fee_rates.last().unwrap(),
        expected_final_value
    ));

    channel.stop_chains_coordinator();
}

/// Test the FuzzedWeightedMedianFeeRate with window size 5 and randomness 0. We increase the
/// amount paid linearly each time. This estimate should grow *faster* than with window size 10.
#[test]
#[ignore]
fn fuzzed_median_fee_rate_estimation_test_window5() {
    fuzzed_median_fee_rate_estimation_test(5, 202680.0992)
}

/// Test the FuzzedWeightedMedianFeeRate with window size 10 and randomness 0. We increase the
/// amount paid linearly each time. This estimate should grow *slower* than with window size 5.
#[test]
#[ignore]
fn fuzzed_median_fee_rate_estimation_test_window10() {
    fuzzed_median_fee_rate_estimation_test(10, 90080.5496)
}

#[test]
#[ignore]
fn use_latest_tip_integration_test() {
    // The purpose of this test is to check if setting the query parameter `tip` to `latest` is working
    // as expected. Multiple endpoints accept this parameter, and in this test, we are using the
    // GetContractSrc method to test it.
    //
    // The following scenarios are tested here:
    // - The caller does not specify the tip paramater, and the canonical chain tip is used regardless of the
    //    state of the unconfirmed microblock stream.
    // - The caller passes tip=latest with an existing unconfirmed microblock stream, and
    //   Clarity state from the unconfirmed microblock stream is successfully loaded.
    // - The caller passes tip=latest with an empty unconfirmed microblock stream, and
    //   Clarity state from the canonical chain tip is successfully loaded (i.e. you don't
    //   get a 404 even though the unconfirmed chain tip points to a nonexistent MARF trie).
    //
    // Note: In this test, we are manually creating a microblock as well as reloading the unconfirmed
    // state of the chainstate, instead of relying on `next_block_and_wait` to generate
    // microblocks. We do this because the unconfirmed state is not automatically being initialized
    // on the node, so attempting to validate any transactions against the expected unconfirmed
    // state fails.
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stacks_addr = to_addr(&spender_sk);
    let spender_addr: PrincipalData = spender_stacks_addr.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 10_000;
    conf.node.microblock_frequency = 1_000;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Let's query our first spender.
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    // this call wakes up our node
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Open chainstate.
    // TODO (hack) instantiate the sortdb in the burnchain
    let _ = btc_regtest_controller.sortdb_mut();
    let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);
    let tip_hash =
        StacksBlockHeader::make_index_block_hash(&consensus_hash, &stacks_block.block_hash());
    let (mut chainstate, _) = StacksChainState::open(
        false,
        CHAIN_ID_TESTNET,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();

    // Initialize the unconfirmed state.
    chainstate
        .reload_unconfirmed_state(
            &btc_regtest_controller
                .sortdb_ref()
                .index_handle_at_block(&chainstate, &tip_hash)
                .unwrap(),
            tip_hash,
        )
        .unwrap();

    // Make microblock with two transactions.
    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let transfer_tx = make_stacks_transfer_mblock_only(
        &spender_sk,
        0,
        1000,
        conf.burnchain.chain_id,
        &recipient.into(),
        1000,
    );

    let caller_src = "
     (define-public (execute)
        (ok stx-liquid-supply))
     ";
    let publish_tx = make_contract_publish_microblock_only(
        &spender_sk,
        1,
        1000,
        conf.burnchain.chain_id,
        "caller",
        caller_src,
    );

    let tx_1 = StacksTransaction::consensus_deserialize(&mut &transfer_tx[..]).unwrap();
    let tx_2 = StacksTransaction::consensus_deserialize(&mut &publish_tx[..]).unwrap();
    let vec_tx = vec![tx_1, tx_2];
    let privk =
        find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024).unwrap();
    let iconn = btc_regtest_controller
        .sortdb_ref()
        .index_handle_at_block(&chainstate, &tip_hash)
        .unwrap();
    let mblock = make_microblock(
        &privk,
        &mut chainstate,
        &iconn,
        consensus_hash,
        stacks_block,
        vec_tx,
    );
    let mut mblock_bytes = vec![];
    mblock.consensus_serialize(&mut mblock_bytes).unwrap();

    let client = reqwest::blocking::Client::new();

    // Post the microblock
    let path = format!("{http_origin}/v2/microblocks");
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(mblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &mblock.block_hash()));

    // Wait for the microblock to be accepted
    sleep_ms(5_000);
    let path = format!("{http_origin}/v2/info");
    let mut iter_count = 0;
    loop {
        let tip_info = client
            .get(&path)
            .send()
            .unwrap()
            .json::<RPCPeerInfoData>()
            .unwrap();
        eprintln!("{:#?}", tip_info);
        if tip_info.unanchored_tip == Some(StacksBlockId([0; 32])) {
            iter_count += 1;
            assert!(
                iter_count < 10,
                "Hit retry count while waiting for net module to process pushed microblock"
            );
            sleep_ms(5_000);
            continue;
        } else {
            break;
        }
    }

    // Wait at least two p2p refreshes so it can produce the microblock.
    for i in 0..30 {
        info!(
            "wait {} more seconds for microblock miner to find our transaction...",
            30 - i
        );
        sleep_ms(1000);
    }

    // Check event observer for new microblock event (expect 1).
    let microblock_events = test_observer::get_microblocks();
    assert_eq!(microblock_events.len(), 1);

    // Don't set the tip parameter, and ask for the source of the contract we just defined in a microblock.
    // This should fail because the anchored tip would be unaware of this contract.
    let err_opt = get_contract_src(
        &http_origin,
        spender_stacks_addr,
        "caller".to_string(),
        false,
    );
    match err_opt {
        Ok(_) => {
            panic!(
                "Asking for the contract source off the anchored tip for a contract published \
            only in unconfirmed state should error."
            );
        }
        // Expect to get "NoSuchContract" because the function we are attempting to call is in a
        // contract that only exists on unconfirmed state (and we did not set tip).
        Err(err_str) => {
            assert!(err_str.contains("No contract source data found"));
        }
    }

    // Set tip=latest, and ask for the source of the contract defined in the microblock.
    // This should succeeed.
    assert!(get_contract_src(
        &http_origin,
        spender_stacks_addr,
        "caller".to_string(),
        true,
    )
    .is_ok());

    // Mine an anchored block because now we want to have no unconfirmed state.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Check that the underlying trie for the unconfirmed state does not exist.
    assert!(chainstate.unconfirmed_state.is_some());
    let unconfirmed_state = chainstate.unconfirmed_state.as_mut().unwrap();
    let trie_exists = match unconfirmed_state
        .clarity_inst
        .trie_exists_for_block(&unconfirmed_state.unconfirmed_chain_tip)
    {
        Ok(res) => res,
        Err(e) => {
            panic!("error when determining whether or not trie exists: {:?}", e);
        }
    };
    assert!(!trie_exists);

    // Set tip=latest, and ask for the source of the contract defined in the previous epoch.
    // The underlying MARF trie for the unconfirmed tip does not exist, so the transaction will be
    // validated against the confirmed chain tip instead of the unconfirmed tip. This should be valid.
    assert!(get_contract_src(
        &http_origin,
        spender_stacks_addr,
        "caller".to_string(),
        true,
    )
    .is_ok());
}

#[test]
#[ignore]
fn test_flash_block_skip_tenure() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, miner_account) = neon_integration_test_conf();
    conf.miner.microblock_attempt_time_ms = 5_000;
    conf.node.wait_time_for_microblocks = 0;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let missed_tenures = run_loop.get_missed_tenures_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // fault injection: force tenures to take too long
    std::env::set_var("STX_TEST_SLOW_TENURE", "11000");

    for i in 0..10 {
        // build one bitcoin block every 10 seconds
        eprintln!("Build bitcoin block +{i}");
        btc_regtest_controller.build_next_block(1);
        sleep_ms(10000);
    }

    // at least one tenure was skipped
    let num_skipped = missed_tenures.load(Ordering::SeqCst);
    eprintln!("Skipped {num_skipped} tenures");
    assert!(num_skipped > 1);

    // let's query the miner's account nonce:

    eprintln!("Miner account: {miner_account}");

    let account = get_account(&http_origin, &miner_account);
    eprintln!("account = {account:?}");
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 2);

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn test_chainwork_first_intervals() {
    let (conf, _) = neon_integration_test_conf();
    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(2016 * 2 - 1);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn test_chainwork_partial_interval() {
    let (conf, _) = neon_integration_test_conf();
    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(2016 - 1);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn test_problematic_txs_are_not_stored() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_sk_3 = StacksPrivateKey::from_hex(SK_3).unwrap();
    let spender_stacks_addr_1 = to_addr(&spender_sk_1);
    let spender_stacks_addr_2 = to_addr(&spender_sk_2);
    let spender_stacks_addr_3 = to_addr(&spender_sk_3);
    let spender_addr_1: PrincipalData = spender_stacks_addr_1.into();
    let spender_addr_2: PrincipalData = spender_stacks_addr_2.into();
    let spender_addr_3: PrincipalData = spender_stacks_addr_3.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_2,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_3,
        amount: 1_000_000_000_000,
    });

    // force mainnet limits in 2.05 for this test
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // take effect immediately
    conf.burnchain.ast_precheck_size_height = Some(0);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());

    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    // something at the limit of the expression depth (will get mined and processed)
    let edge_repeat_factor = AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) - 1;
    let tx_edge_body_start = "{ a : ".repeat(edge_repeat_factor as usize);
    let tx_edge_body_end = "} ".repeat(edge_repeat_factor as usize);
    let tx_edge_body = format!("{tx_edge_body_start}u1 {tx_edge_body_end}");

    let tx_edge = make_contract_publish(
        &spender_sk_1,
        0,
        (tx_edge_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-edge",
        &tx_edge_body,
    );
    let tx_edge_txid = StacksTransaction::consensus_deserialize(&mut &tx_edge[..])
        .unwrap()
        .txid();

    // something just over the limit of the expression depth
    let exceeds_repeat_factor = edge_repeat_factor + 1;
    let tx_exceeds_body_start = "{ a : ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body_end = "} ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body = format!("{tx_exceeds_body_start}u1 {tx_exceeds_body_end}");

    let tx_exceeds = make_contract_publish(
        &spender_sk_2,
        0,
        (tx_exceeds_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-exceeds",
        &tx_exceeds_body,
    );
    let tx_exceeds_txid = StacksTransaction::consensus_deserialize(&mut &tx_exceeds[..])
        .unwrap()
        .txid();

    // something stupidly high over the expression depth
    let high_repeat_factor = 128 * 1024;
    let tx_high_body_start = "{ a : ".repeat(high_repeat_factor as usize);
    let tx_high_body_end = "} ".repeat(high_repeat_factor as usize);
    let tx_high_body = format!("{tx_high_body_start}u1 {tx_high_body_end}");

    let tx_high = make_contract_publish(
        &spender_sk_3,
        0,
        (tx_high_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-high",
        &tx_high_body,
    );
    let tx_high_txid = StacksTransaction::consensus_deserialize(&mut &tx_high[..])
        .unwrap()
        .txid();

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    submit_tx(&http_origin, &tx_edge);
    submit_tx(&http_origin, &tx_exceeds);
    submit_tx(&http_origin, &tx_high);

    // only tx_edge should be in the mempool
    assert!(get_unconfirmed_tx(&http_origin, &tx_edge_txid).is_some());
    assert!(get_unconfirmed_tx(&http_origin, &tx_exceeds_txid).is_none());
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_none());

    channel.stop_chains_coordinator();
}

fn find_new_files(dirp: &str, prev_files: &HashSet<String>) -> (Vec<String>, HashSet<String>) {
    let dirpp = Path::new(dirp);
    debug!("readdir {dirp}");
    let cur_files = fs::read_dir(dirp).unwrap();
    let mut new_files = vec![];
    let mut cur_files_set = HashSet::new();
    for cur_file in cur_files.into_iter() {
        let cur_file = cur_file.unwrap();
        let cur_file_fullpath = dirpp.join(cur_file.path()).to_str().unwrap().to_string();
        test_debug!("file in {dirp}: {cur_file_fullpath}");
        cur_files_set.insert(cur_file_fullpath.clone());
        if prev_files.contains(&cur_file_fullpath) {
            test_debug!("already contains {cur_file_fullpath}");
            continue;
        }
        test_debug!("new file {cur_file_fullpath}");
        new_files.push(cur_file_fullpath);
    }
    debug!(
        "Checked {dirp} for new files; found {} (all: {})",
        new_files.len(),
        cur_files_set.len()
    );
    (new_files, cur_files_set)
}

fn spawn_follower_node(
    initial_conf: &Config,
) -> (
    Config,
    neon::RunLoopCounter,
    PoxSyncWatchdogComms,
    CoordinatorChannels,
) {
    let bootstrap_node_public_key = {
        let keychain = Keychain::default(initial_conf.node.seed.clone());
        let mut pk = keychain.generate_op_signer().get_public_key();
        pk.set_compressed(true);
        pk.to_hex()
    };

    let (mut conf, _) = neon_integration_test_conf();
    conf.node.set_bootstrap_nodes(
        format!(
            "{}@{}",
            &bootstrap_node_public_key, initial_conf.node.p2p_bind
        ),
        conf.burnchain.chain_id,
        conf.burnchain.peer_version,
    );

    test_observer::register_any(&mut conf);

    conf.initial_balances = initial_conf.initial_balances.clone();
    conf.burnchain.epochs = initial_conf.burnchain.epochs.clone();
    conf.burnchain.ast_precheck_size_height = initial_conf.burnchain.ast_precheck_size_height;

    conf.connection_options.inv_sync_interval = 3;

    conf.node.always_use_affirmation_maps = false;

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();
    let pox_sync = run_loop.get_pox_sync_comms();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    (conf, blocks_processed, pox_sync, channel)
}

// TODO: test in epoch 2.1 with parser_v2
#[test]
#[ignore]
fn test_problematic_blocks_are_not_mined() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let bad_blocks_dir = "/tmp/bad-blocks-test_problematic_blocks_are_not_mined";
    if fs::metadata(bad_blocks_dir).is_ok() {
        fs::remove_dir_all(bad_blocks_dir).unwrap();
    }
    fs::create_dir_all(bad_blocks_dir).unwrap();

    std::env::set_var("STACKS_BAD_BLOCKS_DIR", bad_blocks_dir);

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_sk_3 = StacksPrivateKey::from_hex(SK_3).unwrap();
    let spender_stacks_addr_1 = to_addr(&spender_sk_1);
    let spender_stacks_addr_2 = to_addr(&spender_sk_2);
    let spender_stacks_addr_3 = to_addr(&spender_sk_3);
    let spender_addr_1: PrincipalData = spender_stacks_addr_1.into();
    let spender_addr_2: PrincipalData = spender_stacks_addr_2.into();
    let spender_addr_3: PrincipalData = spender_stacks_addr_3.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_2,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_3,
        amount: 1_000_000_000_000,
    });

    // force mainnet limits in 2.05 for this test
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // AST precheck becomes default at burn height
    conf.burnchain.ast_precheck_size_height = Some(210);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    // something just over the limit of the expression depth
    let exceeds_repeat_factor = 32;
    let tx_exceeds_body_start = "{ a : ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body_end = "} ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body = format!("{tx_exceeds_body_start}u1 {tx_exceeds_body_end}");

    let tx_exceeds = make_contract_publish(
        &spender_sk_2,
        0,
        (tx_exceeds_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-exceeds",
        &tx_exceeds_body,
    );
    let tx_exceeds_txid = StacksTransaction::consensus_deserialize(&mut &tx_exceeds[..])
        .unwrap()
        .txid();

    // something stupidly high over the expression depth
    let high_repeat_factor = 3200;
    let tx_high_body_start = "{ a : ".repeat(high_repeat_factor as usize);
    let tx_high_body_end = "} ".repeat(high_repeat_factor as usize);
    let tx_high_body = format!("{tx_high_body_start}u1 {tx_high_body_end}");

    let tx_high = make_contract_publish(
        &spender_sk_3,
        0,
        (tx_high_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-high",
        &tx_high_body,
    );
    let tx_high_txid = StacksTransaction::consensus_deserialize(&mut &tx_high[..])
        .unwrap()
        .txid();

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    debug!("Submit problematic tx_exceeds transaction {tx_exceeds_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_exceeds);
    assert!(get_unconfirmed_tx(&http_origin, &tx_exceeds_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;
    }

    // all blocks were processed
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height == old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for blocks to be processed");

    // no blocks considered problematic
    assert!(all_new_files.is_empty());

    // one block contained tx_exceeds
    let blocks = test_observer::get_blocks();
    let mut found = false;
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_exceeds_txid {
                    found = true;
                    break;
                }
            }
        }
    }

    assert!(found);

    let (tip, cur_ast_rules) = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        (tip, cur_ast_rules)
    };

    assert_eq!(cur_ast_rules, ASTRules::Typical);

    // add another bad tx to the mempool
    debug!("Submit problematic tx_high transaction {tx_high_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_high);
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    btc_regtest_controller.build_next_block(1);

    // wait for runloop to advance
    wait_for(30, || {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let new_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(new_tip.block_height > tip.block_height)
    })
    .expect("Failed waiting for blocks to be processed");

    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // new rules took effect
    assert_eq!(cur_ast_rules, ASTRules::PrecheckSize);

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    eprintln!("old_tip_info = {old_tip_info:?}");

    // mine some blocks, and log problematic blocks
    for _i in 0..6 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;
    }

    // all blocks were processed
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height >= old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for blocks to be processed");

    // none were problematic
    assert!(all_new_files.is_empty());

    // recently-submitted problematic transactions are not in the mempool
    // (but old ones that were already mined, and thus never considered, could still be present)
    test_debug!("Problematic tx {tx_high_txid} should be dropped");
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_none());

    // no block contained the tx_high bad transaction, ever
    let blocks = test_observer::get_blocks();
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                assert!(parsed.txid() != tx_high_txid);
            }
        }
    }

    let new_tip_info = get_chain_info(&conf);

    eprintln!("\nBooting follower\n");

    // verify that a follower node that boots up with this node as a bootstrap peer will process
    // all of the blocks available, even if they are problematic, with the checks on.
    let (follower_conf, _, pox_sync_comms, follower_channel) = spawn_follower_node(&conf);

    eprintln!(
        "\nFollower booted on port {},{}\n",
        follower_conf.node.p2p_bind, follower_conf.node.rpc_bind
    );

    // Do not unwrap in case we were just slow
    let _ = wait_for(300, || {
        let follower_tip_info = get_chain_info(&follower_conf);
        eprintln!(
            "\nFollower is at burn block {} stacks block {}\n",
            follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
        );
        Ok(follower_tip_info.stacks_tip_height == new_tip_info.stacks_tip_height)
    });

    // make sure we aren't just slow -- wait for the follower to do a few download passes
    let num_download_passes = pox_sync_comms.get_download_passes();
    eprintln!(
        "\nFollower has performed {num_download_passes} download passes; wait for {}\n",
        num_download_passes + 5
    );

    wait_for(30, || {
        let download_passes = pox_sync_comms.get_download_passes();
        eprintln!(
            "\nFollower has performed {download_passes} download passes; wait for {}\n",
            num_download_passes + 5
        );
        Ok(download_passes >= num_download_passes + 5)
    })
    .expect("Failed waiting for follower to perform enough download passes");

    eprintln!(
        "\nFollower has performed {} download passes\n",
        pox_sync_comms.get_download_passes()
    );

    let follower_tip_info = get_chain_info(&follower_conf);
    eprintln!(
        "\nFollower is at burn block {} stacks block {}\n",
        follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
    );

    assert_eq!(
        follower_tip_info.stacks_tip_height,
        new_tip_info.stacks_tip_height
    );

    test_observer::clear();
    channel.stop_chains_coordinator();
    follower_channel.stop_chains_coordinator();
}

// TODO: test in epoch 2.1 with parser_v2
#[test]
#[ignore]
fn test_problematic_blocks_are_not_relayed_or_stored() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let bad_blocks_dir = "/tmp/bad-blocks-test_problematic_blocks_are_not_relayed_or_stored";
    if fs::metadata(bad_blocks_dir).is_ok() {
        fs::remove_dir_all(bad_blocks_dir).unwrap();
    }
    fs::create_dir_all(bad_blocks_dir).unwrap();

    std::env::set_var("STACKS_BAD_BLOCKS_DIR", bad_blocks_dir);

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_sk_3 = StacksPrivateKey::from_hex(SK_3).unwrap();
    let spender_stacks_addr_1 = to_addr(&spender_sk_1);
    let spender_stacks_addr_2 = to_addr(&spender_sk_2);
    let spender_stacks_addr_3 = to_addr(&spender_sk_3);
    let spender_addr_1: PrincipalData = spender_stacks_addr_1.into();
    let spender_addr_2: PrincipalData = spender_stacks_addr_2.into();
    let spender_addr_3: PrincipalData = spender_stacks_addr_3.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_2,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_3,
        amount: 1_000_000_000_000,
    });

    // force mainnet limits in 2.05 for this test
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // AST precheck becomes default at burn height
    conf.burnchain.ast_precheck_size_height = Some(210);

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    // something just over the limit of the expression depth
    let exceeds_repeat_factor = 32;
    let tx_exceeds_body_start = "{ a : ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body_end = "} ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body = format!("{tx_exceeds_body_start}u1 {tx_exceeds_body_end}");

    let tx_exceeds = make_contract_publish(
        &spender_sk_2,
        0,
        (tx_exceeds_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-exceeds",
        &tx_exceeds_body,
    );
    let tx_exceeds_txid = StacksTransaction::consensus_deserialize(&mut &tx_exceeds[..])
        .unwrap()
        .txid();

    let high_repeat_factor = 70;
    let tx_high_body_start = "{ a : ".repeat(high_repeat_factor as usize);
    let tx_high_body_end = "} ".repeat(high_repeat_factor as usize);
    let tx_high_body = format!("{tx_high_body_start}u1 {tx_high_body_end}");

    let tx_high = make_contract_publish(
        &spender_sk_3,
        0,
        (tx_high_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-high",
        &tx_high_body,
    );
    let tx_high_txid = StacksTransaction::consensus_deserialize(&mut &tx_high[..])
        .unwrap()
        .txid();

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    debug!("Submit problematic tx_exceeds transaction {tx_exceeds_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_exceeds);
    assert!(get_unconfirmed_tx(&http_origin, &tx_exceeds_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;
    }

    let tip_info = get_chain_info(&conf);

    // blocks were all processed
    assert_eq!(
        tip_info.stacks_tip_height,
        old_tip_info.stacks_tip_height + 5
    );
    // no blocks considered problematic
    assert!(all_new_files.is_empty());

    // one block contained tx_exceeds
    let blocks = test_observer::get_blocks();
    let mut found = false;
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_exceeds_txid {
                    found = true;
                    break;
                }
            }
        }
    }

    assert!(found);

    let (tip, cur_ast_rules) = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        (tip, cur_ast_rules)
    };

    assert_eq!(cur_ast_rules, ASTRules::Typical);

    btc_regtest_controller.build_next_block(1);

    // wait for runloop to advance
    loop {
        sleep_ms(1_000);
        let sortdb = btc_regtest_controller.sortdb_mut();
        let new_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        if new_tip.block_height > tip.block_height {
            break;
        }
    }
    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // new rules took effect
    assert_eq!(cur_ast_rules, ASTRules::PrecheckSize);

    // the follower we will soon boot up will start applying the new AST rules at this height.
    // Make it so the miner does *not* follow the rules
    {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let mut tx = sortdb.tx_begin().unwrap();
        SortitionDB::override_ast_rule_height(&mut tx, ASTRules::PrecheckSize, 10_000).unwrap();
        tx.commit().unwrap();
    }
    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // we reverted to the old rules (but the follower won't)
    assert_eq!(cur_ast_rules, ASTRules::Typical);

    // add another bad tx to the mempool.
    // because the miner is now non-conformant, it should mine this tx.
    debug!("Submit problematic tx_high transaction {tx_high_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_high);
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    eprintln!("old_tip_info = {old_tip_info:?}");

    // mine some blocks, and log problematic blocks
    for _i in 0..6 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;

        let cur_ast_rules = {
            let sortdb = btc_regtest_controller.sortdb_mut();
            let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
            let cur_ast_rules =
                SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
            cur_ast_rules
        };

        // we reverted to the old rules (but the follower won't)
        assert_eq!(cur_ast_rules, ASTRules::Typical);
    }

    let tip_info = get_chain_info(&conf);

    // at least one block was mined (hard to say how many due to the raciness between the burnchain
    // downloader and this thread).
    info!(
        "tip_info.stacks_tip_height = {}, old_tip_info.stacks_tip_height = {}",
        tip_info.stacks_tip_height, old_tip_info.stacks_tip_height
    );
    assert!(tip_info.stacks_tip_height > old_tip_info.stacks_tip_height);
    // one was problematic -- i.e. the one that included tx_high
    assert_eq!(all_new_files.len(), 1);

    // tx_high got mined by the miner
    let blocks = test_observer::get_blocks();
    let mut bad_block_height = None;
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_high_txid {
                    bad_block_height = Some(block.get("block_height").unwrap().as_u64().unwrap());
                }
            }
        }
    }
    assert!(bad_block_height.is_some());
    let bad_block_height = bad_block_height.unwrap();

    // follower should not process bad_block_height or higher
    let new_tip_info = get_chain_info(&conf);

    eprintln!("\nBooting follower\n");

    // verify that a follower node that boots up with this node as a bootstrap peer will process
    // all of the blocks available, even if they are problematic, with the checks on.
    let (follower_conf, _, pox_sync_comms, follower_channel) = spawn_follower_node(&conf);

    eprintln!(
        "\nFollower booted on port {},{}\n",
        follower_conf.node.p2p_bind, follower_conf.node.rpc_bind
    );

    let deadline = get_epoch_time_secs() + 300;
    while get_epoch_time_secs() < deadline {
        let follower_tip_info = get_chain_info(&follower_conf);
        if follower_tip_info.stacks_tip_height == new_tip_info.stacks_tip_height
            || follower_tip_info.stacks_tip_height + 1 == bad_block_height
        {
            break;
        }
        eprintln!(
            "\nFollower is at burn block {} stacks block {} (bad_block is {bad_block_height})\n",
            follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
        );
        sleep_ms(1000);
    }

    // make sure we aren't just slow -- wait for the follower to do a few download passes
    let num_download_passes = pox_sync_comms.get_download_passes();
    eprintln!(
        "\nFollower has performed {num_download_passes} download passes; wait for {}\n",
        num_download_passes + 5
    );

    while num_download_passes + 5 > pox_sync_comms.get_download_passes() {
        sleep_ms(1000);
        eprintln!(
            "\nFollower has performed {} download passes; wait for {}\n",
            pox_sync_comms.get_download_passes(),
            num_download_passes + 5
        );
    }

    eprintln!(
        "\nFollower has performed {} download passes\n",
        pox_sync_comms.get_download_passes()
    );

    let follower_tip_info = get_chain_info(&follower_conf);
    eprintln!(
        "\nFollower is at burn block {} stacks block {} (bad block is {bad_block_height})\n",
        follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
    );

    // follower rejects the bad block
    assert_eq!(follower_tip_info.stacks_tip_height, bad_block_height - 1);

    test_observer::clear();
    channel.stop_chains_coordinator();
    follower_channel.stop_chains_coordinator();
}

// TODO: test in epoch 2.1 with parser_v2
#[test]
#[ignore]
fn test_problematic_microblocks_are_not_mined() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let bad_blocks_dir = "/tmp/bad-blocks-test_problematic_microblocks_are_not_mined";
    if fs::metadata(bad_blocks_dir).is_ok() {
        fs::remove_dir_all(bad_blocks_dir).unwrap();
    }
    fs::create_dir_all(bad_blocks_dir).unwrap();

    std::env::set_var("STACKS_BAD_BLOCKS_DIR", bad_blocks_dir);

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_sk_3 = StacksPrivateKey::from_hex(SK_3).unwrap();
    let spender_stacks_addr_1 = to_addr(&spender_sk_1);
    let spender_stacks_addr_2 = to_addr(&spender_sk_2);
    let spender_stacks_addr_3 = to_addr(&spender_sk_3);
    let spender_addr_1: PrincipalData = spender_stacks_addr_1.into();
    let spender_addr_2: PrincipalData = spender_stacks_addr_2.into();
    let spender_addr_3: PrincipalData = spender_stacks_addr_3.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_2,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_3,
        amount: 1_000_000_000_000,
    });

    // force mainnet limits in 2.05 for this test
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // AST precheck becomes default at burn height
    conf.burnchain.ast_precheck_size_height = Some(210);

    // mine microblocks
    conf.node.mine_microblocks = true;
    conf.node.microblock_frequency = 1_000;
    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    // something just over the limit of the expression depth
    let exceeds_repeat_factor = 32;
    let tx_exceeds_body_start = "{ a : ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body_end = "} ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body = format!("{tx_exceeds_body_start}u1 {tx_exceeds_body_end}");

    let tx_exceeds = make_contract_publish_microblock_only(
        &spender_sk_2,
        0,
        (tx_exceeds_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-exceeds",
        &tx_exceeds_body,
    );
    let tx_exceeds_txid = StacksTransaction::consensus_deserialize(&mut &tx_exceeds[..])
        .unwrap()
        .txid();

    // something stupidly high over the expression depth
    let high_repeat_factor = AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1;
    let tx_high_body_start = "{ a : ".repeat(high_repeat_factor as usize);
    let tx_high_body_end = "} ".repeat(high_repeat_factor as usize);
    let tx_high_body = format!("{tx_high_body_start}u1 {tx_high_body_end}");

    let tx_high = make_contract_publish_microblock_only(
        &spender_sk_3,
        0,
        (tx_high_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-high",
        &tx_high_body,
    );
    let tx_high_txid = StacksTransaction::consensus_deserialize(&mut &tx_high[..])
        .unwrap()
        .txid();

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Submit problematic tx_exceeds transaction {tx_exceeds_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_exceeds);
    assert!(get_unconfirmed_tx(&http_origin, &tx_exceeds_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");
    info!("Submitted problematic tx_exceeds transaction {tx_exceeds_txid}");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;

        // give the microblock miner a chance
        sleep_ms(5_000);
    }

    // microblocks and blocks were all processed
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height == old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for microblocks to be processed");

    // no microblocks considered problematic
    assert!(all_new_files.is_empty());

    // one microblock contained tx_exceeds
    let microblocks = test_observer::get_microblocks();
    let mut found = false;
    for microblock in microblocks {
        let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_exceeds_txid {
                    found = true;
                    break;
                }
            }
        }
    }

    assert!(found);

    let (tip, cur_ast_rules) = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        (tip, cur_ast_rules)
    };

    assert_eq!(cur_ast_rules, ASTRules::Typical);

    // add another bad tx to the mempool
    info!("Submit problematic tx_high transaction {tx_high_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_high);
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");
    info!("Submitted problematic tx_high transaction {tx_high_txid}");

    btc_regtest_controller.build_next_block(1);
    info!("Mined block after submitting problematic tx_high transaction {tx_high_txid}");

    // wait for runloop to advance
    wait_for(30, || {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let new_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(new_tip.block_height > tip.block_height)
    })
    .expect("Failed waiting for runloop to advance");

    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // new rules took effect
    assert_eq!(cur_ast_rules, ASTRules::PrecheckSize);

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    eprintln!("old_tip_info = {old_tip_info:?}");

    // mine some microblocks, and log problematic microblocks
    for _i in 0..6 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;

        // give the microblock miner a chance
        sleep_ms(5_000);
    }

    // sleep a little longer before checking tip info; this should help with test flakiness
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height >= old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for microblocks to be processed");

    // none were problematic
    assert!(all_new_files.is_empty());

    // recently-submitted problematic transactions are not in the mempool
    // (but old ones that were already mined, and thus never considered, could still be present)
    test_debug!("Problematic tx {tx_high_txid} should be dropped");
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_none());

    // no microblock contained the tx_high bad transaction, ever
    let microblocks = test_observer::get_microblocks();
    for microblock in microblocks {
        let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                assert_ne!(parsed.txid(), tx_high_txid);
            }
        }
    }

    let new_tip_info = get_chain_info(&conf);

    eprintln!("\nBooting follower\n");

    // verify that a follower node that boots up with this node as a bootstrap peer will process
    // all of the blocks available, even if they are problematic, with the checks on.
    let (follower_conf, _, pox_sync_comms, follower_channel) = spawn_follower_node(&conf);

    eprintln!(
        "\nFollower booted on port {},{}\n",
        follower_conf.node.p2p_bind, follower_conf.node.rpc_bind
    );

    // Do not unwrap as we may just be slow
    let _ = wait_for(300, || {
        let follower_tip_info = get_chain_info(&follower_conf);
        eprintln!(
            "\nFollower is at burn block {} stacks block {}\n",
            follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height,
        );
        Ok(follower_tip_info.stacks_tip_height == new_tip_info.stacks_tip_height)
    });

    // make sure we aren't just slow -- wait for the follower to do a few download passes
    let num_download_passes = pox_sync_comms.get_download_passes();
    eprintln!(
        "\nFollower has performed {num_download_passes} download passes; wait for {}\n",
        num_download_passes + 5
    );

    wait_for(30, || {
        let download_passes = pox_sync_comms.get_download_passes();
        eprintln!(
            "\nFollower has performed {download_passes} download passes; wait for {}\n",
            num_download_passes + 5
        );
        Ok(download_passes >= num_download_passes + 5)
    })
    .expect("Failed waiting for follower to perform enough download passes");

    eprintln!(
        "\nFollower has performed {} download passes\n",
        pox_sync_comms.get_download_passes()
    );

    let follower_tip_info = get_chain_info(&follower_conf);
    eprintln!(
        "\nFollower is at burn block {} stacks block {}\n",
        follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
    );

    assert_eq!(
        follower_tip_info.stacks_tip_height,
        new_tip_info.stacks_tip_height
    );

    test_observer::clear();
    channel.stop_chains_coordinator();
    follower_channel.stop_chains_coordinator();
}

// TODO: test in epoch 2.1 with parser_v2
#[test]
#[ignore]
fn test_problematic_microblocks_are_not_relayed_or_stored() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let bad_blocks_dir = "/tmp/bad-blocks-test_problematic_microblocks_are_not_relayed_or_stored";
    if fs::metadata(bad_blocks_dir).is_ok() {
        fs::remove_dir_all(bad_blocks_dir).unwrap();
    }
    fs::create_dir_all(bad_blocks_dir).unwrap();

    std::env::set_var("STACKS_BAD_BLOCKS_DIR", bad_blocks_dir);

    let spender_sk_1 = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_sk_2 = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_sk_3 = StacksPrivateKey::from_hex(SK_3).unwrap();
    let spender_stacks_addr_1 = to_addr(&spender_sk_1);
    let spender_stacks_addr_2 = to_addr(&spender_sk_2);
    let spender_stacks_addr_3 = to_addr(&spender_sk_3);
    let spender_addr_1: PrincipalData = spender_stacks_addr_1.into();
    let spender_addr_2: PrincipalData = spender_stacks_addr_2.into();
    let spender_addr_3: PrincipalData = spender_stacks_addr_3.into();

    let (mut conf, _) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr_1,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_2,
        amount: 1_000_000_000_000,
    });
    conf.initial_balances.push(InitialBalance {
        address: spender_addr_3,
        amount: 1_000_000_000_000,
    });

    // force mainnet limits in 2.05 for this test
    conf.burnchain.epochs = Some(EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1,
            block_limit: BLOCK_LIMIT_MAINNET_20.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 10_002,
            block_limit: BLOCK_LIMIT_MAINNET_205.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 10_002,
            end_height: 9223372036854775807,
            block_limit: BLOCK_LIMIT_MAINNET_21.clone(),
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]));
    conf.burnchain.pox_2_activation = Some(10_003);

    // AST precheck becomes default at burn height
    conf.burnchain.ast_precheck_size_height = Some(210);

    // mine microblocks
    conf.node.mine_microblocks = true;
    conf.node.microblock_frequency = 1_000;
    conf.miner.microblock_attempt_time_ms = 1_000;
    conf.node.wait_time_for_microblocks = 0;

    conf.connection_options.inv_sync_interval = 3;

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    // something just over the limit of the expression depth
    let exceeds_repeat_factor = 32;
    let tx_exceeds_body_start = "{ a : ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body_end = "} ".repeat(exceeds_repeat_factor as usize);
    let tx_exceeds_body = format!("{tx_exceeds_body_start}u1 {tx_exceeds_body_end}");

    let tx_exceeds = make_contract_publish_microblock_only(
        &spender_sk_2,
        0,
        (tx_exceeds_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-exceeds",
        &tx_exceeds_body,
    );
    let tx_exceeds_txid = StacksTransaction::consensus_deserialize(&mut &tx_exceeds[..])
        .unwrap()
        .txid();

    // greatly exceeds AST depth, but is still mineable without a stack overflow
    let high_repeat_factor = AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1;
    let tx_high_body_start = "{ a : ".repeat(high_repeat_factor as usize);
    let tx_high_body_end = "} ".repeat(high_repeat_factor as usize);
    let tx_high_body = format!("{tx_high_body_start}u1 {tx_high_body_end}");

    let tx_high = make_contract_publish_microblock_only(
        &spender_sk_3,
        0,
        (tx_high_body.len() * 100) as u64,
        conf.burnchain.chain_id,
        "test-high",
        &tx_high_body,
    );
    let tx_high_txid = StacksTransaction::consensus_deserialize(&mut &tx_high[..])
        .unwrap()
        .txid();

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    debug!("Submit problematic tx_exceeds transaction {tx_exceeds_txid}");
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_exceeds);
    assert!(get_unconfirmed_tx(&http_origin, &tx_exceeds_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;

        // give the microblock miner a chance
        sleep_ms(5_000);
    }

    // microblocks and blocks were all processed
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height == old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for microblocks to be processed");

    // no microblocks considered problematic
    assert!(all_new_files.is_empty());

    // one microblock contained tx_exceeds
    let microblocks = test_observer::get_microblocks();
    let mut found = false;
    for microblock in microblocks {
        let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_exceeds_txid {
                    found = true;
                    break;
                }
            }
        }
    }

    assert!(found);

    let (tip, cur_ast_rules) = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        (tip, cur_ast_rules)
    };

    assert_eq!(cur_ast_rules, ASTRules::Typical);

    btc_regtest_controller.build_next_block(1);

    // wait for runloop to advance
    wait_for(30, || {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let new_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        Ok(new_tip.block_height > tip.block_height)
    })
    .expect("Failed waiting for runloop to advance");

    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // new rules took effect
    assert_eq!(cur_ast_rules, ASTRules::PrecheckSize);

    // the follower we will soon boot up will start applying the new AST rules at this height.
    // Make it so the miner does *not* follow the rules
    {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let mut tx = sortdb.tx_begin().unwrap();
        SortitionDB::override_ast_rule_height(&mut tx, ASTRules::PrecheckSize, 10_000).unwrap();
        tx.commit().unwrap();
    }
    let cur_ast_rules = {
        let sortdb = btc_regtest_controller.sortdb_mut();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        eprintln!("Sort db tip: {}", tip.block_height);
        let cur_ast_rules = SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
        cur_ast_rules
    };

    // we reverted to the old rules (but the follower won't)
    assert_eq!(cur_ast_rules, ASTRules::Typical);

    // add another bad tx to the mempool.
    // because the miner is now non-conformant, it should mine this tx.
    debug!("Submit problematic tx_high transaction {tx_high_txid}");

    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "1");
    submit_tx(&http_origin, &tx_high);
    assert!(get_unconfirmed_tx(&http_origin, &tx_high_txid).is_some());
    std::env::set_var("STACKS_DISABLE_TX_PROBLEMATIC_CHECK", "0");

    let (_, mut cur_files) = find_new_files(bad_blocks_dir, &HashSet::new());
    let old_tip_info = get_chain_info(&conf);
    let mut all_new_files = vec![];

    eprintln!("old_tip_info = {old_tip_info:?}");

    // mine some blocks, and log problematic microblocks
    for _i in 0..6 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let cur_files_old = cur_files.clone();
        let (mut new_files, cur_files_new) = find_new_files(bad_blocks_dir, &cur_files_old);
        all_new_files.append(&mut new_files);
        cur_files = cur_files_new;

        let cur_ast_rules = {
            let sortdb = btc_regtest_controller.sortdb_mut();
            let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
            let cur_ast_rules =
                SortitionDB::get_ast_rules(sortdb.conn(), tip.block_height).unwrap();
            cur_ast_rules
        };

        // we reverted to the old rules (but the follower won't)
        assert_eq!(cur_ast_rules, ASTRules::Typical);

        // give the microblock miner a chance
        sleep_ms(5_000);
    }

    // sleep a little longer before checking tip info; this should help with test flakiness
    wait_for(30, || {
        let tip_info = get_chain_info(&conf);
        Ok(tip_info.stacks_tip_height >= old_tip_info.stacks_tip_height + 5)
    })
    .expect("Failed waiting for microblocks to be processed");

    // at least one was problematic.
    // the miner might make multiple microblocks (only some of which are confirmed), so also check
    // the event observer to see that we actually picked up tx_high
    assert!(!all_new_files.is_empty());

    // tx_high got mined by the miner
    let microblocks = test_observer::get_microblocks();
    let mut bad_block_id = None;
    for microblock in microblocks {
        let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(..) = &parsed.payload {
                if parsed.txid() == tx_high_txid {
                    bad_block_id = {
                        let parts: Vec<_> = microblock
                            .get("parent_index_block_hash")
                            .unwrap()
                            .as_str()
                            .unwrap()
                            .split("0x")
                            .collect();
                        let bad_block_id_hex = parts[1];
                        debug!("bad_block_id_hex = '{bad_block_id_hex}'");
                        Some(StacksBlockId::from_hex(bad_block_id_hex).unwrap())
                    };
                }
            }
        }
    }
    assert!(bad_block_id.is_some());
    let bad_block_id = bad_block_id.unwrap();
    let bad_block = get_block(&http_origin, &bad_block_id).unwrap();
    let bad_block_height = bad_block.header.total_work.work;

    // follower should not process bad_block_height or higher
    let new_tip_info = get_chain_info(&conf);

    eprintln!("\nBooting follower\n");

    // verify that a follower node that boots up with this node as a bootstrap peer will process
    // all of the blocks available, even if they are problematic, with the checks on.
    let (follower_conf, _, pox_sync_comms, follower_channel) = spawn_follower_node(&conf);

    eprintln!(
        "\nFollower booted on port {},{}\n",
        follower_conf.node.p2p_bind, follower_conf.node.rpc_bind
    );

    // Do not unwrap as we may just be slow
    let _ = wait_for(300, || {
        let follower_tip_info = get_chain_info(&follower_conf);
        eprintln!(
            "\nFollower is at burn block {} stacks block {}\n",
            follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height,
        );
        Ok(follower_tip_info.stacks_tip_height == new_tip_info.stacks_tip_height)
    });

    // make sure we aren't just slow -- wait for the follower to do a few download passes
    let num_download_passes = pox_sync_comms.get_download_passes();
    eprintln!(
        "\nFollower has performed {num_download_passes} download passes; wait for {}\n",
        num_download_passes + 5
    );

    wait_for(30, || {
        let download_passes = pox_sync_comms.get_download_passes();
        eprintln!(
            "\nFollower has performed {download_passes} download passes; wait for {}\n",
            num_download_passes + 5
        );
        Ok(download_passes >= num_download_passes + 5)
    })
    .expect("Failed waiting for follower to perform enough download passes");
    eprintln!(
        "\nFollower has performed {} download passes\n",
        pox_sync_comms.get_download_passes()
    );

    let follower_tip_info = get_chain_info(&follower_conf);
    eprintln!(
        "\nFollower is at burn block {} stacks block {} (bad block is {bad_block_height})\n",
        follower_tip_info.burn_block_height, follower_tip_info.stacks_tip_height
    );

    // follower rejects the bad microblock -- can't append subsequent blocks
    assert_eq!(follower_tip_info.stacks_tip_height, bad_block_height);

    test_observer::clear();
    channel.stop_chains_coordinator();
    follower_channel.stop_chains_coordinator();
}

/// Verify that we push all boot receipts even before bootstrapping
#[test]
#[ignore]
fn push_boot_receipts() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _) = neon_integration_test_conf();
    test_observer::register_any(&mut conf);

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    test_observer::spawn();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let _chainstate = run_loop.boot_chainstate(&burnchain_config);

    // verify that the event observer got its boot receipts
    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 1);

    let events = blocks[0]
        .as_object()
        .expect("Expected JSON object for mined block event")
        .get("events")
        .expect("Expected events key in mined block event")
        .as_array()
        .expect("Expected events key to be an array in mined block event");

    assert_eq!(events.len(), 26);
}

/// Verify that we can operate with a custom wallet name
#[test]
#[ignore]
fn run_with_custom_wallet() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _) = neon_integration_test_conf();
    test_observer::register_any(&mut conf);

    // custom wallet
    conf.burnchain.wallet_name = "test_with_custom_wallet".to_string();

    test_observer::spawn();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    thread::spawn(move || run_loop.start(None, 0));

    // Give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // First block wakes up the run loop.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Second block will hold our VRF registration.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // Third block will be the first mined Stacks block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // verify that the event observer got its boot receipts.
    // If we get this far, then it also means that mining and block-production worked.
    let blocks = test_observer::get_blocks();
    assert!(blocks.len() > 1);

    // bitcoin node knows of this wallet
    let wallets = BitcoinRPCRequest::list_wallets(&conf).unwrap();
    let mut found = false;
    for w in wallets {
        if w == conf.burnchain.wallet_name {
            found = true;
        }
    }
    assert!(found);
}

/// Make a contract that takes a parameterized amount of runtime
/// `num_index_of` is the number of times to call `index-of`
fn make_runtime_sized_contract(num_index_of: usize, nonce: u64, addr_prefix: &str) -> String {
    let iters_256 = num_index_of / 256;
    let iters_mod = num_index_of % 256;
    let full_iters_code_parts: Vec<String> = (0..iters_256)
        .map(|_cnt| "(unwrap-panic (index-of BUFF_TO_BYTE input))".to_string())
        .collect();

    let full_iters_code = full_iters_code_parts.join("\n      ");

    let iters_mod_code_parts: Vec<String> =
        (0..iters_mod).map(|cnt| format!("0x{cnt:0>2x}")).collect();

    let iters_mod_code = format!("(list {})", iters_mod_code_parts.join(" "));

    let code = format!(
        "
        (define-constant BUFF_TO_BYTE (list
           0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f
           0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19 0x1a 0x1b 0x1c 0x1d 0x1e 0x1f
           0x20 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0x28 0x29 0x2a 0x2b 0x2c 0x2d 0x2e 0x2f
           0x30 0x31 0x32 0x33 0x34 0x35 0x36 0x37 0x38 0x39 0x3a 0x3b 0x3c 0x3d 0x3e 0x3f
           0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47 0x48 0x49 0x4a 0x4b 0x4c 0x4d 0x4e 0x4f
           0x50 0x51 0x52 0x53 0x54 0x55 0x56 0x57 0x58 0x59 0x5a 0x5b 0x5c 0x5d 0x5e 0x5f
           0x60 0x61 0x62 0x63 0x64 0x65 0x66 0x67 0x68 0x69 0x6a 0x6b 0x6c 0x6d 0x6e 0x6f
           0x70 0x71 0x72 0x73 0x74 0x75 0x76 0x77 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
           0x80 0x81 0x82 0x83 0x84 0x85 0x86 0x87 0x88 0x89 0x8a 0x8b 0x8c 0x8d 0x8e 0x8f
           0x90 0x91 0x92 0x93 0x94 0x95 0x96 0x97 0x98 0x99 0x9a 0x9b 0x9c 0x9d 0x9e 0x9f
           0xa0 0xa1 0xa2 0xa3 0xa4 0xa5 0xa6 0xa7 0xa8 0xa9 0xaa 0xab 0xac 0xad 0xae 0xaf
           0xb0 0xb1 0xb2 0xb3 0xb4 0xb5 0xb6 0xb7 0xb8 0xb9 0xba 0xbb 0xbc 0xbd 0xbe 0xbf
           0xc0 0xc1 0xc2 0xc3 0xc4 0xc5 0xc6 0xc7 0xc8 0xc9 0xca 0xcb 0xcc 0xcd 0xce 0xcf
           0xd0 0xd1 0xd2 0xd3 0xd4 0xd5 0xd6 0xd7 0xd8 0xd9 0xda 0xdb 0xdc 0xdd 0xde 0xdf
           0xe0 0xe1 0xe2 0xe3 0xe4 0xe5 0xe6 0xe7 0xe8 0xe9 0xea 0xeb 0xec 0xed 0xee 0xef
           0xf0 0xf1 0xf2 0xf3 0xf4 0xf5 0xf6 0xf7 0xf8 0xf9 0xfa 0xfb 0xfc 0xfd 0xfe 0xff
        ))
        (define-private (crash-me-folder (input (buff 1)) (ctr uint))
            (begin
                ;; full_iters_code
                {full_iters_code}
                (+ u1 ctr)
            )
        )
        (define-public (crash-me (name (string-ascii 128)))
            (begin
                ;; call index-of (iters_256 * 256) times
                (fold crash-me-folder BUFF_TO_BYTE u0)
                ;; call index-of iters_mod times
                (fold crash-me-folder {iters_mod_code} u0)
                (print name)
                (ok u0)
            )
        )
        (begin
            (crash-me \"large-{nonce}-{addr_prefix}-{num_index_of}\"))
        ",
    );

    eprintln!("{code}");
    code
}

enum TxChainStrategy {
    Expensive,
    Random,
}

pub fn make_expensive_tx_chain(
    privk: &StacksPrivateKey,
    fee_plus: u64,
    chain_id: u32,
    mblock_only: bool,
) -> Vec<Vec<u8>> {
    let addr = to_addr(privk);
    let mut chain = vec![];
    let num_index_of = 256;
    for nonce in 0..25 {
        let mut addr_prefix = addr.to_string();
        let _ = addr_prefix.split_off(12);
        let contract_name = format!("large-{nonce}-{addr_prefix}-{num_index_of}");
        eprintln!("Make tx {contract_name}");
        let tx = if mblock_only {
            make_contract_publish_microblock_only(
                privk,
                nonce,
                1049230 + nonce + fee_plus,
                chain_id,
                &contract_name,
                &make_runtime_sized_contract(num_index_of, nonce, &addr_prefix),
            )
        } else {
            make_contract_publish(
                privk,
                nonce,
                1049230 + nonce + fee_plus,
                chain_id,
                &contract_name,
                &make_runtime_sized_contract(num_index_of, nonce, &addr_prefix),
            )
        };
        chain.push(tx);
    }
    chain
}

pub fn make_random_tx_chain(
    privk: &StacksPrivateKey,
    fee_plus: u64,
    chain_id: u32,
    mblock_only: bool,
) -> Vec<Vec<u8>> {
    let addr = to_addr(privk);
    let mut chain = vec![];

    for nonce in 0..25 {
        // N.B. private keys are 32-33 bytes, so this is always safe
        let random_iters = privk.to_bytes()[nonce as usize] as usize;

        let be_bytes = [
            privk.to_bytes()[nonce as usize],
            privk.to_bytes()[(nonce + 1) as usize],
        ];

        let random_extra_fee = u16::from_be_bytes(be_bytes) as u64;

        let mut addr_prefix = addr.to_string();
        let _ = addr_prefix.split_off(12);
        let contract_name = format!("large-{nonce}-{addr_prefix}-{random_iters}");
        eprintln!("Make tx {contract_name}");
        let tx = if mblock_only {
            make_contract_publish_microblock_only(
                privk,
                nonce,
                1049230 + nonce + fee_plus + random_extra_fee,
                chain_id,
                &contract_name,
                &make_runtime_sized_contract(random_iters, nonce, &addr_prefix),
            )
        } else {
            make_contract_publish(
                privk,
                nonce,
                1049230 + nonce + fee_plus + random_extra_fee,
                chain_id,
                &contract_name,
                &make_runtime_sized_contract(random_iters, nonce, &addr_prefix),
            )
        };
        chain.push(tx);
    }
    chain
}

fn make_mblock_tx_chain(privk: &StacksPrivateKey, fee_plus: u64, chain_id: u32) -> Vec<Vec<u8>> {
    let addr = to_addr(privk);
    let mut chain = vec![];

    for nonce in 0..25 {
        // N.B. private keys are 32-33 bytes, so this is always safe
        let random_iters = privk.to_bytes()[nonce as usize] as usize;

        let be_bytes = [
            privk.to_bytes()[nonce as usize],
            privk.to_bytes()[(nonce + 1) as usize],
        ];

        let random_extra_fee = u16::from_be_bytes(be_bytes) as u64;

        let mut addr_prefix = addr.to_string();
        let _ = addr_prefix.split_off(12);
        let contract_name = format!("crct-{nonce}-{addr_prefix}-{random_iters}");
        eprintln!("Make tx {contract_name}");
        let tx = make_contract_publish_microblock_only(
            privk,
            nonce,
            1049230 + nonce + fee_plus + random_extra_fee,
            chain_id,
            &contract_name,
            &make_runtime_sized_contract(1, nonce, &addr_prefix),
        );
        chain.push(tx);
    }
    chain
}

fn test_competing_miners_build_on_same_chain(
    num_miners: usize,
    conf_template: Config,
    mblock_only: bool,
    block_time_ms: u64,
    chain_strategy: TxChainStrategy,
) {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let privks: Vec<_> = (0..100).map(|_| StacksPrivateKey::random()).collect();
    let balances: Vec<_> = privks
        .iter()
        .map(|privk| {
            let addr = to_addr(privk);
            InitialBalance {
                address: addr.into(),
                amount: 1_000_000_000,
            }
        })
        .collect();

    let mut confs = vec![];
    let mut burnchain_configs = vec![];
    let mut blocks_processed = vec![];

    for _i in 0..num_miners {
        let seed = StacksPrivateKey::random().to_bytes();
        let (mut conf, _) = neon_integration_test_conf_with_seed(seed);

        conf.initial_balances.append(&mut balances.clone());

        conf.node.mine_microblocks = conf_template.node.mine_microblocks;
        conf.miner.microblock_attempt_time_ms = conf_template.miner.microblock_attempt_time_ms;
        conf.node.wait_time_for_microblocks = conf_template.node.wait_time_for_microblocks;
        conf.node.microblock_frequency = conf_template.node.microblock_frequency;
        conf.miner.first_attempt_time_ms = conf_template.miner.first_attempt_time_ms;
        conf.miner.subsequent_attempt_time_ms = conf_template.miner.subsequent_attempt_time_ms;
        conf.node.wait_time_for_blocks = conf_template.node.wait_time_for_blocks;
        conf.burnchain.max_rbf = conf_template.burnchain.max_rbf;

        // multiple nodes so they must download from each other
        conf.miner.wait_for_block_download = true;

        confs.push(conf);
    }

    let chain_id = confs[0].burnchain.chain_id;

    let node_privkey_1 = Secp256k1PrivateKey::from_seed(&confs[0].node.local_peer_seed);
    for i in 1..num_miners {
        let chain_id = confs[0].burnchain.chain_id;
        let peer_version = confs[0].burnchain.peer_version;
        let p2p_bind = confs[0].node.p2p_bind.clone();

        confs[i].node.set_bootstrap_nodes(
            format!(
                "{}@{p2p_bind}",
                &StacksPublicKey::from_private(&node_privkey_1).to_hex(),
            ),
            chain_id,
            peer_version,
        );
    }

    // use long reward cycles
    for conf in &confs {
        let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());
        let reward_cycle_len = 100;
        let prepare_phase_len = 20;
        let pox_constants = PoxConstants::new(
            reward_cycle_len,
            prepare_phase_len,
            4 * prepare_phase_len / 5,
            5,
            15,
            (16 * reward_cycle_len - 1).into(),
            (17 * reward_cycle_len).into(),
            u32::MAX,
            u32::MAX,
            u32::MAX,
            u32::MAX,
        );
        burnchain_config.pox_constants = pox_constants.clone();

        burnchain_configs.push(burnchain_config);
    }

    let mut btcd_controller = BitcoinCoreController::new(confs[0].clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        confs[0].clone(),
        None,
        Some(burnchain_configs[0].clone()),
        None,
    );

    btc_regtest_controller.bootstrap_chain(1);

    // make sure all miners have BTC
    for conf in confs.iter().skip(1) {
        let old_mining_pubkey = btc_regtest_controller.get_mining_pubkey().unwrap();
        btc_regtest_controller
            .set_mining_pubkey(conf.burnchain.local_mining_public_key.clone().unwrap());
        btc_regtest_controller.bootstrap_chain(1);
        btc_regtest_controller.set_mining_pubkey(old_mining_pubkey);
    }

    btc_regtest_controller.bootstrap_chain((199 - num_miners) as u64);

    eprintln!("Chain bootstrapped...");

    for (i, burnchain_config) in burnchain_configs.into_iter().enumerate() {
        let mut run_loop = neon::RunLoop::new(confs[i].clone());
        let blocks_processed_arc = run_loop.get_blocks_processed_arc();

        blocks_processed.push(blocks_processed_arc);
        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));
    }

    let http_origin = format!("http://{}", &confs[0].node.rpc_bind);

    // give the run loops some time to start up!
    for bp in &blocks_processed {
        wait_for_runloop(bp);
    }

    // activate miners
    eprintln!("\n\nBoot miner 0\n\n");
    loop {
        let tip_info_opt = get_chain_info_opt(&confs[0]);
        if let Some(tip_info) = tip_info_opt {
            eprintln!("\n\nMiner 1: {tip_info:?}\n\n");
            if tip_info.stacks_tip_height > 0 {
                break;
            }
        } else {
            eprintln!("\n\nWaiting for miner 0...\n\n");
        }
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed[0]);
    }

    for (i, conf) in confs.iter().enumerate().skip(1) {
        eprintln!("\n\nBoot miner {i}\n\n");
        loop {
            let tip_info_opt = get_chain_info_opt(conf);
            if let Some(tip_info) = tip_info_opt {
                eprintln!("\n\nMiner {i}: {tip_info:?}\n\n");
                if tip_info.stacks_tip_height > 0 {
                    break;
                }
            } else {
                eprintln!("\n\nWaiting for miner {i}...\n\n");
            }
            next_block_and_iterate(&mut btc_regtest_controller, &blocks_processed[i], 5_000);
        }
    }

    eprintln!("\n\nBegin transactions\n\n");

    // blast out lots of expensive transactions.
    // keeps the mempool full, and makes it so miners will spend a nontrivial amount of time
    // building blocks
    let all_txs: Vec<_> = privks
        .iter()
        .enumerate()
        .map(|(i, pk)| match chain_strategy {
            TxChainStrategy::Expensive => {
                make_expensive_tx_chain(pk, (25 * i) as u64, chain_id, mblock_only)
            }
            TxChainStrategy::Random => {
                make_random_tx_chain(pk, (25 * i) as u64, chain_id, mblock_only)
            }
        })
        .collect();
    let mut cnt = 0;
    for tx_chain in all_txs {
        for tx in tx_chain {
            eprintln!("\n\nSubmit tx {cnt}\n\n");
            submit_tx(&http_origin, &tx);
            cnt += 1;
        }
    }

    eprintln!("\n\nBegin mining\n\n");

    // mine quickly -- see if we can induce flash blocks
    for i in 0..1000 {
        eprintln!("\n\nBuild block {i}\n\n");
        btc_regtest_controller.build_next_block(1);
        sleep_ms(block_time_ms);
    }
}

// TODO: this needs to run as a smoke test, since they take too long to run in CI
#[test]
#[ignore]
fn test_one_miner_build_anchor_blocks_on_same_chain_without_rbf() {
    let (mut conf, _) = neon_integration_test_conf();

    conf.node.mine_microblocks = false;
    conf.miner.microblock_attempt_time_ms = 5_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 10_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.burnchain.max_rbf = 0;
    conf.node.wait_time_for_blocks = 1_000;

    test_competing_miners_build_on_same_chain(1, conf, false, 10_000, TxChainStrategy::Random)
}

// TODO: this needs to run as a smoke test, since they take too long to run in CI
#[test]
#[ignore]
fn test_competing_miners_build_anchor_blocks_on_same_chain_without_rbf() {
    let (mut conf, _) = neon_integration_test_conf();

    conf.node.mine_microblocks = false;
    conf.miner.microblock_attempt_time_ms = 5_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 10_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.burnchain.max_rbf = 0;
    conf.node.wait_time_for_blocks = 1_000;

    test_competing_miners_build_on_same_chain(5, conf, false, 10_000, TxChainStrategy::Expensive)
}

// TODO: this needs to run as a smoke test, since they take too long to run in CI
#[test]
#[ignore]
fn test_competing_miners_build_anchor_blocks_and_microblocks_on_same_chain() {
    let (mut conf, _) = neon_integration_test_conf();

    conf.node.mine_microblocks = true;
    conf.miner.microblock_attempt_time_ms = 2_000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 0;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_blocks = 1_000;

    test_competing_miners_build_on_same_chain(5, conf, true, 15_000, TxChainStrategy::Random)
}

#[test]
#[ignore]
fn microblock_miner_multiple_attempts() {
    let (mut conf, miner_account) = neon_integration_test_conf();
    let chain_id = conf.burnchain.chain_id;

    conf.node.mine_microblocks = true;
    conf.miner.microblock_attempt_time_ms = 2_000;
    conf.node.wait_time_for_microblocks = 100;
    conf.node.microblock_frequency = 100;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_blocks = 1_000;

    let privks: Vec<_> = (0..100).map(|_| StacksPrivateKey::random()).collect();
    let balances: Vec<_> = privks
        .iter()
        .map(|privk| {
            let addr = to_addr(privk);
            InitialBalance {
                address: addr.into(),
                amount: 1_000_000_000,
            }
        })
        .collect();

    conf.initial_balances = balances;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:

    let account = get_account(&http_origin, &miner_account);
    eprintln!("Miner account: {account:?}");

    let all_txs: Vec<_> = privks
        .iter()
        .enumerate()
        .map(|(i, pk)| make_mblock_tx_chain(pk, (25 * i) as u64, chain_id))
        .collect();

    let _handle = thread::spawn(move || {
        for (i, txi) in all_txs.iter().enumerate() {
            for (j, tx) in txi.iter().enumerate() {
                eprintln!("\n\nSubmit tx {i},{j}\n\n");
                submit_tx(&http_origin, tx);
                sleep_ms(1_000);
            }
        }
    });

    for _i in 0..10 {
        sleep_ms(30_000);
        btc_regtest_controller.build_next_block(1);
    }

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn min_txs() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let path = "/tmp/activate_vrf_key.min_txs.json";
    conf.miner.min_tx_count = 4;
    conf.miner.first_attempt_time_ms = 0;
    conf.miner.activated_vrf_key_path = Some(path.to_string());

    if fs::metadata(path).is_ok() {
        fs::remove_file(path).unwrap();
    }

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ,
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();

    for i in 0..2 {
        let code = format!("(print \"hello world {i}\")");
        let publish = make_contract_publish(
            &spender_sk,
            i as u64,
            1000,
            conf.burnchain.chain_id,
            &format!("test-publish-{i}"),
            &code,
        );
        submit_tx(&http_origin, &publish);

        debug!("Try to build too-small a block {i}");
        next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 15);
    }

    let blocks = test_observer::get_blocks();
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        if transactions.len() > 1 {
            debug!("Got block: {block:?}");
            assert!(transactions.len() >= 4);
        }
    }

    let saved_vrf_key = RelayerThread::load_saved_vrf_key(path);
    assert!(saved_vrf_key.is_some());

    test_observer::clear();
}

#[test]
#[ignore]
fn filter_txs_by_type() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    let path = "/tmp/activate_vrf_key.filter_txs.json";
    conf.miner.min_tx_count = 4;
    conf.miner.first_attempt_time_ms = 0;
    conf.miner.activated_vrf_key_path = Some(path.to_string());
    conf.miner.txs_to_consider = [MemPoolWalkTxTypes::TokenTransfer].into_iter().collect();

    if fs::metadata(path).is_ok() {
        fs::remove_file(path).unwrap();
    }

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ,
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();
    let mut sent_txids = HashSet::new();
    for i in 0..2 {
        let code = format!("(print \"hello world {i}\")");
        let publish = make_contract_publish(
            &spender_sk,
            i as u64,
            1000,
            conf.burnchain.chain_id,
            &format!("test-publish-{i}"),
            &code,
        );
        let parsed = StacksTransaction::consensus_deserialize(&mut &publish[..]).unwrap();
        sent_txids.insert(parsed.txid());

        submit_tx(&http_origin, &publish);
        next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 15);
    }

    let blocks = test_observer::get_blocks();
    for block in blocks {
        info!("block: {block:?}");
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if sent_txids.contains(&parsed.txid()) {
                panic!("Included a smart contract");
            }
        }
    }

    let saved_vrf_key = RelayerThread::load_saved_vrf_key(path);
    assert!(saved_vrf_key.is_some());

    test_observer::clear();
}

#[test]
#[ignore]
fn filter_txs_by_origin() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::random();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();
    test_observer::register_any(&mut conf);

    conf.miner.min_tx_count = 4;
    conf.miner.first_attempt_time_ms = 0;
    conf.miner.filter_origins =
        [StacksAddress::from_string("STA2MZWV9N67TBYVWTE0PSSKMJ2F6YXW7DX96QAM").unwrap()]
            .into_iter()
            .collect();

    let spender_bal = 10_000_000_000 * u64::from(core::MICROSTACKS_PER_STACKS);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ,
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();
    let mut sent_txids = HashSet::new();
    for i in 0..2 {
        let code = format!("(print \"hello world {i}\")");
        let publish = make_contract_publish(
            &spender_sk,
            i as u64,
            1000,
            conf.burnchain.chain_id,
            &format!("test-publish-{i}"),
            &code,
        );
        let parsed = StacksTransaction::consensus_deserialize(&mut &publish[..]).unwrap();
        sent_txids.insert(parsed.txid());

        submit_tx(&http_origin, &publish);
        next_block_and_wait_with_timeout(&mut btc_regtest_controller, &blocks_processed, 15);
    }

    let blocks = test_observer::get_blocks();
    for block in blocks {
        info!("block: {block:?}");
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if sent_txids.contains(&parsed.txid()) {
                panic!("Included a smart contract");
            }
        }
    }

    test_observer::clear();
}

// https://stackoverflow.com/questions/26958489/how-to-copy-a-folder-recursively-in-rust
fn copy_dir_all(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(entry.path(), dst.as_ref().join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

#[test]
#[ignore]
fn bitcoin_reorg_flap() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, _miner_account) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {sort_height}");

    while sort_height < 210 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {sort_height}");
    }

    // stop bitcoind and copy its DB to simulate a chain flap
    btcd_controller.stop_bitcoind().unwrap();
    thread::sleep(Duration::from_secs(5));

    let btcd_dir = conf.get_burnchain_path_str();
    let mut new_conf = conf.clone();
    new_conf.node.working_dir = format!("{}.new", &conf.node.working_dir);
    fs::create_dir_all(&new_conf.node.working_dir).unwrap();

    copy_dir_all(&btcd_dir, new_conf.get_burnchain_path_str()).unwrap();

    // resume
    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    thread::sleep(Duration::from_secs(5));

    info!("\n\nBegin fork A\n\n");

    // make fork A
    for _i in 0..3 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    btcd_controller.stop_bitcoind().unwrap();

    info!("\n\nBegin reorg flap from A to B\n\n");

    // carry out the flap to fork B -- new_conf's state was the same as before the reorg
    let mut btcd_controller = BitcoinCoreController::new(new_conf.clone());
    let btc_regtest_controller = BitcoinRegtestController::new(new_conf, None);

    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    for _i in 0..5 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    btcd_controller.stop_bitcoind().unwrap();

    info!("\n\nBegin reorg flap from B to A\n\n");

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    let btc_regtest_controller = BitcoinRegtestController::new(conf, None);
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    // carry out the flap back to fork A
    for _i in 0..7 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    assert_eq!(channel.get_sortitions_processed(), 225);
    btcd_controller.stop_bitcoind().unwrap();
    channel.stop_chains_coordinator();
}

/// Advance the bitcoin chain and wait for the miner and any followers to
/// process the next block.
/// NOTE: This only works if the followers are mock-mining, or else the counter
///       will not be updated.
fn next_block_and_wait_all(
    btc_controller: &mut BitcoinRegtestController,
    miner_blocks_processed: &Arc<AtomicU64>,
    follower_blocks_processed: &[&Arc<AtomicU64>],
    timeout: Option<Duration>,
) -> bool {
    let followers_current: Vec<_> = follower_blocks_processed
        .iter()
        .map(|blocks_processed| blocks_processed.load(Ordering::SeqCst))
        .collect();

    if !next_block_and_wait(btc_controller, miner_blocks_processed) {
        return false;
    }

    // wait for followers to catch up
    let timer = Instant::now();
    loop {
        let finished = follower_blocks_processed
            .iter()
            .zip(followers_current.iter())
            .all(|(blocks_processed, start_count)| {
                blocks_processed.load(Ordering::SeqCst) > *start_count
            });

        if finished {
            break;
        }

        if let Some(t) = timeout {
            if timer.elapsed() > t {
                panic!("next_block_and_wait_all() timed out after {t:?}")
            }
        }

        thread::sleep(Duration::from_millis(100));
    }

    true
}

#[test]
#[ignore]
fn bitcoin_reorg_flap_with_follower() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, _miner_account) = neon_integration_test_conf();
    let timeout = Some(Duration::from_secs(60));

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut miner_run_loop = neon::RunLoop::new(conf.clone());
    let run_loop_stopper = miner_run_loop.get_termination_switch();
    let miner_blocks_processed = miner_run_loop.get_blocks_processed_arc();
    let miner_channel = miner_run_loop.get_coordinator_channel().unwrap();

    let mut follower_conf = conf.clone();
    follower_conf.node.mock_mining = true;
    follower_conf.events_observers.clear();
    follower_conf.node.working_dir = format!("{}-follower", &conf.node.working_dir);
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

    let run_loop_thread = thread::spawn(move || miner_run_loop.start(None, 0));
    wait_for_runloop(&miner_blocks_processed);

    // figure out the started node's port
    let node_info = get_chain_info(&conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            conf.node.p2p_bind
        ),
        CHAIN_ID_TESTNET,
        PEER_VERSION_TESTNET,
    );

    let mut follower_run_loop = neon::RunLoop::new(follower_conf.clone());
    let follower_run_loop_stopper = follower_run_loop.get_termination_switch();
    let follower_blocks_processed = follower_run_loop.get_blocks_processed_arc();
    let follower_channel = follower_run_loop.get_coordinator_channel().unwrap();

    let follower_thread = thread::spawn(move || follower_run_loop.start(None, 0));
    wait_for_runloop(&follower_blocks_processed);

    eprintln!("Follower bootup complete!");

    // first block wakes up the run loop
    next_block_and_wait_with_timeout(&mut btc_regtest_controller, &miner_blocks_processed, 60);

    // next block will hold our VRF registration
    // Note that the follower will not see its block processed counter bumped here
    next_block_and_wait_all(
        &mut btc_regtest_controller,
        &miner_blocks_processed,
        &[&follower_blocks_processed],
        timeout,
    );

    let mut miner_sort_height = miner_channel.get_sortitions_processed();
    let mut follower_sort_height = follower_channel.get_sortitions_processed();
    eprintln!(
        "Miner sort height: {miner_sort_height}, follower sort height: {follower_sort_height}"
    );

    while miner_sort_height < 210 && follower_sort_height < 210 {
        next_block_and_wait_all(
            &mut btc_regtest_controller,
            &miner_blocks_processed,
            &[&follower_blocks_processed],
            timeout,
        );
        miner_sort_height = miner_channel.get_sortitions_processed();
        follower_sort_height = miner_channel.get_sortitions_processed();
        eprintln!(
            "Miner sort height: {miner_sort_height}, follower sort height: {follower_sort_height}"
        );
    }

    // stop bitcoind and copy its DB to simulate a chain flap
    btcd_controller.stop_bitcoind().unwrap();
    thread::sleep(Duration::from_secs(5));

    let btcd_dir = conf.get_burnchain_path_str();
    let mut new_conf = conf.clone();
    new_conf.node.working_dir = format!("{}.new", &conf.node.working_dir);
    fs::create_dir_all(&new_conf.node.working_dir).unwrap();

    copy_dir_all(&btcd_dir, new_conf.get_burnchain_path_str()).unwrap();

    // resume
    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    thread::sleep(Duration::from_secs(5));

    info!("\n\nBegin fork A\n\n");

    // make fork A
    for _i in 0..3 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    btcd_controller.stop_bitcoind().unwrap();

    info!("\n\nBegin reorg flap from A to B\n\n");

    // carry out the flap to fork B -- new_conf's state was the same as before the reorg
    let mut btcd_controller = BitcoinCoreController::new(new_conf.clone());
    let btc_regtest_controller = BitcoinRegtestController::new(new_conf, None);

    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    for _i in 0..5 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    btcd_controller.stop_bitcoind().unwrap();

    info!("\n\nBegin reorg flap from B to A\n\n");

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    let btc_regtest_controller = BitcoinRegtestController::new(conf, None);
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    // carry out the flap back to fork A
    for _i in 0..7 {
        btc_regtest_controller.build_next_block(1);
        thread::sleep(Duration::from_secs(5));
    }

    assert_eq!(miner_channel.get_sortitions_processed(), 225);
    assert_eq!(follower_channel.get_sortitions_processed(), 225);

    run_loop_stopper.store(false, Ordering::SeqCst);
    follower_run_loop_stopper.store(false, Ordering::SeqCst);

    run_loop_thread.join().unwrap();
    follower_thread.join().unwrap();
}

/// Tests the following:
///  - Mock miner output to file
///  - Test replay of mock mined blocks using `stacks-inspect  replay-mock-mining``
#[test]
#[ignore]
fn mock_miner_replay() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let timeout = Some(Duration::from_secs(30));
    // Had to add this so that mock miner makes an attempt on EVERY block
    let block_gap = Duration::from_secs(1);

    let test_dir = PathBuf::from("/tmp/stacks-integration-test-mock_miner_replay");
    _ = fs::remove_dir_all(&test_dir);

    let (conf, _miner_account) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());
    let mut btc_regtest_controller =
        BitcoinRegtestController::with_burnchain(conf.clone(), None, Some(burnchain_config), None);

    btc_regtest_controller.bootstrap_chain(201);

    info!("Chain bootstrapped...");

    let mut miner_run_loop = neon::RunLoop::new(conf.clone());
    let miner_blocks_processed = miner_run_loop.get_blocks_processed_arc();
    let miner_channel = miner_run_loop.get_coordinator_channel().unwrap();

    let mut follower_conf = conf.clone();
    follower_conf.events_observers.clear();
    follower_conf.node.mock_mining = true;
    follower_conf.node.mock_mining_output_dir = Some(test_dir.join("mock-miner-output"));
    follower_conf.node.working_dir = format!("{}-follower", &conf.node.working_dir);
    follower_conf.node.seed = vec![0x01; 32];
    follower_conf.node.local_peer_seed = vec![0x02; 32];

    let rpc_port = gen_random_port();
    let p2p_port = gen_random_port();

    let localhost = "127.0.0.1";
    follower_conf.node.rpc_bind = format!("{localhost}:{rpc_port}");
    follower_conf.node.p2p_bind = format!("{localhost}:{p2p_port}");
    follower_conf.node.data_url = format!("http://{localhost}:{rpc_port}");
    follower_conf.node.p2p_address = format!("{localhost}:{p2p_port}");

    thread::spawn(move || miner_run_loop.start(None, 0));
    wait_for_runloop(&miner_blocks_processed);

    // figure out the started node's port
    let node_info = get_chain_info(&conf);
    follower_conf.node.add_bootstrap_node(
        &format!(
            "{}@{}",
            &node_info.node_public_key.unwrap(),
            conf.node.p2p_bind
        ),
        CHAIN_ID_TESTNET,
        PEER_VERSION_TESTNET,
    );

    let mut follower_run_loop = neon::RunLoop::new(follower_conf.clone());
    let follower_blocks_processed = follower_run_loop.get_blocks_processed_arc();
    let follower_channel = follower_run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || follower_run_loop.start(None, 0));
    wait_for_runloop(&follower_blocks_processed);

    info!("Follower bootup complete!");

    // first block wakes up the run loop
    next_block_and_wait_all(
        &mut btc_regtest_controller,
        &miner_blocks_processed,
        &[],
        timeout,
    );

    thread::sleep(block_gap);

    // second block will hold our VRF registration
    next_block_and_wait_all(
        &mut btc_regtest_controller,
        &miner_blocks_processed,
        &[&follower_blocks_processed],
        timeout,
    );

    thread::sleep(block_gap);

    // Third block will be the first mined Stacks block.
    next_block_and_wait_all(
        &mut btc_regtest_controller,
        &miner_blocks_processed,
        &[&follower_blocks_processed],
        timeout,
    );

    thread::sleep(block_gap);

    // ---------- Setup finished, start test ----------

    // PART 1
    // Run mock miner configured to output to files

    // Mine some blocks for mock miner output
    for _ in 0..10 {
        next_block_and_wait_all(
            &mut btc_regtest_controller,
            &miner_blocks_processed,
            &[&follower_blocks_processed],
            timeout,
        );
        thread::sleep(block_gap);
    }

    info!("Mock minining finished");

    let miner_blocks_processed_end = miner_channel.get_stacks_blocks_processed();
    let follower_blocks_processed_end = follower_channel.get_stacks_blocks_processed();

    let blocks_dir = follower_conf.node.mock_mining_output_dir.clone().unwrap();
    let file_count = follower_conf
        .node
        .mock_mining_output_dir
        .unwrap()
        .read_dir()
        .unwrap_or_else(|e| panic!("Failed to read directory: {e}"))
        .count();

    // Check that expected output files exist
    assert!(test_dir.is_dir());
    assert!(blocks_dir.is_dir());
    assert_eq!(file_count, 12);
    assert_eq!(miner_blocks_processed_end, follower_blocks_processed_end);

    // PART 2
    // Run `mock_miner_replay()`
    let blocks_dir = blocks_dir.into_os_string().into_string().unwrap();
    let db_path = format!("{}/neon", conf.node.working_dir);
    let args: Vec<String> = vec!["replay-mock-mining".into(), db_path, blocks_dir];

    info!("Replaying mock mined blocks...");
    cli::command_replay_mock_mining(&args, Some(&conf));

    // ---------- Test finished, clean up ----------

    miner_channel.stop_chains_coordinator();
    follower_channel.stop_chains_coordinator();
}

#[test]
#[ignore]
/// Verify that the config option, `burnchain.max_unspent_utxos`, is respected.
fn listunspent_max_utxos() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();
    let prom_port = gen_random_port();
    let localhost = "127.0.0.1";
    let prom_bind = format!("{localhost}:{prom_port}");
    conf.node.prometheus_bind = Some(prom_bind);

    conf.burnchain.max_rbf = 1000000;
    conf.burnchain.max_unspent_utxos = Some(10);

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let keychain = Keychain::default(conf.node.seed.clone());
    let mut op_signer = keychain.generate_op_signer();

    let (_, network_id) = conf.burnchain.get_bitcoin_network();
    let hash160 = Hash160::from_data(&op_signer.get_public_key().to_bytes());
    let address = BitcoinAddress::from_bytes_legacy(
        network_id,
        LegacyBitcoinAddressType::PublicKeyHash,
        &hash160.0,
    )
    .expect("Public key incorrect");

    let filter_addresses = vec![addr2str(&address)];

    let res = BitcoinRPCRequest::list_unspent(&conf, filter_addresses, false, 1, &None, 0);
    let utxos = res.expect("Failed to get utxos");
    assert_eq!(utxos.num_utxos(), 10);
}

#[test]
#[ignore]
/// Test out stopping bitcoind and restarting it
fn start_stop_bitcoind() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();
    let prom_port = gen_random_port();
    let localhost = "127.0.0.1";
    let prom_bind = format!("{localhost}:{prom_port}");
    conf.node.prometheus_bind = Some(prom_bind);

    conf.burnchain.max_rbf = 1000000;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf, None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    btcd_controller
        .stop_bitcoind()
        .expect("Failed to stop bitcoind");

    thread::sleep(Duration::from_secs(5));

    btcd_controller
        .start_bitcoind()
        .expect("Failed to start bitcoind");

    btcd_controller
        .stop_bitcoind()
        .expect("Failed to stop bitcoind");
}
