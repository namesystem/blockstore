// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
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
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use std::time::Instant;
use std::{cmp, fs, mem};

use clarity::vm::analysis::{CheckError, CheckErrors};
use clarity::vm::ast::errors::ParseErrors;
use clarity::vm::ast::ASTRules;
use clarity::vm::clarity::TransactionConnection;
use clarity::vm::database::BurnStateDB;
use clarity::vm::errors::Error as InterpreterError;
use clarity::vm::types::TypeSignature;
use serde::Deserialize;
use stacks_common::codec::{read_next, write_next, StacksMessageCodec};
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksAddress, StacksBlockId, StacksWorkScore, TrieHash,
};
use stacks_common::types::StacksPublicKeyBuffer;
use stacks_common::util::get_epoch_time_ms;
use stacks_common::util::hash::{MerkleTree, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{MessageSignature, Secp256k1PrivateKey};
use stacks_common::util::vrf::*;

use crate::burnchains::{Burnchain, PrivateKey, PublicKey};
use crate::chainstate::burn::db::sortdb::{
    SortitionDB, SortitionDBConn, SortitionHandleConn, SortitionHandleTx,
};
use crate::chainstate::burn::operations::*;
use crate::chainstate::burn::*;
use crate::chainstate::stacks::address::StacksAddressExtensions;
use crate::chainstate::stacks::db::blocks::{MemPoolRejection, SetupBlockResult};
use crate::chainstate::stacks::db::transactions::{
    handle_clarity_runtime_error, ClarityRuntimeTxError,
};
use crate::chainstate::stacks::db::unconfirmed::UnconfirmedState;
use crate::chainstate::stacks::db::{
    ChainstateTx, ClarityTx, MinerRewardInfo, StacksChainState, MINER_REWARD_MATURITY,
};
use crate::chainstate::stacks::events::{StacksTransactionEvent, StacksTransactionReceipt};
use crate::chainstate::stacks::{Error, StacksBlockHeader, StacksMicroblockHeader, *};
use crate::clarity_vm::clarity::{ClarityConnection, ClarityInstance, Error as clarity_error};
use crate::core::mempool::*;
use crate::core::*;
use crate::cost_estimates::metrics::CostMetric;
use crate::cost_estimates::CostEstimator;
use crate::monitoring::{
    set_last_mined_block_transaction_count, set_last_mined_execution_cost_observed,
};
use crate::net::relay::Relayer;
use crate::net::Error as net_error;

/// Fully-assembled Stacks anchored, block as well as some extra metadata pertaining to how it was
/// linked to the burnchain and what view(s) the miner had of the burnchain before and after
/// completing the block.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssembledAnchorBlock {
    /// Consensus hash of the parent Stacks block
    pub parent_consensus_hash: ConsensusHash,
    /// Consensus hash this Stacks block
    pub consensus_hash: ConsensusHash,
    /// Burnchain tip's block hash when we finished mining
    pub burn_hash: BurnchainHeaderHash,
    /// Burnchain tip's block height when we finished mining
    pub burn_block_height: u64,
    /// Burnchain tip's block hash when we started mining (could be different)
    pub orig_burn_hash: BurnchainHeaderHash,
    /// The block we produced
    pub anchored_block: StacksBlock,
    /// The attempt count of this block (multiple blocks will be attempted per burnchain block)
    pub attempt: u64,
    /// Epoch timestamp in milliseconds when we started producing the block.
    pub tenure_begin: u128,
}
impl_file_io_serde_json!(AssembledAnchorBlock);

/// System status for mining.
/// The miner can be Ready, in which case a miner is allowed to run
/// The miner can be Blocked, in which case the miner *should not start* and/or *should terminate*
/// if running.
/// The inner u64 is a per-thread ID that lets threads querying the miner status identify whether
/// or not they or another thread were the last to modify the state.
#[derive(Debug, Clone, PartialEq)]
pub struct MinerStatus {
    blockers: HashSet<ThreadId>,
    spend_amount: u64,
}

impl MinerStatus {
    pub fn make_ready(spend_amount: u64) -> MinerStatus {
        MinerStatus {
            blockers: HashSet::new(),
            spend_amount,
        }
    }

    pub fn add_blocked(&mut self) {
        self.blockers.insert(std::thread::current().id());
    }

    pub fn remove_blocked(&mut self) {
        self.blockers.remove(&std::thread::current().id());
    }

    pub fn is_blocked(&self) -> bool {
        if !self.blockers.is_empty() {
            debug!("Miner: blocked by {:?}", &self.blockers);
            true
        } else {
            false
        }
    }

    pub fn get_spend_amount(&self) -> u64 {
        return self.spend_amount;
    }

    pub fn set_spend_amount(&mut self, amt: u64) {
        self.spend_amount = amt;
    }
}

impl std::fmt::Display for MinerStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self)
    }
}

/// halt mining
pub fn signal_mining_blocked(miner_status: Arc<Mutex<MinerStatus>>) {
    debug!("Signaling miner to block"; "thread_id" => ?std::thread::current().id());
    match miner_status.lock() {
        Ok(mut status) => {
            status.add_blocked();
        }
        Err(_e) => {
            panic!("FATAL: mutex poisoned");
        }
    }
}

/// resume mining if we blocked it earlier
pub fn signal_mining_ready(miner_status: Arc<Mutex<MinerStatus>>) {
    debug!("Signaling miner to resume"; "thread_id" => ?std::thread::current().id());
    match miner_status.lock() {
        Ok(mut status) => {
            status.remove_blocked();
        }
        Err(_e) => {
            panic!("FATAL: mutex poisoned");
        }
    }
}

/// get the mining amount
pub fn get_mining_spend_amount(miner_status: Arc<Mutex<MinerStatus>>) -> u64 {
    match miner_status.lock() {
        Ok(status) => status.get_spend_amount(),
        Err(_e) => {
            panic!("FATAL: mutex poisoned");
        }
    }
}

/// set the mining amount
pub fn set_mining_spend_amount(miner_status: Arc<Mutex<MinerStatus>>, amt: u64) {
    miner_status
        .lock()
        .expect("FATAL: mutex poisoned")
        .set_spend_amount(amt);
}

/// Policy settings for how mining will proceed
#[derive(Debug, Clone)]
pub struct BlockBuilderSettings {
    pub max_miner_time_ms: u64,
    pub mempool_settings: MemPoolWalkSettings,
    pub miner_status: Arc<Mutex<MinerStatus>>,
    /// Should the builder attempt to confirm any parent microblocks
    pub confirm_microblocks: bool,
}

impl BlockBuilderSettings {
    // TODO: add tests from mutation testing results #4873
    #[cfg_attr(test, mutants::skip)]
    pub fn limited() -> BlockBuilderSettings {
        BlockBuilderSettings {
            max_miner_time_ms: u64::MAX,
            mempool_settings: MemPoolWalkSettings::default(),
            miner_status: Arc::new(Mutex::new(MinerStatus::make_ready(0))),
            confirm_microblocks: true,
        }
    }

    // TODO: add tests from mutation testing results #4873
    #[cfg_attr(test, mutants::skip)]
    pub fn max_value() -> BlockBuilderSettings {
        BlockBuilderSettings {
            max_miner_time_ms: u64::MAX,
            mempool_settings: MemPoolWalkSettings::zero(),
            miner_status: Arc::new(Mutex::new(MinerStatus::make_ready(0))),
            confirm_microblocks: true,
        }
    }
}

#[derive(Clone)]
struct MicroblockMinerRuntime {
    bytes_so_far: u64,
    pub prev_microblock_header: Option<StacksMicroblockHeader>,
    considered: Option<HashSet<Txid>>,
    num_mined: u64,
    tip: StacksBlockId,

    // fault injection, inherited from unconfirmed
    disable_bytes_check: bool,
    disable_cost_check: bool,
}

/// The value of `BlockLimitFunction` holds the state of the size of the block being built.
/// As the value increases, the less we can add to blocks.
#[derive(PartialEq)]
pub enum BlockLimitFunction {
    /// The block size limit has not been hit, and there are no restrictions on what can be added to
    /// a block.
    NO_LIMIT_HIT,
    /// We have got a pretty full block, and so will not allow any more contract call or
    /// contract publish transactions to be added to this block.
    CONTRACT_LIMIT_HIT,
    /// We have a completely full block. No new transactions can be added to the block.
    LIMIT_REACHED,
}

pub struct MinerEpochInfo<'a> {
    pub chainstate_tx: ChainstateTx<'a>,
    pub clarity_instance: &'a mut ClarityInstance,
    pub burn_tip: BurnchainHeaderHash,
    /// This is the expected burn tip height (i.e., the current burnchain tip + 1)
    ///  of the mined block
    pub burn_tip_height: u32,
    pub parent_microblocks: Vec<StacksMicroblock>,
    pub mainnet: bool,
    pub ast_rules: ASTRules,
}

impl From<&UnconfirmedState> for MicroblockMinerRuntime {
    fn from(unconfirmed: &UnconfirmedState) -> MicroblockMinerRuntime {
        let considered = unconfirmed.mined_txs.keys().cloned().collect();
        MicroblockMinerRuntime {
            bytes_so_far: unconfirmed.bytes_so_far,
            prev_microblock_header: unconfirmed.last_mblock.clone(),
            considered: Some(considered),
            num_mined: 0,
            tip: unconfirmed.confirmed_chain_tip.clone(),

            disable_bytes_check: unconfirmed.disable_bytes_check,
            disable_cost_check: unconfirmed.disable_cost_check,
        }
    }
}

/// Represents a successful transaction. This transaction should be added to the block.
#[derive(Debug, Clone, PartialEq)]
pub struct TransactionSuccess {
    pub tx: StacksTransaction,
    /// The fee that was charged to the user for doing this transaction.
    pub fee: u64,
    pub receipt: StacksTransactionReceipt,
    /// Whether the soft limit was reached after this transaction was processed.
    pub soft_limit_reached: bool,
}

/// Represents a failed transaction. Something went wrong when processing this transaction.
#[derive(Debug)]
pub struct TransactionError {
    pub tx: StacksTransaction,
    pub error: Error,
}

/// Represents a transaction that was skipped, but might succeed later.
#[derive(Debug)]
pub struct TransactionSkipped {
    pub tx: StacksTransaction,
    /// This error is the reason the transaction was skipped (ex: BlockTooBigError)
    pub error: Error,
}

/// Represents a transaction that is problematic and should be dropped.
#[derive(Debug)]
pub struct TransactionProblematic {
    pub tx: StacksTransaction,
    pub error: Error,
}

/// Represents an event for a successful transaction. This transaction should be added to the block.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransactionSuccessEvent {
    #[serde(deserialize_with = "hex_deserialize", serialize_with = "hex_serialize")]
    pub txid: Txid,
    pub fee: u64,
    pub execution_cost: ExecutionCost,
    pub result: Value,
    pub soft_limit_reached: bool,
}

/// Represents an event for a failed transaction. Something went wrong when processing this transaction.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TransactionErrorEvent {
    #[serde(deserialize_with = "hex_deserialize", serialize_with = "hex_serialize")]
    pub txid: Txid,
    pub error: String,
}

/// Represents an event for a transaction that was skipped, but might succeed later.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransactionSkippedEvent {
    #[serde(deserialize_with = "hex_deserialize", serialize_with = "hex_serialize")]
    pub txid: Txid,
    pub error: String,
}

/// Represents an event for a transaction that needs to be dropped from the mempool for some reason
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransactionProblematicEvent {
    #[serde(deserialize_with = "hex_deserialize", serialize_with = "hex_serialize")]
    pub txid: Txid,
    pub error: String,
}

fn hex_serialize<S: serde::Serializer>(txid: &Txid, s: S) -> Result<S::Ok, S::Error> {
    let inst = txid.to_hex();
    s.serialize_str(inst.as_str())
}

fn hex_deserialize<'de, D: serde::Deserializer<'de>>(d: D) -> Result<Txid, D::Error> {
    let inst_str = String::deserialize(d)?;
    Txid::from_hex(&inst_str).map_err(serde::de::Error::custom)
}

/// `TransactionResult` represents the outcome of transaction processing.
/// We use this enum to involve the compiler in forcing us to always clearly
/// indicate the outcome of a transaction.
///
/// There are currently three outcomes for a transaction:
/// 1) succeed
/// 2) fail, may be tried again later
/// 3) be skipped for now, to be tried again later
#[derive(Debug)]
pub enum TransactionResult {
    /// Transaction has already succeeded.
    Success(TransactionSuccess),
    /// Transaction failed when processed.
    ProcessingError(TransactionError),
    /// Transaction wasn't ready to be processed, but might succeed later.
    Skipped(TransactionSkipped),
    /// Transaction is problematic (e.g. a DDoS vector) and should be dropped.
    /// This error variant is a placeholder for fixing Clarity VM quirks in the next network
    /// upgrade.
    Problematic(TransactionProblematic),
}

/// This struct is used to transmit data about transaction results through either the `mined_block`
/// or `mined_microblock` event.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum TransactionEvent {
    /// Transaction has already succeeded.
    Success(TransactionSuccessEvent),
    /// Transaction failed. It may succeed later depending on the error.
    ProcessingError(TransactionErrorEvent),
    /// Transaction wasn't ready to be processed, but might succeed later.
    /// The bool represents whether mempool propagation should halt or continue
    Skipped(TransactionSkippedEvent),
    /// Transaction is problematic and will be dropped
    Problematic(TransactionProblematicEvent),
}

impl TransactionResult {
    /// Logs a queryable message for the case where `txid` has succeeded.
    pub fn log_transaction_success(tx: &StacksTransaction) {
        info!("Tx successfully processed.";
            "event_name" => %"transaction_result",
            "tx_id" => %tx.txid(),
            "event_type" => %"success",
        );
    }

    /// Logs a queryable message for the case where `txid` has failed
    /// with error `err`.
    pub fn log_transaction_error(tx: &StacksTransaction, err: &Error) {
        info!("Tx processing failed with error";
            "event_name" => "transaction_result",
            "reason" => %err,
            "tx_id" => %tx.txid(),
            "event_type" => "error",
        );
    }

    /// Logs a queryable message for the case where `tx` has been skipped
    /// for error `err`.
    pub fn log_transaction_skipped(tx: &StacksTransaction, err: &Error) {
        info!(
            "Tx processing skipped";
            "event_name" => "transaction_result",
            "tx_id" => %tx.txid(),
            "event_type" => "skip",
            "reason" => %err,
        );
    }

    /// Logs a queryable message for the case where `tx` is problematic and needs to be dropped.
    pub fn log_transaction_problematic(tx: &StacksTransaction, err: &Error) {
        info!(
            "Tx processing problematic";
            "event_name" => "transaction_result",
            "tx_id" => %tx.txid(),
            "event_type" => "problematic",
            "reason" => %err,
        )
    }

    /// Creates a `TransactionResult` backed by `TransactionSuccess`.
    /// This method logs "transaction success" as a side effect.
    pub fn success(
        transaction: &StacksTransaction,
        fee: u64,
        receipt: StacksTransactionReceipt,
    ) -> TransactionResult {
        Self::log_transaction_success(transaction);
        Self::Success(TransactionSuccess {
            tx: transaction.clone(),
            fee,
            receipt,
            soft_limit_reached: false,
        })
    }

    /// Creates a `TransactionResult` backed by `TransactionSuccess` with a soft limit reached.
    /// This method logs "transaction success" as a side effect.
    pub fn success_with_soft_limit(
        transaction: &StacksTransaction,
        fee: u64,
        receipt: StacksTransactionReceipt,
        soft_limit_reached: bool,
    ) -> TransactionResult {
        Self::log_transaction_success(transaction);
        Self::Success(TransactionSuccess {
            tx: transaction.clone(),
            fee,
            receipt,
            soft_limit_reached,
        })
    }

    /// Creates a `TransactionResult` backed by `TransactionError`.
    /// This method logs "transaction error" as a side effect.
    pub fn error(transaction: &StacksTransaction, error: Error) -> TransactionResult {
        Self::log_transaction_error(transaction, &error);
        TransactionResult::ProcessingError(TransactionError {
            tx: transaction.clone(),
            error,
        })
    }

    /// Creates a `TransactionResult` backed by `TransactionSkipped`.
    /// This method logs "transaction skipped" as a side effect.
    /// Takes in a reason (String) and uses the default error type for
    /// skipped transactions, `StacksTransactionSkipped` for the associated error.
    pub fn skipped(transaction: &StacksTransaction, reason: String) -> TransactionResult {
        let error = Error::StacksTransactionSkipped(reason);
        Self::log_transaction_skipped(transaction, &error);
        TransactionResult::Skipped(TransactionSkipped {
            tx: transaction.clone(),
            error,
        })
    }

    /// Creates a `TransactionResult` backed by `TransactionSkipped`.
    /// This method logs "transaction skipped" as a side effect.
    pub fn skipped_due_to_error(
        transaction: &StacksTransaction,
        error: Error,
    ) -> TransactionResult {
        Self::log_transaction_skipped(transaction, &error);
        TransactionResult::Skipped(TransactionSkipped {
            tx: transaction.clone(),
            error,
        })
    }

    /// Creates a `TransactionResult` backed by `TransactionProblematic`.
    /// This method logs "transaction problematic" as a side effect.
    pub fn problematic(transaction: &StacksTransaction, error: Error) -> TransactionResult {
        Self::log_transaction_problematic(transaction, &error);
        TransactionResult::Problematic(TransactionProblematic {
            tx: transaction.clone(),
            error,
        })
    }

    pub fn convert_to_event(&self) -> TransactionEvent {
        match &self {
            TransactionResult::Success(TransactionSuccess {
                tx,
                fee,
                receipt,
                soft_limit_reached,
            }) => TransactionEvent::Success(TransactionSuccessEvent {
                txid: tx.txid(),
                fee: *fee,
                execution_cost: receipt.execution_cost.clone(),
                result: receipt.result.clone(),
                soft_limit_reached: *soft_limit_reached,
            }),
            TransactionResult::ProcessingError(TransactionError { tx, error }) => {
                TransactionEvent::ProcessingError(TransactionErrorEvent {
                    txid: tx.txid(),
                    error: error.to_string(),
                })
            }
            TransactionResult::Skipped(TransactionSkipped { tx, error }) => {
                TransactionEvent::Skipped(TransactionSkippedEvent {
                    txid: tx.txid(),
                    error: error.to_string(),
                })
            }
            TransactionResult::Problematic(TransactionProblematic { tx, error }) => {
                TransactionEvent::Problematic(TransactionProblematicEvent {
                    txid: tx.txid(),
                    error: error.to_string(),
                })
            }
        }
    }

    /// Returns true iff this enum is backed by `TransactionSuccess`.
    pub fn is_ok(&self) -> bool {
        matches!(self, TransactionResult::Success(_))
    }

    /// Returns a TransactionSuccess result as a pair of 1) fee and 2) receipt.
    /// Otherwise crashes.
    pub fn unwrap(self) -> (u64, StacksTransactionReceipt) {
        match self {
            TransactionResult::Success(TransactionSuccess { fee, receipt, .. }) => (fee, receipt),
            _ => panic!("Tried to `unwrap` a non-success result."),
        }
    }

    /// Returns true iff this enum is backed by `Error`.
    pub fn is_err(&self) -> bool {
        matches!(self, TransactionResult::ProcessingError(_))
    }

    /// Returns an Error result as an Error.
    /// Otherwise crashes.
    pub fn unwrap_err(self) -> Error {
        match self {
            TransactionResult::ProcessingError(TransactionError { tx: _, error }) => error,
            _ => panic!("Tried to `unwrap_error` a non-error result."),
        }
    }

    /// Is a given transaction-processing error evidence of a problematic transaction?
    /// We can't clone() the error, nor use a reference, so we have to return it.
    /// Returns (true, error) if so
    /// Returns (false, error) if none
    pub fn is_problematic(
        tx: &StacksTransaction,
        error: Error,
        epoch_id: StacksEpochId,
    ) -> (bool, Error) {
        let error = match error {
            Error::ClarityError(e) => match handle_clarity_runtime_error(e) {
                ClarityRuntimeTxError::Rejectable(e) => {
                    // this transaction would invalidate the whole block, so don't re-consider it
                    info!("Problematic transaction would invalidate the block, so dropping from mempool"; "txid" => %tx.txid(), "error" => %e);
                    return (true, Error::ClarityError(e));
                }
                // recover original ClarityError
                ClarityRuntimeTxError::Acceptable { error, .. } => {
                    if let clarity_error::Parse(ref parse_err) = error {
                        info!("Parse error: {}", parse_err; "txid" => %tx.txid());
                        match &parse_err.err {
                            ParseErrors::ExpressionStackDepthTooDeep
                            | ParseErrors::VaryExpressionStackDepthTooDeep => {
                                info!("Problematic transaction failed AST depth check"; "txid" => %tx.txid());
                                return (true, Error::ClarityError(error));
                            }
                            _ => {}
                        }
                    }
                    Error::ClarityError(error)
                }
                ClarityRuntimeTxError::CostError(cost, budget) => {
                    Error::ClarityError(clarity_error::CostError(cost, budget))
                }
                ClarityRuntimeTxError::AnalysisError(e) => {
                    let clarity_err = Error::ClarityError(clarity_error::Interpreter(
                        InterpreterError::Unchecked(e),
                    ));
                    if epoch_id < StacksEpochId::Epoch21 {
                        // this would invalidate the block, so it's problematic
                        return (true, clarity_err);
                    } else {
                        // in 2.1 and later, this can be mined
                        clarity_err
                    }
                }
                ClarityRuntimeTxError::AbortedByCallback(val, assets, events) => {
                    Error::ClarityError(clarity_error::AbortedByCallback(val, assets, events))
                }
            },
            Error::InvalidFee => {
                // The transaction didn't have enough STX left over after it was run.
                // While such a transaction *could* be mineable in the future, e.g. depending on
                // which code paths were hit, the user should really have attached an appropriate
                // tx fee in the first place.  In Stacks 2.1, the code will debit the fee first, so
                // this will no longer be an issue.
                info!("Problematic transaction caused InvalidFee";
                      "txid" => %tx.txid(),
                      "origin" => %tx.get_origin().get_address(false),
                      "payload" => ?tx.payload,
                );
                return (true, Error::InvalidFee);
            }
            e => e,
        };
        (false, error)
    }
}

/// Trait that defines what it means to be a block builder
pub trait BlockBuilder {
    fn try_mine_tx_with_len(
        &mut self,
        clarity_tx: &mut ClarityTx,
        tx: &StacksTransaction,
        tx_len: u64,
        limit_behavior: &BlockLimitFunction,
        ast_rules: ASTRules,
    ) -> TransactionResult;

    /// Append a transaction if doing so won't exceed the epoch data size.
    /// Errors out if we fail to mine the tx (exceed budget, or the transaction is invalid).
    fn try_mine_tx(
        &mut self,
        clarity_tx: &mut ClarityTx,
        tx: &StacksTransaction,
        ast_rules: ASTRules,
    ) -> Result<TransactionResult, Error> {
        let tx_len = tx.tx_len();
        match self.try_mine_tx_with_len(
            clarity_tx,
            tx,
            tx_len,
            &BlockLimitFunction::NO_LIMIT_HIT,
            ast_rules,
        ) {
            TransactionResult::Success(s) => Ok(TransactionResult::Success(s)),
            TransactionResult::Skipped(TransactionSkipped { error, .. })
            | TransactionResult::ProcessingError(TransactionError { error, .. }) => Err(error),
            TransactionResult::Problematic(TransactionProblematic { tx, .. }) => {
                Err(Error::ProblematicTransaction(tx.txid()))
            }
        }
    }
}

///
///    Independent structure for building microblocks:
///       StacksBlockBuilder cannot be used, since microblocks should only be broadcasted
///       once the anchored block is mined, won sortition, and a StacksBlockBuilder will
///       not survive that long.
///
///     StacksMicroblockBuilder holds a mutable reference to the provided chainstate in the
///       new function. This is required for the `clarity_tx` -- basically, to append transactions
///       as new microblocks, the builder _needs_ to be able to keep the current clarity_tx "open"
pub struct StacksMicroblockBuilder<'a> {
    anchor_block: BlockHeaderHash,
    anchor_block_consensus_hash: ConsensusHash,
    anchor_block_height: u64,
    header_reader: StacksChainState,
    clarity_tx: Option<ClarityTx<'a, 'a>>,
    unconfirmed: bool,
    runtime: MicroblockMinerRuntime,
    settings: BlockBuilderSettings,
    ast_rules: ASTRules,
}

impl<'a> StacksMicroblockBuilder<'a> {
    pub fn new(
        anchor_block: BlockHeaderHash,
        anchor_block_consensus_hash: ConsensusHash,
        chainstate: &'a mut StacksChainState,
        burn_dbconn: &'a dyn BurnStateDB,
        settings: BlockBuilderSettings,
    ) -> Result<StacksMicroblockBuilder<'a>, Error> {
        let runtime = if let Some(unconfirmed_state) = chainstate.unconfirmed_state.as_ref() {
            MicroblockMinerRuntime::from(unconfirmed_state)
        } else {
            warn!("No unconfirmed state instantiated; cannot mine microblocks");
            return Err(Error::NoSuchBlockError);
        };

        let (header_reader, _) = chainstate.reopen()?;
        let anchor_block_header = StacksChainState::get_anchored_block_header_info(
            header_reader.db(),
            &anchor_block_consensus_hash,
            &anchor_block,
        )?
        .ok_or_else(|| {
            warn!(
                "No such block: {}/{}",
                &anchor_block_consensus_hash, &anchor_block
            );
            Error::NoSuchBlockError
        })?;
        let anchor_block_height = anchor_block_header.stacks_block_height;
        let burn_height = anchor_block_header.burn_header_height;
        let ast_rules = burn_dbconn.get_ast_rules(burn_height);

        // when we drop the miner, the underlying clarity instance will be rolled back
        chainstate.set_unconfirmed_dirty(true);

        // find parent block's execution cost
        let parent_index_hash =
            StacksBlockHeader::make_index_block_hash(&anchor_block_consensus_hash, &anchor_block);
        let cost_so_far =
            StacksChainState::get_stacks_block_anchored_cost(chainstate.db(), &parent_index_hash)?
                .ok_or(Error::NoSuchBlockError)?;

        // We need to open the chainstate _after_ any possible errors could occur, otherwise, we'd have opened
        //  the chainstate, but will lose the reference to the clarity_tx before the Drop handler for StacksMicroblockBuilder
        //  could take over.
        let mut clarity_tx = chainstate.block_begin(
            burn_dbconn,
            &anchor_block_consensus_hash,
            &anchor_block,
            &MINER_BLOCK_CONSENSUS_HASH,
            &MINER_BLOCK_HEADER_HASH,
        );

        debug!(
            "Begin microblock mining from {} from unconfirmed state with cost {:?}",
            &StacksBlockHeader::make_index_block_hash(&anchor_block_consensus_hash, &anchor_block),
            &cost_so_far
        );
        clarity_tx.reset_cost(cost_so_far);

        Ok(StacksMicroblockBuilder {
            anchor_block,
            anchor_block_consensus_hash,
            anchor_block_height,
            runtime,
            clarity_tx: Some(clarity_tx),
            header_reader,
            unconfirmed: false,
            settings,
            ast_rules,
        })
    }

    /// Create a microblock miner off of the _unconfirmed_ chaintip, i.e., resuming construction of
    /// a microblock stream.
    pub fn resume_unconfirmed(
        chainstate: &'a mut StacksChainState,
        burn_dbconn: &'a dyn BurnStateDB,
        cost_so_far: &ExecutionCost,
        settings: BlockBuilderSettings,
    ) -> Result<StacksMicroblockBuilder<'a>, Error> {
        let runtime = if let Some(unconfirmed_state) = chainstate.unconfirmed_state.as_ref() {
            MicroblockMinerRuntime::from(unconfirmed_state)
        } else {
            warn!("No unconfirmed state instantiated; cannot mine microblocks");
            return Err(Error::NoSuchBlockError);
        };

        let (header_reader, _) = chainstate.reopen()?;
        let (
            anchored_consensus_hash,
            anchored_block_hash,
            anchored_block_height,
            anchored_burn_height,
        ) = if let Some(unconfirmed) = chainstate.unconfirmed_state.as_ref() {
            let header_info = StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                chainstate.db(),
                &unconfirmed.confirmed_chain_tip,
            )?
            .ok_or_else(|| {
                warn!(
                    "No such confirmed block {}",
                    &unconfirmed.confirmed_chain_tip
                );
                Error::NoSuchBlockError
            })?;
            (
                header_info.consensus_hash,
                header_info.anchored_header.block_hash(),
                header_info.stacks_block_height,
                header_info.burn_header_height,
            )
        } else {
            // unconfirmed state needs to be initialized
            debug!("Unconfirmed chainstate not initialized");
            return Err(Error::NoSuchBlockError)?;
        };

        let ast_rules = burn_dbconn.get_ast_rules(anchored_burn_height);

        let mut clarity_tx = chainstate.begin_unconfirmed(burn_dbconn).ok_or_else(|| {
            warn!(
                "Failed to begin-unconfirmed on {}/{}",
                &anchored_consensus_hash, &anchored_block_hash
            );
            Error::NoSuchBlockError
        })?;

        debug!(
            "Resume microblock mining from {} from unconfirmed state with cost {:?}",
            &StacksBlockHeader::make_index_block_hash(
                &anchored_consensus_hash,
                &anchored_block_hash
            ),
            cost_so_far
        );
        clarity_tx.reset_cost(cost_so_far.clone());

        Ok(StacksMicroblockBuilder {
            anchor_block: anchored_block_hash,
            anchor_block_consensus_hash: anchored_consensus_hash,
            anchor_block_height: anchored_block_height,
            runtime,
            clarity_tx: Some(clarity_tx),
            header_reader,
            unconfirmed: true,
            settings,
            ast_rules,
        })
    }

    /// Produce a microblock, given its parent.
    /// No accounting state will be updated.
    pub fn make_next_microblock_from_txs(
        txs: Vec<StacksTransaction>,
        miner_key: &Secp256k1PrivateKey,
        parent_anchor_block_hash: &BlockHeaderHash,
        prev_microblock_header: Option<&StacksMicroblockHeader>,
        ast_rules: ASTRules,
    ) -> Result<StacksMicroblock, Error> {
        let miner_pubkey_hash =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(miner_key));
        if txs.is_empty() {
            return Err(Error::NoTransactionsToMine);
        }

        let txid_vecs: Vec<_> = txs.iter().map(|tx| tx.txid().as_bytes().to_vec()).collect();

        let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
        let tx_merkle_root = merkle_tree.root();
        let mut next_microblock_header = if let Some(prev_microblock) = prev_microblock_header {
            StacksMicroblockHeader::from_parent_unsigned(prev_microblock, &tx_merkle_root)
                .ok_or(Error::MicroblockStreamTooLongError)?
        } else {
            // .prev_block is the hash of the parent anchored block
            StacksMicroblockHeader::first_unsigned(parent_anchor_block_hash, &tx_merkle_root)
        };

        if ast_rules != ASTRules::Typical {
            next_microblock_header.version = cmp::max(
                STACKS_BLOCK_VERSION_AST_PRECHECK_SIZE,
                next_microblock_header.version,
            );
        }

        next_microblock_header.sign(miner_key).unwrap();
        next_microblock_header.verify(&miner_pubkey_hash).unwrap();
        Ok(StacksMicroblock {
            header: next_microblock_header,
            txs,
        })
    }

    /// Produce the next microblock in the stream, unconditionally, from the given txs.
    /// Inner accouting state, like runtime and space, will be updated.
    /// Otherwise, no validity checking will be done.
    pub fn make_next_microblock(
        &mut self,
        txs: Vec<StacksTransaction>,
        miner_key: &Secp256k1PrivateKey,
        tx_events: Vec<TransactionEvent>,
        event_dispatcher: Option<&dyn MemPoolEventDispatcher>,
    ) -> Result<StacksMicroblock, Error> {
        let microblock = StacksMicroblockBuilder::make_next_microblock_from_txs(
            txs,
            miner_key,
            &self.anchor_block,
            self.runtime.prev_microblock_header.as_ref(),
            self.ast_rules,
        )?;
        self.runtime.prev_microblock_header = Some(microblock.header.clone());

        if let Some(dispatcher) = event_dispatcher {
            dispatcher.mined_microblock_event(
                &microblock,
                tx_events,
                self.anchor_block_consensus_hash,
                self.anchor_block,
            )
        }

        info!(
            "Miner: Created microblock block {} (seq={}) off of {}/{}: {} transaction(s)",
            microblock.block_hash(),
            microblock.header.sequence,
            self.anchor_block_consensus_hash,
            self.anchor_block,
            microblock.txs.len()
        );
        Ok(microblock)
    }

    /// Mine the next transaction into a microblock.
    /// Returns Ok(TransactionResult::Success) if the transaction was mined into this microblock.
    /// Returns Ok(TransactionResult::Skipped) if the transaction was not mined, but can be mined later.
    /// Returns Ok(TransactionResult::Error) if the transaction was not mined due to an error.
    /// Returns Ok(TransactionResult::Problematic) if the transaction should be dropped from the mempool.
    /// Returns Err(e) if an error occurs during the function.
    ///
    /// This calls `StacksChainState::process_transaction` and also checks certain pre-conditions
    /// and handles errors.
    ///
    /// # Pre-Checks
    /// - skip if the `anchor_mode` rules out micro-blocks
    /// - skip if 'tx.txid()` is already in `considered`
    /// - skip if adding the block would result in a block size bigger than `MAX_EPOCH_SIZE`
    ///
    /// # Error Handling
    /// - If the error when processing a tx is `CostOverflowError`, reset the cost of the block.
    fn mine_next_transaction(
        clarity_tx: &mut ClarityTx,
        tx: StacksTransaction,
        tx_len: u64,
        bytes_so_far: u64,
        limit_behavior: &BlockLimitFunction,
        ast_rules: ASTRules,
    ) -> Result<TransactionResult, Error> {
        if tx.anchor_mode != TransactionAnchorMode::OffChainOnly
            && tx.anchor_mode != TransactionAnchorMode::Any
        {
            return Ok(TransactionResult::skipped_due_to_error(
                &tx,
                Error::InvalidStacksTransaction(
                    "Invalid transaction anchor mode for streamed data".to_string(),
                    false,
                ),
            ));
        }

        if bytes_so_far + tx_len >= MAX_EPOCH_SIZE.into() {
            info!(
                "Adding microblock tx {} would exceed epoch data size",
                &tx.txid()
            );
            return Ok(TransactionResult::skipped_due_to_error(
                &tx,
                Error::BlockTooBigError,
            ));
        }
        match limit_behavior {
            BlockLimitFunction::CONTRACT_LIMIT_HIT => {
                match &tx.payload {
                    TransactionPayload::ContractCall(cc) => {
                        // once we've hit the runtime limit once, allow boot code contract calls, but do not try to eval
                        //   other contract calls
                        if !cc.address.is_boot_code_addr() {
                            return Ok(TransactionResult::skipped(
                                &tx,
                                "BlockLimitFunction::CONTRACT_LIMIT_HIT".to_string(),
                            ));
                        }
                    }
                    TransactionPayload::SmartContract(..) => {
                        return Ok(TransactionResult::skipped(
                            &tx,
                            "BlockLimitFunction::CONTRACT_LIMIT_HIT".to_string(),
                        ));
                    }
                    _ => {}
                }
            }
            BlockLimitFunction::LIMIT_REACHED => {
                return Ok(TransactionResult::skipped(
                    &tx,
                    "BlockLimitFunction::LIMIT_REACHED".to_string(),
                ))
            }
            BlockLimitFunction::NO_LIMIT_HIT => {}
        };

        // preemptively skip problematic transactions
        if let Err(e) = Relayer::static_check_problematic_relayed_tx(
            clarity_tx.config.mainnet,
            clarity_tx.get_epoch(),
            &tx,
            ast_rules,
        ) {
            info!(
                "Detected problematic tx {} while mining; dropping from mempool",
                tx.txid()
            );
            return Ok(TransactionResult::problematic(&tx, Error::NetError(e)));
        }

        let quiet = !cfg!(test);
        match StacksChainState::process_transaction(clarity_tx, &tx, quiet, ast_rules) {
            Ok((fee, receipt)) => Ok(TransactionResult::success(&tx, fee, receipt)),
            Err(e) => {
                let (is_problematic, e) =
                    TransactionResult::is_problematic(&tx, e, clarity_tx.get_epoch());
                if is_problematic {
                    Ok(TransactionResult::problematic(&tx, e))
                } else {
                    match &e {
                        Error::CostOverflowError(cost_before, cost_after, total_budget) => {
                            // note: this path _does_ not perform the tx block budget % heuristic,
                            //  because this code path is not directly called with a mempool handle.
                            clarity_tx.reset_cost(cost_before.clone());
                            if total_budget.proportion_largest_dimension(cost_before)
                                < TX_BLOCK_LIMIT_PROPORTION_HEURISTIC
                            {
                                warn!(
                                    "Transaction {} consumed over {}% of block budget, marking as invalid; budget was {}",
                                    tx.txid(),
                                    100 - TX_BLOCK_LIMIT_PROPORTION_HEURISTIC,
                                    &total_budget
                                );
                                let mut measured_cost = cost_after.clone();
                                let measured_cost = if measured_cost.sub(cost_before).is_ok() {
                                    Some(measured_cost)
                                } else {
                                    warn!(
                                        "Failed to compute measured cost of a too big transaction"
                                    );
                                    None
                                };
                                return Ok(TransactionResult::error(
                                    &tx,
                                    Error::TransactionTooBigError(measured_cost),
                                ));
                            } else {
                                warn!(
                                    "Transaction {} reached block cost {}; budget was {}",
                                    tx.txid(),
                                    &cost_after,
                                    &total_budget
                                );
                                return Ok(TransactionResult::skipped_due_to_error(
                                    &tx,
                                    Error::BlockTooBigError,
                                ));
                            }
                        }
                        _ => Ok(TransactionResult::error(&tx, e)),
                    }
                }
            }
        }
    }

    /// NOTE: this is only used in integration tests.
    #[cfg(any(test, feature = "testing"))]
    pub fn mine_next_microblock_from_txs(
        &mut self,
        txs_and_lens: Vec<(StacksTransaction, u64)>,
        miner_key: &Secp256k1PrivateKey,
    ) -> Result<StacksMicroblock, Error> {
        let mut txs_included = vec![];

        let mut clarity_tx = self
            .clarity_tx
            .take()
            .expect("Microblock already open and processing");

        let mut considered = self
            .runtime
            .considered
            .take()
            .expect("Microblock already open and processing");

        let mut bytes_so_far = self.runtime.bytes_so_far;
        let mut num_txs = self.runtime.num_mined;
        let mut tx_events = Vec::new();
        let mut block_limit_hit = BlockLimitFunction::NO_LIMIT_HIT;

        let mut result = Ok(());
        for (tx, tx_len) in txs_and_lens.into_iter() {
            if considered.contains(&tx.txid()) {
                continue;
            } else {
                considered.insert(tx.txid());
            }

            match StacksMicroblockBuilder::mine_next_transaction(
                &mut clarity_tx,
                tx.clone(),
                tx_len,
                bytes_so_far,
                &block_limit_hit,
                self.ast_rules,
            ) {
                Ok(tx_result) => {
                    tx_events.push(tx_result.convert_to_event());
                    match tx_result {
                        TransactionResult::Success(..) => {
                            test_debug!("Include tx {} in microblock", tx.txid());
                            bytes_so_far += tx_len;
                            num_txs += 1;
                            txs_included.push(tx);
                        }
                        TransactionResult::Skipped(TransactionSkipped { error, .. })
                        | TransactionResult::ProcessingError(TransactionError { error, .. }) => {
                            test_debug!("Exclude tx {} from microblock", tx.txid());
                            if let Error::BlockTooBigError = &error {
                                // done mining -- our execution budget is exceeded.
                                // Make the block from the transactions we did manage to get
                                test_debug!("Block budget exceeded on tx {}", &tx.txid());
                                if block_limit_hit == BlockLimitFunction::NO_LIMIT_HIT {
                                    test_debug!("Switch to mining stx-transfers only");
                                    block_limit_hit = BlockLimitFunction::CONTRACT_LIMIT_HIT;
                                } else if block_limit_hit == BlockLimitFunction::CONTRACT_LIMIT_HIT
                                {
                                    test_debug!(
                                        "Stop mining microblock block due to limit exceeded"
                                    );
                                    break;
                                }
                            }
                            continue;
                        }
                        TransactionResult::Problematic(TransactionProblematic {
                            tx: _tx, ..
                        }) => {
                            test_debug!("Exclude problematic tx {} from microblock", _tx.txid());
                            continue;
                        }
                    }
                }
                Err(e) => {
                    result = Err(e);
                    break;
                }
            }
        }

        // do fault injection
        if self.runtime.disable_bytes_check {
            warn!("Fault injection: disabling miner limit on microblock stream size");
            bytes_so_far = 0;
        }
        if self.runtime.disable_cost_check {
            warn!("Fault injection: disabling miner limit on microblock runtime cost");
            clarity_tx.reset_cost(ExecutionCost::ZERO);
        }

        self.runtime.bytes_so_far = bytes_so_far;
        self.clarity_tx.replace(clarity_tx);
        self.runtime.considered.replace(considered);
        self.runtime.num_mined = num_txs;

        if let Err(e) = result {
            warn!("Error producing microblock: {}", e);
            return Err(e);
        }

        return self.make_next_microblock(txs_included, miner_key, tx_events, None);
    }

    pub fn mine_next_microblock(
        &mut self,
        mem_pool: &mut MemPoolDB,
        miner_key: &Secp256k1PrivateKey,
        event_dispatcher: &dyn MemPoolEventDispatcher,
    ) -> Result<StacksMicroblock, Error> {
        let mut txs_included = vec![];
        let mempool_settings = self.settings.mempool_settings.clone();

        let mut clarity_tx = self
            .clarity_tx
            .take()
            .expect("Microblock already open and processing");

        let mut considered = self
            .runtime
            .considered
            .take()
            .expect("Microblock already open and processing");

        let mut invalidated_txs = vec![];
        let mut to_drop_and_blacklist = vec![];

        let mut bytes_so_far = self.runtime.bytes_so_far;
        let mut num_txs = self.runtime.num_mined;
        let mut num_selected = 0;
        let mut tx_events = Vec::new();
        let deadline = get_epoch_time_ms() + u128::from(self.settings.max_miner_time_ms);
        let mut block_limit_hit = BlockLimitFunction::NO_LIMIT_HIT;

        mem_pool.reset_nonce_cache()?;
        let stacks_epoch_id = clarity_tx.get_epoch();
        let block_limit = clarity_tx
            .block_limit()
            .expect("No block limit found for clarity_tx.");
        mem_pool.estimate_tx_rates(100, &block_limit, &stacks_epoch_id)?;

        debug!(
            "Microblock transaction selection begins (child of {}), bytes so far: {}",
            &self.anchor_block, bytes_so_far
        );
        let mut blocked = false;

        let result = {
            let mut intermediate_result;
            loop {
                let mut num_added = 0;
                intermediate_result = mem_pool.iterate_candidates(
                    &mut clarity_tx,
                    &mut tx_events,
                    mempool_settings.clone(),
                    |clarity_tx, to_consider, estimator| {
                        let mempool_tx = &to_consider.tx;
                        let update_estimator = to_consider.update_estimate;

                        if get_epoch_time_ms() >= deadline {
                            debug!(
                                "Microblock miner deadline exceeded ({} ms)",
                                self.settings.max_miner_time_ms
                            );
                            return Ok(None);
                        }

                        blocked = (*self.settings.miner_status.lock().expect("FATAL: mutex poisoned")).is_blocked();
                        if blocked {
                            debug!("Microblock miner stopping due to preemption");
                            return Ok(None);
                        }

                        if considered.contains(&mempool_tx.tx.txid()) {
                            return Ok(Some(TransactionResult::skipped(
                                &mempool_tx.tx, "Transaction already considered.".to_string()).convert_to_event()));
                        } else {
                            considered.insert(mempool_tx.tx.txid());
                        }

                        match StacksMicroblockBuilder::mine_next_transaction(
                            clarity_tx,
                            mempool_tx.tx.clone(),
                            mempool_tx.metadata.len,
                            bytes_so_far,
                            &block_limit_hit,
                            self.ast_rules.clone(),
                        ) {
                            Ok(tx_result) => {
                                let result_event = tx_result.convert_to_event();
                                match tx_result {
                                    TransactionResult::Success(TransactionSuccess {
                                        receipt,
                                        ..
                                    }) => {
                                        bytes_so_far += mempool_tx.metadata.len;

                                        if update_estimator {
                                            if let Err(e) = estimator.notify_event(
                                                &mempool_tx.tx.payload,
                                                &receipt.execution_cost,
                                                &block_limit,
                                                &stacks_epoch_id,
                                            ) {
                                                warn!("Error updating estimator";
                                              "txid" => %mempool_tx.metadata.txid,
                                              "error" => ?e);
                                            }
                                        }

                                        debug!(
                                            "Include tx {} ({}) in microblock",
                                            mempool_tx.tx.txid(),
                                            mempool_tx.tx.payload.name()
                                        );
                                        txs_included.push(mempool_tx.tx.clone());
                                        num_txs += 1;
                                        num_added += 1;
                                        num_selected += 1;
                                        Ok(Some(result_event))
                                    }
                                    TransactionResult::Skipped(TransactionSkipped {
                                        error,
                                        ..
                                    })
                                    | TransactionResult::ProcessingError(TransactionError {
                                        error,
                                        ..
                                    }) => {
                                        match &error {
                                            Error::BlockTooBigError => {
                                                // done mining -- our execution budget is exceeded.
                                                // Make the block from the transactions we did manage to get
                                                debug!("Block budget exceeded on tx {}", &mempool_tx.tx.txid());
                                                if block_limit_hit == BlockLimitFunction::NO_LIMIT_HIT {
                                                    debug!("Block budget exceeded while mining microblock";
                                                        "tx" => %mempool_tx.tx.txid(), "next_behavior" => "Switch to mining stx-transfers only");
                                                    block_limit_hit =
                                                        BlockLimitFunction::CONTRACT_LIMIT_HIT;
                                                } else if block_limit_hit
                                                    == BlockLimitFunction::CONTRACT_LIMIT_HIT
                                                {
                                                    debug!("Block budget exceeded while mining microblock";
                                                        "tx" => %mempool_tx.tx.txid(), "next_behavior" => "Stop mining microblock");
                                                    block_limit_hit = BlockLimitFunction::LIMIT_REACHED;
                                                    return Ok(None);
                                                }
                                            }
                                            Error::TransactionTooBigError(measured_cost) => {
                                                if update_estimator {
                                                    if let Some(measured_cost) = measured_cost {
                                                        if let Err(e) = estimator.notify_event(
                                                            &mempool_tx.tx.payload,
                                                            measured_cost,
                                                            &block_limit,
                                                            &stacks_epoch_id,
                                                        ) {
                                                            warn!("Error updating estimator";
                                                                  "txid" => %mempool_tx.metadata.txid,
                                                                  "error" => ?e);
                                                        }
                                                    }
                                                }

                                                invalidated_txs.push(mempool_tx.metadata.txid);
                                            }
                                            _ => {}
                                        }
                                        return Ok(Some(result_event))
                                    }
                                    TransactionResult::Problematic(TransactionProblematic { tx, .. }) => {
                                        debug!("Drop problematic transaction {}", &tx.txid());
                                        to_drop_and_blacklist.push(tx.txid());
                                        Ok(Some(result_event))
                                    }
                                }
                            }
                            Err(e) => Err(e),
                        }
                    },
                );

                if !to_drop_and_blacklist.is_empty() {
                    debug!(
                        "Dropping and blacklisting {} problematic transaction(s)",
                        &to_drop_and_blacklist.len()
                    );
                    let _ = mem_pool.drop_and_blacklist_txs(&to_drop_and_blacklist);
                }

                if intermediate_result.is_err() {
                    break;
                }

                if num_added == 0 {
                    break;
                }
            }
            intermediate_result
        };

        debug!(
            "Miner: Microblock transaction selection finished (child of {}); {} transactions selected",
            &self.anchor_block, num_selected
        );

        // do fault injection
        if self.runtime.disable_bytes_check {
            warn!("Fault injection: disabling miner limit on microblock stream size");
            bytes_so_far = 0;
        }
        if self.runtime.disable_cost_check {
            warn!("Fault injection: disabling miner limit on microblock runtime cost");
            clarity_tx.reset_cost(ExecutionCost::ZERO);
        }

        self.runtime.bytes_so_far = bytes_so_far;
        self.clarity_tx.replace(clarity_tx);
        self.runtime.considered.replace(considered);
        self.runtime.num_mined = num_txs;

        mem_pool.drop_txs(&invalidated_txs)?;
        event_dispatcher.mempool_txs_dropped(
            invalidated_txs,
            None,
            MemPoolDropReason::TOO_EXPENSIVE,
        );
        event_dispatcher.mempool_txs_dropped(
            to_drop_and_blacklist,
            None,
            MemPoolDropReason::PROBLEMATIC,
        );

        if blocked {
            debug!(
                "Miner: Microblock transaction selection aborted (child of {}); {} transactions selected",
                &self.anchor_block, num_selected
            );
            return Err(Error::MinerAborted);
        }

        match result {
            Ok(_) => {}
            Err(e) => {
                warn!("Failure building microblock: {}", e);
                return Err(e);
            }
        }

        return self.make_next_microblock(
            txs_included,
            miner_key,
            tx_events,
            Some(event_dispatcher),
        );
    }

    pub fn get_bytes_so_far(&self) -> u64 {
        self.runtime.bytes_so_far
    }

    pub fn get_cost_so_far(&self) -> Option<ExecutionCost> {
        self.clarity_tx.as_ref().map(|tx| tx.cost_so_far())
    }
}

impl Drop for StacksMicroblockBuilder<'_> {
    fn drop(&mut self) {
        debug!(
            "Drop StacksMicroblockBuilder";
            "chain tip" => %&self.runtime.tip,
            "txs mined off tip" => &self.runtime.considered.as_ref().map(|x| x.len()).unwrap_or(0),
            "txs added" => self.runtime.num_mined,
            "bytes so far" => self.runtime.bytes_so_far,
            "cost so far" => &format!("{:?}", &self.get_cost_so_far())
        );
        self.clarity_tx
            .take()
            .expect("Attempted to reclose closed microblock builder")
            .rollback_block()
    }
}

impl StacksBlockBuilder {
    fn from_parent_pubkey_hash(
        miner_id: usize,
        parent_chain_tip: &StacksHeaderInfo,
        total_work: &StacksWorkScore,
        proof: &VRFProof,
        pubkh: Hash160,
    ) -> StacksBlockBuilder {
        let header = StacksBlockHeader::from_parent_empty(
            &parent_chain_tip.anchored_header,
            parent_chain_tip.microblock_tail.as_ref(),
            total_work,
            proof,
            &pubkh,
        );

        let mut header_bytes = vec![];
        header
            .consensus_serialize(&mut header_bytes)
            .expect("FATAL: failed to serialize to vec");
        let bytes_so_far = u64::try_from(header_bytes.len()).expect("header bytes exceeds 2^64");

        StacksBlockBuilder {
            chain_tip: parent_chain_tip.clone(),
            txs: vec![],
            micro_txs: vec![],
            total_anchored_fees: 0,
            total_confirmed_streamed_fees: 0,
            total_streamed_fees: 0,
            bytes_so_far,
            anchored_done: false,
            parent_consensus_hash: parent_chain_tip.consensus_hash.clone(),
            parent_header_hash: header.parent_block.clone(),
            header,
            parent_microblock_hash: parent_chain_tip
                .microblock_tail
                .as_ref()
                .map(|hdr| hdr.block_hash()),
            prev_microblock_header: StacksMicroblockHeader::first_unsigned(
                &EMPTY_MICROBLOCK_PARENT_HASH,
                &Sha512Trunc256Sum([0u8; 32]),
            ), // will be updated
            miner_privkey: StacksPrivateKey::random(), // caller should overwrite this, or refrain from mining microblocks
            miner_payouts: None,
            miner_id,
        }
    }

    pub fn from_parent(
        miner_id: usize,
        parent_chain_tip: &StacksHeaderInfo,
        total_work: &StacksWorkScore,
        proof: &VRFProof,
        microblock_privkey: &StacksPrivateKey,
    ) -> StacksBlockBuilder {
        let mut pubk = StacksPublicKey::from_private(microblock_privkey);
        pubk.set_compressed(true);
        let pubkh = Hash160::from_node_public_key(&pubk);

        let mut builder = StacksBlockBuilder::from_parent_pubkey_hash(
            miner_id,
            parent_chain_tip,
            total_work,
            proof,
            pubkh,
        );
        builder.miner_privkey = microblock_privkey.clone();
        builder
    }

    fn first_pubkey_hash(
        miner_id: usize,
        genesis_consensus_hash: &ConsensusHash,
        genesis_burn_header_hash: &BurnchainHeaderHash,
        genesis_burn_header_height: u32,
        genesis_burn_header_timestamp: u64,
        proof: &VRFProof,
        pubkh: Hash160,
    ) -> StacksBlockBuilder {
        let genesis_chain_tip = StacksHeaderInfo {
            anchored_header: StacksBlockHeader::genesis_block_header().into(),
            microblock_tail: None,
            stacks_block_height: 0,
            index_root: TrieHash([0u8; 32]),
            consensus_hash: genesis_consensus_hash.clone(),
            burn_header_hash: genesis_burn_header_hash.clone(),
            burn_header_timestamp: genesis_burn_header_timestamp,
            burn_header_height: genesis_burn_header_height,
            anchored_block_size: 0,
            burn_view: None,
        };

        let mut builder = StacksBlockBuilder::from_parent_pubkey_hash(
            miner_id,
            &genesis_chain_tip,
            &StacksWorkScore::initial(),
            proof,
            pubkh,
        );
        builder.header.parent_block = EMPTY_MICROBLOCK_PARENT_HASH.clone();
        builder
    }

    pub fn first(
        miner_id: usize,
        genesis_consensus_hash: &ConsensusHash,
        genesis_burn_header_hash: &BurnchainHeaderHash,
        genesis_burn_header_height: u32,
        genesis_burn_header_timestamp: u64,
        proof: &VRFProof,
        microblock_privkey: &StacksPrivateKey,
    ) -> StacksBlockBuilder {
        let mut pubk = StacksPublicKey::from_private(microblock_privkey);
        pubk.set_compressed(true);
        let pubkh = Hash160::from_node_public_key(&pubk);

        let mut builder = StacksBlockBuilder::first_pubkey_hash(
            miner_id,
            genesis_consensus_hash,
            genesis_burn_header_hash,
            genesis_burn_header_height,
            genesis_burn_header_timestamp,
            proof,
            pubkh,
        );
        builder.miner_privkey = microblock_privkey.clone();
        builder
    }

    /// Assign the block parent
    pub fn set_parent_block(&mut self, parent_block_hash: &BlockHeaderHash) {
        self.header.parent_block = parent_block_hash.clone();
    }

    /// Assign the anchored block's parent microblock (used for testing orphaning)
    pub fn set_parent_microblock(
        &mut self,
        parent_mblock_hash: &BlockHeaderHash,
        parent_mblock_seq: u16,
    ) {
        self.header.parent_microblock = parent_mblock_hash.clone();
        self.header.parent_microblock_sequence = parent_mblock_seq;
    }

    /// Set the block header's public key hash
    pub fn set_microblock_pubkey_hash(&mut self, pubkh: Hash160) -> bool {
        if self.anchored_done {
            // too late
            return false;
        }

        self.header.microblock_pubkey_hash = pubkh;
        return true;
    }

    /// Set the block miner's private key
    pub fn set_microblock_privkey(&mut self, privk: StacksPrivateKey) {
        self.miner_privkey = privk;
    }

    /// Reset measured costs and fees
    pub fn reset_costs(&mut self) {
        self.total_anchored_fees = 0;
        self.total_confirmed_streamed_fees = 0;
        self.total_streamed_fees = 0;
    }

    /// Append a transaction if doing so won't exceed the epoch data size.
    /// Does not check for errors
    #[cfg(test)]
    pub fn force_mine_tx(
        &mut self,
        clarity_tx: &mut ClarityTx,
        tx: &StacksTransaction,
    ) -> Result<(), Error> {
        let mut tx_bytes = vec![];
        tx.consensus_serialize(&mut tx_bytes)
            .map_err(Error::CodecError)?;
        let tx_len = u64::try_from(tx_bytes.len()).expect("tx len exceeds 2^64 bytes");

        if self.bytes_so_far + tx_len >= MAX_EPOCH_SIZE.into() {
            warn!(
                "Epoch size is {} >= {}",
                self.bytes_so_far + tx_len,
                MAX_EPOCH_SIZE
            );
        }

        let quiet = !cfg!(test);
        if !self.anchored_done {
            // save
            match StacksChainState::process_transaction(clarity_tx, tx, quiet, ASTRules::Typical) {
                Ok((fee, receipt)) => {
                    self.total_anchored_fees += fee;
                }
                Err(e) => {
                    warn!("Invalid transaction {} in anchored block, but forcing inclusion (error: {:?})", &tx.txid(), &e);
                }
            }

            self.txs.push(tx.clone());
        } else {
            match StacksChainState::process_transaction(clarity_tx, tx, quiet, ASTRules::Typical) {
                Ok((fee, receipt)) => {
                    self.total_streamed_fees += fee;
                }
                Err(e) => {
                    warn!(
                        "Invalid transaction {} in microblock, but forcing inclusion (error: {:?})",
                        &tx.txid(),
                        &e
                    );
                }
            }

            self.micro_txs.push(tx.clone());
        }

        self.bytes_so_far += tx_len;
        Ok(())
    }

    pub fn finalize_block(&mut self, clarity_tx: &mut ClarityTx) -> StacksBlock {
        // done!  Calculate state root and tx merkle root
        let txid_vecs: Vec<_> = self
            .txs
            .iter()
            .map(|tx| tx.txid().as_bytes().to_vec())
            .collect();

        let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
        let tx_merkle_root = merkle_tree.root();
        let state_root_hash = clarity_tx.seal();

        self.header.tx_merkle_root = tx_merkle_root;
        self.header.state_index_root = state_root_hash;

        let block = StacksBlock {
            header: self.header.clone(),
            txs: self.txs.clone(),
        };

        self.prev_microblock_header = StacksMicroblockHeader::first_unsigned(
            &block.block_hash(),
            &Sha512Trunc256Sum([0u8; 32]),
        );

        self.prev_microblock_header.prev_block = block.block_hash();
        self.anchored_done = true;

        test_debug!(
            "\n\nMiner {}: Mined anchored block {}, {} transactions, state root is {}\n",
            self.miner_id,
            block.block_hash(),
            block.txs.len(),
            state_root_hash
        );

        info!(
            "Miner: mined anchored block {} height {} with {} txs, parent block {}, parent microblock {} ({}), state root = {}",
            block.block_hash(),
            block.header.total_work.work,
            block.txs.len(),
            &self.header.parent_block,
            &self.header.parent_microblock,
            self.header.parent_microblock_sequence,
            state_root_hash
        );

        block
    }

    /// Finish building the anchored block.
    /// TODO: expand to deny mining a block whose anchored static checks fail (and allow the caller
    /// to disable this, in order to test mining invalid blocks)
    /// Returns: stacks block
    pub fn mine_anchored_block(&mut self, clarity_tx: &mut ClarityTx) -> StacksBlock {
        assert!(!self.anchored_done);
        StacksChainState::finish_block(
            clarity_tx,
            self.miner_payouts.as_ref(),
            u32::try_from(self.header.total_work.work).expect("FATAL: more than 2^32 blocks"),
            self.header.microblock_pubkey_hash,
        )
        .expect("FATAL: call to `finish_block` failed");
        self.finalize_block(clarity_tx)
    }

    /// Cut the next microblock.
    pub fn mine_next_microblock<'a>(&mut self) -> Result<StacksMicroblock, Error> {
        let txid_vecs: Vec<_> = self
            .micro_txs
            .iter()
            .map(|tx| tx.txid().as_bytes().to_vec())
            .collect();

        let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
        let tx_merkle_root = merkle_tree.root();
        let mut next_microblock_header =
            if self.prev_microblock_header.tx_merkle_root == Sha512Trunc256Sum([0u8; 32]) {
                // .prev_block is the hash of the parent anchored block
                StacksMicroblockHeader::first_unsigned(
                    &self.prev_microblock_header.prev_block,
                    &tx_merkle_root,
                )
            } else {
                StacksMicroblockHeader::from_parent_unsigned(
                    &self.prev_microblock_header,
                    &tx_merkle_root,
                )
                .ok_or(Error::MicroblockStreamTooLongError)?
            };

        test_debug!("Sign with {}", self.miner_privkey.to_hex());

        next_microblock_header.sign(&self.miner_privkey).unwrap();
        next_microblock_header
            .verify(&self.header.microblock_pubkey_hash)
            .unwrap();

        self.prev_microblock_header = next_microblock_header.clone();

        let microblock = StacksMicroblock {
            header: next_microblock_header,
            txs: self.micro_txs.clone(),
        };

        self.micro_txs.clear();

        test_debug!(
            "\n\nMiner {}: Mined microblock block {} (seq={}): {} transaction(s)\n",
            self.miner_id,
            microblock.block_hash(),
            microblock.header.sequence,
            microblock.txs.len()
        );
        Ok(microblock)
    }

    fn load_parent_microblocks(
        &mut self,
        chainstate: &mut StacksChainState,
        parent_consensus_hash: &ConsensusHash,
        parent_header_hash: &BlockHeaderHash,
    ) -> Result<Vec<StacksMicroblock>, Error> {
        if let Some(microblock_parent_hash) = self.parent_microblock_hash.as_ref() {
            // load up a microblock fork
            let microblocks = StacksChainState::load_microblock_stream_fork(
                chainstate.db(),
                parent_consensus_hash,
                parent_header_hash,
                microblock_parent_hash,
            )?
            .ok_or(Error::NoSuchBlockError)?;

            debug!(
                "Loaded {} microblocks made by {}/{} tipped at {}",
                microblocks.len(),
                parent_consensus_hash,
                parent_header_hash,
                microblock_parent_hash
            );
            Ok(microblocks)
        } else {
            // apply all known parent microblocks before beginning our tenure
            let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                &self.parent_consensus_hash,
                &self.parent_header_hash,
            );
            let (parent_microblocks, _) =
                match StacksChainState::load_descendant_staging_microblock_stream_with_poison(
                    chainstate.db(),
                    &parent_index_hash,
                    0,
                    u16::MAX,
                )? {
                    Some(x) => x,
                    None => (vec![], None),
                };

            debug!(
                "Loaded {} microblocks made by {}/{}",
                parent_microblocks.len(),
                parent_consensus_hash,
                parent_header_hash
            );
            Ok(parent_microblocks)
        }
    }

    // TODO: add tests from mutation testing results #4859
    #[cfg_attr(test, mutants::skip)]
    /// This function should be called before `epoch_begin`.
    /// It loads the parent microblock stream, sets the parent microblock, and returns
    /// data necessary for `epoch_begin`.
    /// Returns chainstate transaction, clarity instance, burnchain header hash
    /// of the burn tip, burn tip height + 1, the parent microblock stream,
    /// the parent consensus hash, the parent header hash, and a bool
    /// representing whether the network is mainnet or not.
    pub fn pre_epoch_begin<'a>(
        &mut self,
        chainstate: &'a mut StacksChainState,
        burn_dbconn: &'a SortitionHandleConn,
        confirm_microblocks: bool,
    ) -> Result<MinerEpochInfo<'a>, Error> {
        debug!(
            "Miner epoch begin";
            "miner" => %self.miner_id,
            "chain_tip" => %format!("{}/{}", self.chain_tip.consensus_hash,
                                    self.header.parent_block)
        );

        if let Some((ref _miner_payout, ref _user_payouts, ref _parent_reward, ref _reward_info)) =
            self.miner_payouts
        {
            test_debug!(
                "Miner payout to process: {:?}; user payouts: {:?}; parent payout: {:?}",
                _miner_payout,
                _user_payouts,
                _parent_reward
            );
        }

        let parent_index_hash = StacksBlockHeader::make_index_block_hash(
            &self.parent_consensus_hash,
            &self.parent_header_hash,
        );

        let burn_tip = SortitionDB::get_canonical_chain_tip_bhh(burn_dbconn.conn())?;
        let burn_tip_height = u32::try_from(
            SortitionDB::get_canonical_burn_chain_tip(burn_dbconn.conn())?.block_height,
        )
        .expect("FATAL: more than 2^32 sortitions");

        let parent_microblocks = if !confirm_microblocks {
            debug!("Block assembly invoked with confirm_microblocks = false. Will not confirm any microblocks.");
            vec![]
        } else if StacksChainState::block_crosses_epoch_boundary(
            chainstate.db(),
            &self.parent_consensus_hash,
            &self.parent_header_hash,
        )? {
            info!("Descendant of {}/{} will NOT confirm any microblocks, since it will cross an epoch boundary", &self.parent_consensus_hash, &self.parent_header_hash);
            vec![]
        } else {
            match self.load_parent_microblocks(
                chainstate,
                &self.parent_consensus_hash.clone(),
                &self.parent_header_hash.clone(),
            ) {
                Ok(x) => x,
                Err(e) => {
                    warn!("Miner failed to load parent microblock, mining without parent microblock tail";
                              "parent_block_hash" => %self.parent_header_hash,
                              "parent_index_hash" => %parent_index_hash,
                              "parent_consensus_hash" => %self.parent_consensus_hash,
                              "parent_microblock_hash" => match self.parent_microblock_hash.as_ref() {
                                  Some(x) => format!("Some({x})"),
                                  None => "None".to_string(),
                              },
                              "error" => ?e);
                    vec![]
                }
            }
        };

        debug!(
            "Descendant of {}/{} confirms {} microblock(s)",
            &self.parent_consensus_hash,
            &self.parent_header_hash,
            parent_microblocks.len()
        );

        if parent_microblocks.is_empty() {
            self.set_parent_microblock(&EMPTY_MICROBLOCK_PARENT_HASH, 0);
        } else {
            let num_mblocks = parent_microblocks.len();
            let last_mblock_hdr = parent_microblocks[num_mblocks - 1].header.clone();
            self.set_parent_microblock(&last_mblock_hdr.block_hash(), last_mblock_hdr.sequence);
        };

        let mainnet = chainstate.config().mainnet;

        // data won't be committed, so do a concurrent transaction
        let (chainstate_tx, clarity_instance) = chainstate.chainstate_tx_begin()?;

        let ast_rules =
            SortitionDB::get_ast_rules(burn_dbconn.conn(), (burn_tip_height + 1).into())?;

        Ok(MinerEpochInfo {
            chainstate_tx,
            clarity_instance,
            burn_tip,
            burn_tip_height: burn_tip_height + 1,
            parent_microblocks,
            mainnet,
            ast_rules,
        })
    }

    /// Begin mining an epoch's transactions.
    /// Returns an open ClarityTx for mining the block, as well as the ExecutionCost of any confirmed
    ///  microblocks.
    /// NOTE: even though we don't yet know the block hash, the Clarity VM ensures that a
    /// transaction can't query information about the _current_ block (i.e. information that is not
    /// yet known).
    /// This function was separated from `pre_epoch_begin` because something "higher" than `epoch_begin`
    /// must own `ChainstateTx` and `ClarityInstance`, which are borrowed to construct the
    /// returned ClarityTx object.
    pub fn epoch_begin<'a, 'b>(
        &mut self,
        burn_dbconn: &'a SortitionHandleConn,
        info: &'b mut MinerEpochInfo<'a>,
    ) -> Result<(ClarityTx<'b, 'b>, ExecutionCost), Error> {
        let SetupBlockResult {
            clarity_tx,
            microblock_execution_cost,
            microblock_fees,
            matured_miner_rewards_opt,
            ..
        } = StacksChainState::setup_block(
            &mut info.chainstate_tx,
            info.clarity_instance,
            burn_dbconn,
            burn_dbconn,
            burn_dbconn.conn(),
            &burn_dbconn.context.pox_constants,
            &self.chain_tip,
            info.burn_tip,
            info.burn_tip_height,
            self.parent_consensus_hash,
            self.parent_header_hash,
            &info.parent_microblocks,
            info.mainnet,
            Some(self.miner_id),
        )?;
        self.miner_payouts = matured_miner_rewards_opt;
        self.total_confirmed_streamed_fees +=
            u64::try_from(microblock_fees).expect("more than 2^64 microstx microblock fees");

        Ok((clarity_tx, microblock_execution_cost))
    }

    /// Finish up mining an epoch's transactions
    pub fn epoch_finish(self, tx: ClarityTx) -> Result<ExecutionCost, Error> {
        let new_consensus_hash = MINER_BLOCK_CONSENSUS_HASH.clone();
        let new_block_hash = MINER_BLOCK_HEADER_HASH.clone();

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(&new_consensus_hash, &new_block_hash);

        // clear out the block trie we just created, so the block validator logic doesn't step all
        // over it.
        //        let moved_name = format!("{}.mined", index_block_hash);

        // write out the trie...
        let consumed = tx.commit_mined_block(&index_block_hash)?;

        test_debug!(
            "\n\nMiner {}: Finished mining child of {}/{}. Trie is in mined_blocks table.\n",
            self.miner_id,
            self.chain_tip.consensus_hash,
            self.chain_tip.anchored_header.block_hash()
        );

        Ok(consumed)
    }
    /// Unconditionally build an anchored block from a list of transactions.
    ///  Used in test cases
    #[cfg(test)]
    pub fn make_anchored_block_from_txs(
        builder: StacksBlockBuilder,
        chainstate_handle: &StacksChainState,
        burn_dbconn: &SortitionHandleConn,
        txs: Vec<StacksTransaction>,
    ) -> Result<(StacksBlock, u64, ExecutionCost), Error> {
        Self::make_anchored_block_and_microblock_from_txs(
            builder,
            chainstate_handle,
            burn_dbconn,
            txs,
            vec![],
        )
        .map(|(stacks_block, size, cost, _)| (stacks_block, size, cost))
    }

    /// Unconditionally build an anchored block from a list of transactions.
    ///  Used in test cases
    #[cfg(test)]
    pub fn make_anchored_block_and_microblock_from_txs(
        mut builder: StacksBlockBuilder,
        chainstate_handle: &StacksChainState,
        burn_dbconn: &SortitionHandleConn,
        txs: Vec<StacksTransaction>,
        mut mblock_txs: Vec<StacksTransaction>,
    ) -> Result<(StacksBlock, u64, ExecutionCost, Option<StacksMicroblock>), Error> {
        debug!("Build anchored block from {} transactions", txs.len());
        let (mut chainstate, _) = chainstate_handle.reopen()?;
        let mut miner_epoch_info = builder.pre_epoch_begin(&mut chainstate, burn_dbconn, true)?;
        let ast_rules = miner_epoch_info.ast_rules;
        let (mut epoch_tx, _) = builder.epoch_begin(burn_dbconn, &mut miner_epoch_info)?;
        for tx in txs.into_iter() {
            match builder.try_mine_tx(&mut epoch_tx, &tx, ast_rules.clone()) {
                Ok(_) => {
                    debug!("Included {}", &tx.txid());
                }
                Err(Error::BlockTooBigError) => {
                    // done mining -- our execution budget is exceeded.
                    // Make the block from the transactions we did manage to get
                    debug!("Block budget exceeded on tx {}", &tx.txid());
                }
                Err(Error::InvalidStacksTransaction(_emsg, true)) => {
                    // if we have an invalid transaction that was quietly ignored, don't warn here either
                    test_debug!(
                        "Failed to apply tx {}: InvalidStacksTransaction '{:?}'",
                        &tx.txid(),
                        &_emsg
                    );
                    continue;
                }
                Err(Error::ProblematicTransaction(txid)) => {
                    test_debug!("Encountered problematic transaction. Aborting");
                    return Err(Error::ProblematicTransaction(txid));
                }

                Err(e) => {
                    warn!("Failed to apply tx {}: {:?}", &tx.txid(), &e);
                    continue;
                }
            }
        }
        let block = builder.mine_anchored_block(&mut epoch_tx);
        let size = builder.bytes_so_far;

        let mblock_opt = if mblock_txs.is_empty() {
            None
        } else {
            builder.micro_txs.append(&mut mblock_txs);
            let mblock = builder.mine_next_microblock()?;
            Some(mblock)
        };

        let cost = builder.epoch_finish(epoch_tx)?;
        Ok((block, size, cost, mblock_opt))
    }

    // TODO: add tests from mutation testing results #4860
    #[cfg_attr(test, mutants::skip)]
    /// Create a block builder for mining
    pub fn make_block_builder(
        burnchain: &Burnchain,
        mainnet: bool,
        stacks_parent_header: &StacksHeaderInfo,
        proof: VRFProof,
        total_burn: u64,
        pubkey_hash: Hash160,
    ) -> Result<StacksBlockBuilder, Error> {
        let builder = if stacks_parent_header.consensus_hash == FIRST_BURNCHAIN_CONSENSUS_HASH {
            let (first_block_hash, first_block_height, first_block_ts) = if mainnet {
                (
                    BurnchainHeaderHash::from_hex(BITCOIN_MAINNET_FIRST_BLOCK_HASH).unwrap(),
                    BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT,
                    BITCOIN_MAINNET_FIRST_BLOCK_TIMESTAMP,
                )
            } else {
                (
                    burnchain.first_block_hash,
                    burnchain.first_block_height,
                    burnchain.first_block_timestamp,
                )
            };
            StacksBlockBuilder::first_pubkey_hash(
                0,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &first_block_hash,
                u32::try_from(first_block_height).expect("FATAL: first block is over 2^32"),
                u64::try_from(first_block_ts).expect("FATAL: first block timestamp is over 2^64"),
                &proof,
                pubkey_hash,
            )
        } else {
            // building off an existing stacks block
            let new_work = StacksWorkScore {
                burn: total_burn,
                work: stacks_parent_header
                    .stacks_block_height
                    .checked_add(1)
                    .expect("FATAL: block height overflow"),
            };

            StacksBlockBuilder::from_parent_pubkey_hash(
                0,
                stacks_parent_header,
                &new_work,
                &proof,
                pubkey_hash,
            )
        };

        Ok(builder)
    }

    // TODO: add tests from mutation testing results #4860
    #[cfg_attr(test, mutants::skip)]
    /// Create a block builder for regtest mining
    pub fn make_regtest_block_builder(
        burnchain: &Burnchain,
        stacks_parent_header: &StacksHeaderInfo,
        proof: VRFProof,
        total_burn: u64,
        pubkey_hash: Hash160,
    ) -> Result<StacksBlockBuilder, Error> {
        let builder = if stacks_parent_header.consensus_hash == FIRST_BURNCHAIN_CONSENSUS_HASH {
            StacksBlockBuilder::first_pubkey_hash(
                0,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &burnchain.first_block_hash,
                u32::try_from(burnchain.first_block_height)
                    .expect("first regtest bitcoin block is over 2^32"),
                u64::try_from(burnchain.first_block_timestamp)
                    .expect("first regtest bitcoin block timestamp is over 2^64"),
                &proof,
                pubkey_hash,
            )
        } else {
            // building off an existing stacks block
            let new_work = StacksWorkScore {
                burn: total_burn,
                work: stacks_parent_header
                    .stacks_block_height
                    .checked_add(1)
                    .expect("FATAL: block height overflow"),
            };

            StacksBlockBuilder::from_parent_pubkey_hash(
                0,
                stacks_parent_header,
                &new_work,
                &proof,
                pubkey_hash,
            )
        };
        Ok(builder)
    }

    /// Select transactions for block inclusion from the mempool.
    /// Applies them to the ongoing ClarityTx.
    /// If invalid transactions are encountered, they are dropped from the mempool.
    /// Returns whether or not the miner got blocked, as well as the gathered tx events
    pub fn select_and_apply_transactions<B: BlockBuilder>(
        epoch_tx: &mut ClarityTx,
        builder: &mut B,
        mempool: &mut MemPoolDB,
        tip_height: u64,
        initial_txs: &[StacksTransaction],
        settings: BlockBuilderSettings,
        event_observer: Option<&dyn MemPoolEventDispatcher>,
        ast_rules: ASTRules,
    ) -> Result<(bool, Vec<TransactionEvent>), Error> {
        let max_miner_time_ms = settings.max_miner_time_ms;
        let mempool_settings = settings.mempool_settings.clone();
        let ts_start = get_epoch_time_ms();
        let stacks_epoch_id = epoch_tx.get_epoch();
        let block_limit = epoch_tx
            .block_limit()
            .expect("Failed to obtain block limit from miner's block connection");

        let mut tx_events = Vec::new();

        for initial_tx in initial_txs.iter() {
            tx_events.push(
                builder
                    .try_mine_tx(epoch_tx, initial_tx, ast_rules.clone())?
                    .convert_to_event(),
            );
        }

        // nakamoto miner tenure start heuristic:
        //  mine an empty block so you can start your tenure quickly!
        if let Some(tx) = initial_txs.first() {
            if matches!(
                &tx.payload,
                TransactionPayload::TenureChange(TenureChangePayload {
                    cause: TenureChangeCause::BlockFound,
                    ..
                })
            ) {
                debug!("PRINT HERE : {:?}", tx.payload);
                info!("Nakamoto miner heuristic: during tenure change blocks, produce a fast short block to begin tenure");
                return Ok((false, tx_events));
            }
        }

        mempool.reset_nonce_cache()?;
        mempool.estimate_tx_rates(100, &block_limit, &stacks_epoch_id)?;

        let mut block_limit_hit = BlockLimitFunction::NO_LIMIT_HIT;
        let mut considered = HashSet::new(); // txids of all transactions we looked at
        let mut mined_origin_nonces: HashMap<StacksAddress, u64> = HashMap::new(); // map addrs of mined transaction origins to the nonces we used
        let mut mined_sponsor_nonces: HashMap<StacksAddress, u64> = HashMap::new(); // map addrs of mined transaction sponsors to the nonces we used

        let mut invalidated_txs = vec![];
        let mut to_drop_and_blacklist = vec![];
        let mut update_timings = vec![];

        let deadline = ts_start + u128::from(max_miner_time_ms);
        let mut num_txs = 0;
        let mut blocked = false;

        debug!("Block transaction selection begins (parent height = {tip_height})");
        let result = {
            let mut loop_result = Ok(());
            while block_limit_hit != BlockLimitFunction::LIMIT_REACHED {
                let mut num_considered = 0;
                let intermediate_result = mempool.iterate_candidates(
                    epoch_tx,
                    &mut tx_events,
                    mempool_settings.clone(),
                    |epoch_tx, to_consider, estimator| {
                        // first, have we been preempted?
                        blocked = (*settings.miner_status.lock().expect("FATAL: mutex poisoned"))
                            .is_blocked();
                        if blocked {
                            debug!("Miner stopping due to preemption");
                            return Ok(None);
                        }

                        let txinfo = &to_consider.tx;
                        let update_estimator = to_consider.update_estimate;

                        if block_limit_hit == BlockLimitFunction::LIMIT_REACHED {
                            return Ok(None);
                        }
                        let time_now = get_epoch_time_ms();
                        if time_now >= deadline {
                            debug!("Miner mining time exceeded ({} ms)", max_miner_time_ms);
                            return Ok(None);
                        }
                        if let Some(time_estimate) = txinfo.metadata.time_estimate_ms {
                            if time_now.saturating_add(time_estimate.into()) > deadline {
                                debug!("Mining tx would cause us to exceed our deadline, skipping";
                                       "txid" => %txinfo.tx.txid(),
                                       "deadline" => deadline,
                                       "now" => time_now,
                                       "estimate" => time_estimate);
                                return Ok(Some(
                                    TransactionResult::skipped(
                                        &txinfo.tx,
                                        "Transaction would exceed deadline.".into(),
                                    )
                                    .convert_to_event(),
                                ));
                            }
                        }

                        // skip transactions early if we can
                        if considered.contains(&txinfo.tx.txid()) {
                            return Ok(Some(
                                TransactionResult::skipped(
                                    &txinfo.tx,
                                    "Transaction already considered.".to_string(),
                                )
                                .convert_to_event(),
                            ));
                        }

                        if let Some(nonce) = mined_origin_nonces.get(&txinfo.tx.origin_address()) {
                            if *nonce >= txinfo.tx.get_origin_nonce() {
                                return Ok(Some(
                                    TransactionResult::skipped(
                                        &txinfo.tx,
                                        format!(
                                            "Bad origin nonce, tx nonce {} versus {}.",
                                            txinfo.tx.get_origin_nonce(),
                                            *nonce
                                        ),
                                    )
                                    .convert_to_event(),
                                ));
                            }
                        }
                        if let Some(sponsor_addr) = txinfo.tx.sponsor_address() {
                            if let Some(nonce) = mined_sponsor_nonces.get(&sponsor_addr) {
                                if let Some(sponsor_nonce) = txinfo.tx.get_sponsor_nonce() {
                                    if *nonce >= sponsor_nonce {
                                        return Ok(Some(
                                            TransactionResult::skipped(
                                                &txinfo.tx,
                                                format!(
                                                    "Bad sponsor nonce, tx nonce {} versus {}.",
                                                    sponsor_nonce, *nonce
                                                ),
                                            )
                                            .convert_to_event(),
                                        ));
                                    }
                                }
                            }
                        }

                        considered.insert(txinfo.tx.txid());
                        num_considered += 1;

                        let tx_start = Instant::now();
                        let tx_result = builder.try_mine_tx_with_len(
                            epoch_tx,
                            &txinfo.tx,
                            txinfo.metadata.len,
                            &block_limit_hit,
                            ast_rules,
                        );

                        let result_event = tx_result.convert_to_event();
                        match tx_result {
                            TransactionResult::Success(TransactionSuccess {
                                tx: _,
                                fee: _,
                                receipt,
                                soft_limit_reached,
                            }) => {
                                if txinfo.metadata.time_estimate_ms.is_none() {
                                    // use i64 to avoid running into issues when storing in
                                    //  rusqlite.
                                    let time_estimate_ms: i64 = tx_start
                                        .elapsed()
                                        .as_millis()
                                        .try_into()
                                        .unwrap_or(i64::MAX);
                                    let time_estimate_ms: u64 = time_estimate_ms
                                        .try_into()
                                        // should be unreachable
                                        .unwrap_or(0);
                                    update_timings.push((txinfo.tx.txid(), time_estimate_ms));
                                }

                                num_txs += 1;
                                if update_estimator {
                                    if let Err(e) = estimator.notify_event(
                                        &txinfo.tx.payload,
                                        &receipt.execution_cost,
                                        &block_limit,
                                        &stacks_epoch_id,
                                    ) {
                                        warn!("Error updating estimator";
                                              "txid" => %txinfo.metadata.txid,
                                              "error" => ?e);
                                    }
                                }
                                mined_origin_nonces.insert(
                                    txinfo.tx.origin_address(),
                                    txinfo.tx.get_origin_nonce(),
                                );
                                if let (Some(sponsor_addr), Some(sponsor_nonce)) =
                                    (txinfo.tx.sponsor_address(), txinfo.tx.get_sponsor_nonce())
                                {
                                    mined_sponsor_nonces.insert(sponsor_addr, sponsor_nonce);
                                }
                                if soft_limit_reached {
                                    // done mining -- our soft limit execution budget is exceeded.
                                    // Make the block from the transactions we did manage to get
                                    debug!(
                                        "Soft block budget exceeded on tx {}",
                                        &txinfo.tx.txid()
                                    );
                                    if block_limit_hit != BlockLimitFunction::CONTRACT_LIMIT_HIT {
                                        debug!("Switch to mining stx-transfers only");
                                        block_limit_hit = BlockLimitFunction::CONTRACT_LIMIT_HIT;
                                    }
                                }
                            }
                            TransactionResult::Skipped(TransactionSkipped { error, .. })
                            | TransactionResult::ProcessingError(TransactionError {
                                error, ..
                            }) => {
                                match &error {
                                    Error::StacksTransactionSkipped(_) => {}
                                    Error::BlockTooBigError => {
                                        // done mining -- our execution budget is exceeded.
                                        // Make the block from the transactions we did manage to get
                                        debug!("Block budget exceeded on tx {}", &txinfo.tx.txid());
                                        if block_limit_hit == BlockLimitFunction::NO_LIMIT_HIT {
                                            debug!("Switch to mining stx-transfers only");
                                            block_limit_hit =
                                                BlockLimitFunction::CONTRACT_LIMIT_HIT;
                                        } else if block_limit_hit
                                            == BlockLimitFunction::CONTRACT_LIMIT_HIT
                                        {
                                            debug!(
                                                "Stop mining anchored block due to limit exceeded"
                                            );
                                            block_limit_hit = BlockLimitFunction::LIMIT_REACHED;
                                            return Ok(None);
                                        }
                                    }
                                    Error::TransactionTooBigError(measured_cost) => {
                                        if update_estimator {
                                            if let Some(measured_cost) = measured_cost {
                                                if let Err(e) = estimator.notify_event(
                                                    &txinfo.tx.payload,
                                                    measured_cost,
                                                    &block_limit,
                                                    &stacks_epoch_id,
                                                ) {
                                                    warn!("Error updating estimator";
                                                                  "txid" => %txinfo.metadata.txid,
                                                                  "error" => ?e);
                                                }
                                            }
                                        }

                                        invalidated_txs.push(txinfo.metadata.txid);
                                    }
                                    Error::InvalidStacksTransaction(_, true) => {
                                        // if we have an invalid transaction that was quietly ignored, don't warn here either
                                    }
                                    e => {
                                        info!("Failed to apply tx {}: {:?}", &txinfo.tx.txid(), &e);
                                        return Ok(Some(result_event));
                                    }
                                }
                            }
                            TransactionResult::Problematic(TransactionProblematic {
                                tx, ..
                            }) => {
                                // drop from the mempool
                                debug!("Drop and blacklist problematic transaction {}", &tx.txid());
                                to_drop_and_blacklist.push(tx.txid());
                            }
                        }

                        Ok(Some(result_event))
                    },
                );

                if !update_timings.is_empty() {
                    if let Err(e) = mempool.update_tx_time_estimates(&update_timings) {
                        warn!("Error while updating time estimates for mempool"; "err" => ?e);
                    }
                }

                if !to_drop_and_blacklist.is_empty() {
                    let _ = mempool.drop_and_blacklist_txs(&to_drop_and_blacklist);
                }

                match intermediate_result {
                    Err(e) => {
                        loop_result = Err(e);
                        break;
                    }
                    Ok((_txs_considered, stop_reason)) => {
                        match stop_reason {
                            MempoolIterationStopReason::NoMoreCandidates => break,
                            MempoolIterationStopReason::DeadlineReached => break,
                            // if the iterator function exited, let the loop tick: it checks the block limits
                            MempoolIterationStopReason::IteratorExited => {}
                        }
                    }
                }

                if num_considered == 0 {
                    break;
                }
            }
            debug!("Block transaction selection finished (parent height {}): {} transactions selected ({} considered)", &tip_height, num_txs, considered.len());
            loop_result
        };

        mempool.drop_txs(&invalidated_txs)?;

        if let Some(observer) = event_observer {
            observer.mempool_txs_dropped(invalidated_txs, None, MemPoolDropReason::TOO_EXPENSIVE);
            observer.mempool_txs_dropped(
                to_drop_and_blacklist,
                None,
                MemPoolDropReason::PROBLEMATIC,
            );
        }

        if let Err(e) = result {
            warn!("Failure building block: {}", e);
            return Err(e);
        }

        Ok((blocked, tx_events))
    }

    // TODO: add tests from mutation testing results #4861
    // Or keep the skip and remove the comment
    #[cfg_attr(test, mutants::skip)]
    /// Given access to the mempool, mine an anchored block with no more than the given execution cost.
    ///   returns the assembled block, and the consumed execution budget.
    pub fn build_anchored_block(
        chainstate_handle: &StacksChainState, // not directly used; used as a handle to open other chainstates
        burn_dbconn: &SortitionHandleConn,
        mempool: &mut MemPoolDB,
        parent_stacks_header: &StacksHeaderInfo, // Stacks header we're building off of
        total_burn: u64, // the burn so far on the burnchain (i.e. from the last burnchain block)
        proof: VRFProof, // proof over the burnchain's last seed
        pubkey_hash: Hash160,
        coinbase_tx: &StacksTransaction,
        settings: BlockBuilderSettings,
        event_observer: Option<&dyn MemPoolEventDispatcher>,
        burnchain: &Burnchain,
    ) -> Result<(StacksBlock, ExecutionCost, u64), Error> {
        if !matches!(coinbase_tx.payload, TransactionPayload::Coinbase(..)) {
            return Err(Error::MemPoolError(
                "Not a coinbase transaction".to_string(),
            ));
        }

        let (tip_consensus_hash, tip_block_hash, tip_height) = (
            parent_stacks_header.consensus_hash.clone(),
            parent_stacks_header.anchored_header.block_hash(),
            parent_stacks_header.stacks_block_height,
        );

        debug!(
            "Build anchored block off of {}/{} height {}",
            &tip_consensus_hash, &tip_block_hash, tip_height
        );

        let (mut chainstate, _) = chainstate_handle.reopen()?;

        let mut builder = StacksBlockBuilder::make_block_builder(
            burnchain,
            chainstate.mainnet,
            parent_stacks_header,
            proof,
            total_burn,
            pubkey_hash,
        )?;

        if !settings.confirm_microblocks {
            builder.parent_microblock_hash = None;
        }

        let ts_start = get_epoch_time_ms();

        let mut miner_epoch_info =
            builder.pre_epoch_begin(&mut chainstate, burn_dbconn, settings.confirm_microblocks)?;
        let ast_rules = miner_epoch_info.ast_rules;
        if ast_rules != ASTRules::Typical {
            builder.header.version = cmp::max(
                STACKS_BLOCK_VERSION_AST_PRECHECK_SIZE,
                builder.header.version,
            );
        }

        let (mut epoch_tx, confirmed_mblock_cost) =
            builder.epoch_begin(burn_dbconn, &mut miner_epoch_info)?;

        let block_limit = epoch_tx
            .block_limit()
            .expect("Failed to obtain block limit from miner's block connection");

        let (blocked, tx_events) = match Self::select_and_apply_transactions(
            &mut epoch_tx,
            &mut builder,
            mempool,
            parent_stacks_header.stacks_block_height,
            &[coinbase_tx.clone()],
            settings,
            event_observer,
            ast_rules,
        ) {
            Ok(x) => x,
            Err(e) => {
                warn!("Failure building block: {}", e);
                epoch_tx.rollback_block();
                return Err(e);
            }
        };

        if blocked {
            debug!(
                "Miner: Anchored block transaction selection aborted (child of {})",
                &parent_stacks_header.anchored_header.block_hash()
            );
            return Err(Error::MinerAborted);
        }

        // save the block so we can build microblocks off of it
        let block = builder.mine_anchored_block(&mut epoch_tx);
        let size = builder.bytes_so_far;
        let consumed = builder.epoch_finish(epoch_tx)?;

        let ts_end = get_epoch_time_ms();

        if let Some(observer) = event_observer {
            observer.mined_block_event(
                SortitionDB::get_canonical_burn_chain_tip(burn_dbconn.conn())?.block_height + 1,
                &block,
                size,
                &consumed,
                &confirmed_mblock_cost,
                tx_events,
            );
        }

        set_last_mined_block_transaction_count(
            u64::try_from(block.txs.len()).expect("more than 2^64 txs"),
        );
        set_last_mined_execution_cost_observed(&consumed, &block_limit);

        info!(
            "Miner: mined anchored block";
            "stacks_block_hash" => %block.block_hash(),
            "height" => block.header.total_work.work,
            "tx_count" => block.txs.len(),
            "parent_stacks_block_hash" => %block.header.parent_block,
            "parent_stacks_microblock" => %block.header.parent_microblock,
            "parent_stacks_microblock_seq" => block.header.parent_microblock_sequence,
            "block_size" => size,
            "execution_consumed" => %consumed,
            "%-full" => block_limit.proportion_largest_dimension(&consumed),
            "assembly_time_ms" => ts_end.saturating_sub(ts_start),
            "tx_fees_microstacks" => block.txs.iter().fold(0, |agg: u64, tx| {
                agg.saturating_add(tx.get_tx_fee())
            })
        );

        Ok((block, consumed, size))
    }
}

impl BlockBuilder for StacksBlockBuilder {
    /// Append a transaction if doing so won't exceed the epoch data size.
    /// Errors out if we exceed budget, or the transaction is invalid.
    fn try_mine_tx_with_len(
        &mut self,
        clarity_tx: &mut ClarityTx,
        tx: &StacksTransaction,
        tx_len: u64,
        limit_behavior: &BlockLimitFunction,
        ast_rules: ASTRules,
    ) -> TransactionResult {
        if self.bytes_so_far + tx_len >= MAX_EPOCH_SIZE.into() {
            return TransactionResult::skipped_due_to_error(tx, Error::BlockTooBigError);
        }

        match limit_behavior {
            BlockLimitFunction::CONTRACT_LIMIT_HIT => {
                match &tx.payload {
                    TransactionPayload::ContractCall(cc) => {
                        // once we've hit the runtime limit once, allow boot code contract calls, but do not try to eval
                        //   other contract calls
                        if !cc.address.is_boot_code_addr() {
                            return TransactionResult::skipped(
                                tx,
                                "BlockLimitFunction::CONTRACT_LIMIT_HIT".to_string(),
                            );
                        }
                    }
                    TransactionPayload::SmartContract(..) => {
                        return TransactionResult::skipped(
                            tx,
                            "BlockLimitFunction::CONTRACT_LIMIT_HIT".to_string(),
                        );
                    }
                    _ => {}
                }
            }
            BlockLimitFunction::LIMIT_REACHED => {
                return TransactionResult::skipped(
                    tx,
                    "BlockLimitFunction::LIMIT_REACHED".to_string(),
                )
            }
            BlockLimitFunction::NO_LIMIT_HIT => {}
        };

        let quiet = !cfg!(test);
        let result = if !self.anchored_done {
            // building up the anchored blocks
            if tx.anchor_mode != TransactionAnchorMode::OnChainOnly
                && tx.anchor_mode != TransactionAnchorMode::Any
            {
                return TransactionResult::skipped_due_to_error(
                    tx,
                    Error::InvalidStacksTransaction(
                        "Invalid transaction anchor mode for anchored data".to_string(),
                        false,
                    ),
                );
            }

            // preemptively skip problematic transactions
            if let Err(e) = Relayer::static_check_problematic_relayed_tx(
                clarity_tx.config.mainnet,
                clarity_tx.get_epoch(),
                tx,
                ast_rules,
            ) {
                info!(
                    "Detected problematic tx {} while mining; dropping from mempool",
                    tx.txid()
                );
                return TransactionResult::problematic(tx, Error::NetError(e));
            }
            let (fee, receipt) = match StacksChainState::process_transaction(
                clarity_tx, tx, quiet, ast_rules,
            ) {
                Ok((fee, receipt)) => (fee, receipt),
                Err(e) => {
                    let (is_problematic, e) =
                        TransactionResult::is_problematic(tx, e, clarity_tx.get_epoch());
                    if is_problematic {
                        return TransactionResult::problematic(tx, e);
                    } else {
                        match e {
                            Error::CostOverflowError(cost_before, cost_after, total_budget) => {
                                clarity_tx.reset_cost(cost_before.clone());
                                if total_budget.proportion_largest_dimension(&cost_before)
                                    < TX_BLOCK_LIMIT_PROPORTION_HEURISTIC
                                {
                                    warn!(
                                            "Transaction {} consumed over {}% of block budget, marking as invalid; budget was {}",
                                            tx.txid(),
                                            100 - TX_BLOCK_LIMIT_PROPORTION_HEURISTIC,
                                            &total_budget
                                        );
                                    let mut measured_cost = cost_after;
                                    let measured_cost = if measured_cost.sub(&cost_before).is_ok() {
                                        Some(measured_cost)
                                    } else {
                                        warn!(
                                        "Failed to compute measured cost of a too big transaction"
                                    );
                                        None
                                    };
                                    return TransactionResult::error(
                                        tx,
                                        Error::TransactionTooBigError(measured_cost),
                                    );
                                } else {
                                    warn!(
                                        "Transaction {} reached block cost {}; budget was {}",
                                        tx.txid(),
                                        &cost_after,
                                        &total_budget
                                    );
                                    return TransactionResult::skipped_due_to_error(
                                        tx,
                                        Error::BlockTooBigError,
                                    );
                                }
                            }
                            _ => return TransactionResult::error(tx, e),
                        }
                    }
                }
            };
            info!("Include tx";
                  "tx" => %tx.txid(),
                  "payload" => tx.payload.name(),
                  "origin" => %tx.origin_address());

            // save
            self.txs.push(tx.clone());
            self.total_anchored_fees += fee;

            TransactionResult::success(tx, fee, receipt)
        } else {
            // building up the microblocks
            if tx.anchor_mode != TransactionAnchorMode::OffChainOnly
                && tx.anchor_mode != TransactionAnchorMode::Any
            {
                return TransactionResult::skipped_due_to_error(
                    tx,
                    Error::InvalidStacksTransaction(
                        "Invalid transaction anchor mode for streamed data".to_string(),
                        false,
                    ),
                );
            }

            // preemptively skip problematic transactions
            if let Err(e) = Relayer::static_check_problematic_relayed_tx(
                clarity_tx.config.mainnet,
                clarity_tx.get_epoch(),
                tx,
                ast_rules,
            ) {
                info!(
                    "Detected problematic tx {} while mining; dropping from mempool",
                    tx.txid()
                );
                return TransactionResult::problematic(tx, Error::NetError(e));
            }
            let (fee, receipt) = match StacksChainState::process_transaction(
                clarity_tx, tx, quiet, ast_rules,
            ) {
                Ok((fee, receipt)) => (fee, receipt),
                Err(e) => {
                    let (is_problematic, e) =
                        TransactionResult::is_problematic(tx, e, clarity_tx.get_epoch());
                    if is_problematic {
                        return TransactionResult::problematic(tx, e);
                    } else {
                        match e {
                            Error::CostOverflowError(cost_before, cost_after, total_budget) => {
                                clarity_tx.reset_cost(cost_before.clone());
                                if total_budget.proportion_largest_dimension(&cost_before)
                                    < TX_BLOCK_LIMIT_PROPORTION_HEURISTIC
                                {
                                    warn!(
                                        "Transaction {} consumed over {}% of block budget, marking as invalid; budget was {}",
                                        tx.txid(),
                                        100 - TX_BLOCK_LIMIT_PROPORTION_HEURISTIC,
                                        &total_budget
                                    );
                                    let mut measured_cost = cost_after;
                                    let measured_cost = if measured_cost.sub(&cost_before).is_ok() {
                                        Some(measured_cost)
                                    } else {
                                        warn!(
                                        "Failed to compute measured cost of a too big transaction"
                                    );
                                        None
                                    };

                                    return TransactionResult::error(
                                        tx,
                                        Error::TransactionTooBigError(measured_cost),
                                    );
                                } else {
                                    warn!(
                                        "Transaction {} reached block cost {cost_after}; budget was {total_budget}",
                                        tx.txid()
                                    );
                                    return TransactionResult::skipped_due_to_error(
                                        tx,
                                        Error::BlockTooBigError,
                                    );
                                }
                            }
                            _ => return TransactionResult::error(tx, e),
                        }
                    }
                }
            };
            debug!(
                "Include tx {} ({}) in microblock",
                tx.txid(),
                tx.payload.name()
            );

            // save
            self.micro_txs.push(tx.clone());
            self.total_streamed_fees += fee;

            TransactionResult::success(tx, fee, receipt)
        };

        self.bytes_so_far += tx_len;
        result
    }
}
