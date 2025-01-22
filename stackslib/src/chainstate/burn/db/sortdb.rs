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

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::io::{ErrorKind, Write};
use std::ops::{Deref, DerefMut};
use std::str::FromStr;
use std::{cmp, fmt, fs};

use clarity::vm::ast::ASTRules;
use clarity::vm::costs::ExecutionCost;
use clarity::vm::representations::{ClarityName, ContractName};
use clarity::vm::types::{PrincipalData, Value};
use rand;
use rand::RngCore;
use rusqlite::types::ToSql;
use rusqlite::{
    params, Connection, Error as sqlite_error, OpenFlags, OptionalExtension, Row, Transaction,
};
use sha2::{Digest, Sha512_256};
use stacks_common::address::AddressHashMode;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, StacksAddress, StacksBlockId,
    TrieHash, VRFSeed,
};
use stacks_common::types::sqlite::NO_PARAMS;
use stacks_common::types::StacksPublicKeyBuffer;
use stacks_common::util::hash::{hex_bytes, to_hex, Hash160, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{MessageSignature, Secp256k1PublicKey};
use stacks_common::util::vrf::*;
use stacks_common::util::{get_epoch_time_secs, log};

use crate::burnchains::affirmation::{AffirmationMap, AffirmationMapEntry};
use crate::burnchains::bitcoin::BitcoinNetworkType;
use crate::burnchains::db::{BurnchainDB, BurnchainHeaderReader};
use crate::burnchains::{
    Address, Burnchain, BurnchainBlockHeader, BurnchainRecipient, BurnchainSigner,
    BurnchainStateTransition, BurnchainStateTransitionOps, BurnchainTransaction, BurnchainView,
    Error as BurnchainError, PoxConstants, PublicKey, Txid,
};
use crate::chainstate::burn::operations::leader_block_commit::{
    MissedBlockCommit, RewardSetInfo, OUTPUTS_PER_COMMIT,
};
use crate::chainstate::burn::operations::{
    BlockstackOperationType, DelegateStxOp, LeaderBlockCommitOp, LeaderKeyRegisterOp, PreStxOp,
    StackStxOp, TransferStxOp, VoteForAggregateKeyOp,
};
use crate::chainstate::burn::{
    BlockSnapshot, ConsensusHash, ConsensusHashExtensions, Opcodes, OpsHash, SortitionHash,
};
use crate::chainstate::coordinator::{
    Error as CoordinatorError, PoxAnchorBlockStatus, RewardCycleInfo, SortitionDBMigrator,
};
use crate::chainstate::nakamoto::{NakamotoBlockHeader, NakamotoChainState};
use crate::chainstate::stacks::address::{PoxAddress, StacksAddressExtensions};
use crate::chainstate::stacks::boot::PoxStartCycleInfo;
use crate::chainstate::stacks::db::{StacksBlockHeaderTypes, StacksChainState, StacksHeaderInfo};
use crate::chainstate::stacks::index::marf::{MARFOpenOpts, MarfConnection, MARF};
use crate::chainstate::stacks::index::storage::TrieFileStorage;
use crate::chainstate::stacks::index::{
    ClarityMarfTrieId, Error as MARFError, MARFValue, MarfTrieId,
};
use crate::chainstate::stacks::{StacksPublicKey, *};
use crate::chainstate::ChainstateDB;
use crate::core::{
    StacksEpoch, StacksEpochExtension, StacksEpochId, AST_RULES_PRECHECK_SIZE,
    FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH, STACKS_EPOCH_MAX,
};
use crate::net::neighbors::MAX_NEIGHBOR_BLOCK_DELAY;
use crate::util_lib::db::{
    db_mkdirs, get_ancestor_block_hash, opt_u64_to_sql, query_count, query_row, query_row_columns,
    query_row_panic, query_rows, sql_pragma, table_exists, tx_begin_immediate, tx_busy_handler,
    u64_to_sql, DBConn, DBTx, Error as db_error, FromColumn, FromRow, IndexDBConn, IndexDBTx,
};

const BLOCK_HEIGHT_MAX: u64 = (1 << 63) - 1;

pub const REWARD_WINDOW_START: u64 = 144 * 15;
pub const REWARD_WINDOW_END: u64 = 144 * 90 + REWARD_WINDOW_START;

pub type BlockHeaderCache = HashMap<ConsensusHash, (Option<BlockHeaderHash>, ConsensusHash)>;

impl FromRow<SortitionId> for SortitionId {
    fn from_row(row: &Row) -> Result<SortitionId, db_error> {
        SortitionId::from_column(row, "sortition_id")
    }
}

impl FromRow<ConsensusHash> for ConsensusHash {
    fn from_row(row: &Row) -> Result<ConsensusHash, db_error> {
        ConsensusHash::from_column(row, "consensus_hash")
    }
}

impl FromRow<BurnchainHeaderHash> for BurnchainHeaderHash {
    fn from_row(row: &Row) -> Result<BurnchainHeaderHash, db_error> {
        BurnchainHeaderHash::from_column(row, "burn_header_hash")
    }
}

impl FromRow<MissedBlockCommit> for MissedBlockCommit {
    fn from_row(row: &Row) -> Result<MissedBlockCommit, db_error> {
        let intended_sortition = SortitionId::from_column(row, "intended_sortition_id")?;
        let input_json: String = row.get_unwrap("input");
        let input = serde_json::from_str(&input_json).map_err(db_error::SerializationError)?;
        let txid = Txid::from_column(row, "txid")?;

        Ok(MissedBlockCommit {
            input,
            txid,
            intended_sortition,
        })
    }
}

impl FromRow<BlockSnapshot> for BlockSnapshot {
    fn from_row(row: &Row) -> Result<BlockSnapshot, db_error> {
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let burn_header_timestamp = u64::from_column(row, "burn_header_timestamp")?;
        let parent_burn_header_hash =
            BurnchainHeaderHash::from_column(row, "parent_burn_header_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let ops_hash = OpsHash::from_column(row, "ops_hash")?;
        let total_burn_str: String = row.get_unwrap("total_burn");
        let sortition: bool = row.get_unwrap("sortition");
        let sortition_hash = SortitionHash::from_column(row, "sortition_hash")?;
        let winning_block_txid = Txid::from_column(row, "winning_block_txid")?;
        let winning_stacks_block_hash =
            BlockHeaderHash::from_column(row, "winning_stacks_block_hash")?;
        let index_root = TrieHash::from_column(row, "index_root")?;
        let num_sortitions = u64::from_column(row, "num_sortitions")?;

        // information we learn about the stacks block this snapshot committedto
        let stacks_block_accepted: bool = row.get_unwrap("stacks_block_accepted");
        let stacks_block_height = u64::from_column(row, "stacks_block_height")?;
        let arrival_index = u64::from_column(row, "arrival_index")?;

        // information about what we have determined about the stacks chain tip.
        // This is memoized to a given canonical chain tip block.
        let canonical_stacks_tip_height = u64::from_column(row, "canonical_stacks_tip_height")?;
        let canonical_stacks_tip_hash =
            BlockHeaderHash::from_column(row, "canonical_stacks_tip_hash")?;
        let canonical_stacks_tip_consensus_hash =
            ConsensusHash::from_column(row, "canonical_stacks_tip_consensus_hash")?;

        // identifiers derived from PoX forking state
        let sortition_id = SortitionId::from_column(row, "sortition_id")?;
        let parent_sortition_id = SortitionId::from_column(row, "parent_sortition_id")?;
        let pox_valid = row.get_unwrap("pox_valid");

        let accumulated_coinbase_ustx_str: String = row.get_unwrap("accumulated_coinbase_ustx");
        let accumulated_coinbase_ustx = accumulated_coinbase_ustx_str
            .parse::<u128>()
            .expect("DB CORRUPTION: failed to parse stored value");

        let total_burn = total_burn_str
            .parse::<u64>()
            .map_err(|_e| db_error::ParseError)?;

        let miner_pk_hash = row.get("miner_pk_hash")?;

        let snapshot = BlockSnapshot {
            block_height,
            burn_header_timestamp,
            burn_header_hash,
            parent_burn_header_hash,
            consensus_hash,
            ops_hash,
            total_burn,
            sortition,
            sortition_hash,
            winning_block_txid,
            winning_stacks_block_hash,
            index_root,
            num_sortitions,

            stacks_block_accepted,
            stacks_block_height,
            arrival_index,

            canonical_stacks_tip_height,
            canonical_stacks_tip_hash,
            canonical_stacks_tip_consensus_hash,

            sortition_id,
            parent_sortition_id,
            pox_valid,
            accumulated_coinbase_ustx,

            miner_pk_hash,
        };
        Ok(snapshot)
    }
}

impl FromRow<LeaderKeyRegisterOp> for LeaderKeyRegisterOp {
    fn from_row(row: &Row) -> Result<LeaderKeyRegisterOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let public_key = VRFPublicKey::from_column(row, "public_key")?;
        let memo_hex: String = row.get_unwrap("memo");

        let memo_bytes = hex_bytes(&memo_hex).map_err(|_e| db_error::ParseError)?;

        let memo = memo_bytes.to_vec();

        let leader_key_row = LeaderKeyRegisterOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,

            consensus_hash,
            public_key,
            memo,
        };

        Ok(leader_key_row)
    }
}

impl FromRow<LeaderBlockCommitOp> for LeaderBlockCommitOp {
    fn from_row(row: &Row) -> Result<LeaderBlockCommitOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let block_header_hash = BlockHeaderHash::from_column(row, "block_header_hash")?;
        let new_seed = VRFSeed::from_column(row, "new_seed")?;
        let parent_block_ptr: u32 = row.get_unwrap("parent_block_ptr");
        let parent_vtxindex: u16 = row.get_unwrap("parent_vtxindex");
        let key_block_ptr: u32 = row.get_unwrap("key_block_ptr");
        let key_vtxindex: u16 = row.get_unwrap("key_vtxindex");
        let memo_hex: String = row.get_unwrap("memo");
        let burn_fee_str: String = row.get_unwrap("burn_fee");
        let input_json: String = row.get_unwrap("input");
        let apparent_sender_json: String = row.get_unwrap("apparent_sender");
        let sunset_burn_str: String = row.get_unwrap("sunset_burn");

        let commit_outs = serde_json::from_value(row.get_unwrap("commit_outs"))
            .expect("Unparseable value stored to database");

        let memo_bytes = hex_bytes(&memo_hex).map_err(|_e| db_error::ParseError)?;

        let memo = memo_bytes.to_vec();

        let input = serde_json::from_str(&input_json).map_err(db_error::SerializationError)?;

        let apparent_sender =
            serde_json::from_str(&apparent_sender_json).map_err(db_error::SerializationError)?;

        let burn_fee = burn_fee_str
            .parse::<u64>()
            .expect("DB Corruption: burn fee is not parseable as u64");

        let sunset_burn = sunset_burn_str
            .parse::<u64>()
            .expect("DB Corruption: Sunset burn is not parseable as u64");

        let burn_parent_modulus: u8 = row.get_unwrap("burn_parent_modulus");

        let punished_str: Option<String> = row.get_unwrap("punished");
        let punished = punished_str
            .as_deref()
            .map(serde_json::from_str)
            .transpose()
            .map_err(db_error::SerializationError)?
            .unwrap_or_default();

        let block_commit = LeaderBlockCommitOp {
            block_header_hash,
            new_seed,
            parent_block_ptr,
            parent_vtxindex,
            key_block_ptr,
            key_vtxindex,
            memo,
            burn_parent_modulus,

            burn_fee,
            input,
            apparent_sender,
            commit_outs,
            sunset_burn,
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            treatment: punished,
        };
        Ok(block_commit)
    }
}

impl FromRow<StackStxOp> for StackStxOp {
    fn from_row(row: &Row) -> Result<StackStxOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let reward_addr = PoxAddress::from_column(row, "reward_addr")?;
        let stacked_ustx_str: String = row.get_unwrap("stacked_ustx");
        let stacked_ustx = u128::from_str_radix(&stacked_ustx_str, 10)
            .expect("CORRUPTION: bad u128 written to sortdb");
        let num_cycles = row.get_unwrap("num_cycles");
        let signing_key_str_opt: Option<String> = row.get("signer_key")?;
        let signer_key = match signing_key_str_opt {
            Some(key_str) => serde_json::from_str(&key_str).ok(),
            None => None,
        };
        let max_amount_str_opt: Option<String> = row.get("max_amount")?;
        let max_amount = match max_amount_str_opt {
            Some(max_amount_str) => u128::from_str_radix(&max_amount_str, 10)
                .map_err(|_| db_error::ParseError)
                .ok(),
            None => None,
        };
        let auth_id = row.get("auth_id")?;

        Ok(StackStxOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            reward_addr,
            stacked_ustx,
            num_cycles,
            signer_key,
            max_amount,
            auth_id,
        })
    }
}

impl FromRow<DelegateStxOp> for DelegateStxOp {
    fn from_row(row: &Row) -> Result<DelegateStxOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let delegate_to = StacksAddress::from_column(row, "delegate_to")?;
        let reward_addr_str: String = row.get_unwrap("reward_addr");
        let reward_addr = serde_json::from_str(&reward_addr_str)
            .expect("CORRUPTION: DB stored bad transition ops");

        let delegated_ustx_str: String = row.get_unwrap("delegated_ustx");
        let delegated_ustx = u128::from_str_radix(&delegated_ustx_str, 10)
            .expect("CORRUPTION: bad u128 written to sortdb");
        let until_burn_height = u64::from_column(row, "until_burn_height")?;

        Ok(DelegateStxOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            delegate_to,
            reward_addr,
            delegated_ustx,
            until_burn_height,
        })
    }
}

impl FromRow<TransferStxOp> for TransferStxOp {
    fn from_row(row: &Row) -> Result<TransferStxOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let recipient = StacksAddress::from_column(row, "recipient_addr")?;
        let transfered_ustx_str: String = row.get_unwrap("transfered_ustx");
        let transfered_ustx = u128::from_str_radix(&transfered_ustx_str, 10)
            .expect("CORRUPTION: bad u128 written to sortdb");
        let memo_hex: String = row.get_unwrap("memo");
        let memo = hex_bytes(&memo_hex).map_err(|_| db_error::Corruption)?;

        Ok(TransferStxOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            recipient,
            transfered_ustx,
            memo,
        })
    }
}

impl FromRow<VoteForAggregateKeyOp> for VoteForAggregateKeyOp {
    fn from_row(row: &Row) -> Result<VoteForAggregateKeyOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let aggregate_key_str: String = row.get_unwrap("aggregate_key");
        let aggregate_key: StacksPublicKeyBuffer = serde_json::from_str(&aggregate_key_str)
            .expect("CORRUPTION: DB stored bad transition ops");
        let round: u32 = row.get_unwrap("round");
        let reward_cycle = u64::from_column(row, "reward_cycle")?;
        let signer_index: u16 = row.get_unwrap("signer_index");
        let signer_key_str: String = row.get_unwrap("signer_key");
        let signer_key: StacksPublicKeyBuffer = serde_json::from_str(&signer_key_str)
            .expect("CORRUPTION: DB stored bad transition ops");

        Ok(VoteForAggregateKeyOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            aggregate_key,
            round,
            reward_cycle,
            signer_index,
            signer_key,
        })
    }
}

impl FromColumn<ASTRules> for ASTRules {
    fn from_column(row: &Row, column_name: &str) -> Result<ASTRules, db_error> {
        let x: u8 = row.get_unwrap(column_name);
        let ast_rules = ASTRules::from_u8(x).ok_or(db_error::ParseError)?;
        Ok(ast_rules)
    }
}

impl FromRow<(ASTRules, u64)> for (ASTRules, u64) {
    fn from_row(row: &Row) -> Result<(ASTRules, u64), db_error> {
        let ast_rules = ASTRules::from_column(row, "ast_rule_id")?;
        let height = u64::from_column(row, "block_height")?;
        Ok((ast_rules, height))
    }
}

struct AcceptedStacksBlockHeader {
    pub tip_consensus_hash: ConsensusHash, // PoX tip
    pub consensus_hash: ConsensusHash,     // stacks block consensus hash
    pub block_hash: BlockHeaderHash,       // stacks block hash
    pub height: u64,                       // stacks block height
}

#[derive(Debug)]
pub struct InitialMiningBonus {
    pub total_reward: u128,
    pub per_block: u128,
}

impl FromRow<AcceptedStacksBlockHeader> for AcceptedStacksBlockHeader {
    fn from_row(row: &Row) -> Result<AcceptedStacksBlockHeader, db_error> {
        let tip_consensus_hash = ConsensusHash::from_column(row, "tip_consensus_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let block_hash = BlockHeaderHash::from_column(row, "stacks_block_hash")?;
        let height = u64::from_column(row, "block_height")?;

        Ok(AcceptedStacksBlockHeader {
            tip_consensus_hash,
            consensus_hash,
            block_hash,
            height,
        })
    }
}

impl FromRow<StacksEpoch> for StacksEpoch {
    fn from_row(row: &Row) -> Result<StacksEpoch, db_error> {
        let epoch_id_u32: u32 = row.get_unwrap("epoch_id");
        let epoch_id = StacksEpochId::try_from(epoch_id_u32).map_err(|_| db_error::ParseError)?;

        let start_height = u64::from_column(row, "start_block_height")?;
        let end_height = u64::from_column(row, "end_block_height")?;

        let network_epoch: u8 = row.get_unwrap("network_epoch");

        let block_limit = row.get_unwrap("block_limit");
        Ok(StacksEpoch {
            epoch_id,
            start_height,
            end_height,
            block_limit,
            network_epoch,
        })
    }
}

pub const SORTITION_DB_VERSION: &str = "9";

const SORTITION_DB_INITIAL_SCHEMA: &[&str] = &[
    r#"
    PRAGMA foreign_keys = ON;
    "#,
    r#"
    -- sortition snapshots -- snapshot of all transactions processed in a burn block
    -- organizes the set of forks in the burn chain as well.
    CREATE TABLE snapshots(
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT UNIQUE NOT NULL,
        parent_sortition_id TEXT NOT NULL,
        burn_header_timestamp INT NOT NULL,
        parent_burn_header_hash TEXT NOT NULL,
        consensus_hash TEXT UNIQUE NOT NULL,
        ops_hash TEXT NOT NULL,
        total_burn TEXT NOT NULL,
        sortition INTEGER NOT NULL,
        sortition_hash TEXT NOT NULL,
        winning_block_txid TEXT NOT NULL,
        winning_stacks_block_hash TEXT NOT NULL,
        index_root TEXT UNIQUE NOT NULL,

        num_sortitions INTEGER NOT NULL,

        stacks_block_accepted INTEGER NOT NULL,        -- set to 1 if we fetched and processed this Stacks block
        stacks_block_height INTEGER NOT NULL,           -- set to the height of the stacks block, once it's processed
        arrival_index INTEGER NOT NULL,                 -- (global) order in which this Stacks block was processed

        canonical_stacks_tip_height INTEGER NOT NULL,   -- height of highest known Stacks fork in this burn chain fork
        canonical_stacks_tip_hash TEXT NOT NULL,        -- hash of highest known Stacks fork's tip block in this burn chain fork
        canonical_stacks_tip_consensus_hash TEXT NOT NULL,   -- burn hash of highest known Stacks fork's tip block in this burn chain fork

        pox_valid INTEGER NOT NULL,

        accumulated_coinbase_ustx TEXT NOT NULL,

        -- JSON-serialized total PoX payouts
        pox_payouts TEXT NOT NULL,

        PRIMARY KEY(sortition_id)
    );"#,
    r#"
    CREATE TABLE snapshot_transition_ops(
      sortition_id TEXT PRIMARY KEY,
      accepted_ops TEXT NOT NULL,
      consumed_keys TEXT NOT NULL
    );"#,
    r#"
    -- all leader keys registered in the blockchain.
    -- contains pointers to the burn block and fork in which they occur
    CREATE TABLE leader_keys(
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT NOT NULL,

        consensus_hash TEXT NOT NULL,
        public_key TEXT NOT NULL,
        memo TEXT,

        PRIMARY KEY(txid,sortition_id),
        FOREIGN KEY(sortition_id) REFERENCES snapshots(sortition_id)
    );"#,
    r#"
    CREATE TABLE block_commits(
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT NOT NULL,

        block_header_hash TEXT NOT NULL,
        new_seed TEXT NOT NULL,
        parent_block_ptr INTEGER NOT NULL,
        parent_vtxindex INTEGER NOT NULL,
        key_block_ptr INTEGER NOT NULL,
        key_vtxindex INTEGER NOT NULL,
        memo TEXT,
        commit_outs TEXT,
        burn_fee TEXT NOT NULL,     -- use text to encode really big numbers
        sunset_burn TEXT NOT NULL,     -- use text to encode really big numbers
        input TEXT NOT NULL,
        apparent_sender TEXT NOT NULL,
        burn_parent_modulus INTEGER NOT NULL,

        PRIMARY KEY(txid,sortition_id),
        FOREIGN KEY(sortition_id) REFERENCES snapshots(sortition_id)
    );"#,
    r#"
    CREATE TABLE stack_stx (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        reward_addr TEXT NOT NULL,
        stacked_ustx TEXT NOT NULL,
        num_cycles INTEGER NOT NULL,

        -- The primary key here is (txid, burn_header_hash) because
        -- this transaction will be accepted regardless of which sortition
        -- history it is in.
        PRIMARY KEY(txid,burn_header_hash)
    );"#,
    r#"
    CREATE TABLE transfer_stx (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        recipient_addr TEXT NOT NULL,
        transfered_ustx TEXT NOT NULL,
        memo TEXT NOT NULL,

        -- The primary key here is (txid, burn_header_hash) because
        -- this transaction will be accepted regardless of which sortition
        -- history it is in.
        PRIMARY KEY(txid,burn_header_hash)
    );"#,
    r#"
    CREATE TABLE missed_commits (
        txid TEXT NOT NULL,
        input TEXT NOT NULL,
        intended_sortition_id TEXT NOT NULL,

        PRIMARY KEY(txid, intended_sortition_id)
    );"#,
    "CREATE TABLE db_config(version TEXT PRIMARY KEY);",
];

const SORTITION_DB_SCHEMA_2: &[&str] = &[r#"
     CREATE TABLE epochs (
         start_block_height INTEGER NOT NULL,
         end_block_height INTEGER NOT NULL,
         epoch_id INTEGER NOT NULL,
         block_limit TEXT NOT NULL,
         network_epoch INTEGER NOT NULL,
         PRIMARY KEY(start_block_height,epoch_id)
     );"#];

const SORTITION_DB_SCHEMA_3: &[&str] = &[r#"
    CREATE TABLE block_commit_parents (
        block_commit_txid TEXT NOT NULL,
        block_commit_sortition_id TEXT NOT NULL,

        parent_sortition_id TEXT NOT NULL,

        PRIMARY KEY(block_commit_txid,block_commit_sortition_id),
        FOREIGN KEY(block_commit_txid,block_commit_sortition_id) REFERENCES block_commits(txid,sortition_id)
    );"#];

const SORTITION_DB_SCHEMA_4: &[&str] = &[
    r#"
    CREATE TABLE delegate_stx (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        delegate_to TEXT NOT NULL,
        reward_addr TEXT NOT NULL,
        delegated_ustx TEXT NOT NULL,
        until_burn_height INTEGER,

        PRIMARY KEY(txid,burn_header_hash)
    );"#,
    r#"
    CREATE TABLE ast_rule_heights (
        ast_rule_id INTEGER PRIMARY KEY NOT NULL,
        block_height INTEGER NOT NULL
    );"#,
];

/// The changes for version five *just* replace the existing epochs table
///  by deleting all the current entries and inserting the new epochs definition.
const SORTITION_DB_SCHEMA_5: &[&str] = &[r#"
     DELETE FROM epochs;"#];

const SORTITION_DB_SCHEMA_6: &[&str] = &[r#"
     DELETE FROM epochs;"#];

const SORTITION_DB_SCHEMA_7: &[&str] = &[r#"
     DELETE FROM epochs;"#];

const SORTITION_DB_SCHEMA_8: &[&str] = &[
    r#"DELETE FROM epochs;"#,
    r#"DROP INDEX IF EXISTS index_user_burn_support_txid;"#,
    r#"DROP INDEX IF EXISTS index_user_burn_support_sortition_id_vtxindex;"#,
    r#"DROP INDEX IF EXISTS index_user_burn_support_sortition_id_hash_160_key_vtxindex_key_block_ptr_vtxindex;"#,
    r#"DROP TABLE IF EXISTS user_burn_support;"#,
    r#"ALTER TABLE snapshots ADD miner_pk_hash TEXT DEFAULT NULL"#,
    r#"
    -- eagerly-processed reward sets, before they're applied to the start of the next reward cycle
    CREATE TABLE preprocessed_reward_sets (
        sortition_id TEXT PRIMARY KEY,
        reward_set TEXT NOT NULL
    );"#,
    r#"
    -- canonical chain tip at each sortition ID.
    -- This is updated in both 2.x and Nakamoto, but Nakamoto relies on this exclusively
    CREATE TABLE stacks_chain_tips (
        sortition_id TEXT PRIMARY KEY,
        consensus_hash TEXT NOT NULL,
        block_hash TEXT NOT NULL,
        block_height INTEGER NOT NULL
    );"#,
    r#"ALTER TABLE stack_stx ADD signer_key TEXT DEFAULT NULL;"#,
    r#"ALTER TABLE stack_stx ADD max_amount TEXT DEFAULT NULL;"#,
    r#"ALTER TABLE stack_stx ADD auth_id INTEGER DEFAULT NULL;"#,
    r#"
    -- table definition for `vote-for-aggregate-key` burn op
    CREATE TABLE vote_for_aggregate_key (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        aggregate_key TEXT NOT NULL,
        round INTEGER NOT NULL,
        reward_cycle INTEGER NOT NULL,
        signer_index INTEGER NOT NULL,
        signer_key TEXT NOT NULL,

        PRIMARY KEY(txid,burn_header_hash)
    );"#,
];

static SORTITION_DB_SCHEMA_9: &[&str] =
    &[r#"ALTER TABLE block_commits ADD punished TEXT DEFAULT NULL;"#];

const LAST_SORTITION_DB_INDEX: &str = "index_block_commits_by_sender";
const SORTITION_DB_INDEXES: &[&str] = &[
    "CREATE INDEX IF NOT EXISTS snapshots_block_hashes ON snapshots(block_height,index_root,winning_stacks_block_hash);",
    "CREATE INDEX IF NOT EXISTS snapshots_block_stacks_hashes ON snapshots(num_sortitions,index_root,winning_stacks_block_hash);",
    "CREATE INDEX IF NOT EXISTS snapshots_block_heights ON snapshots(burn_header_hash,block_height);",
    "CREATE INDEX IF NOT EXISTS snapshots_block_winning_hash ON snapshots(winning_stacks_block_hash);",
    "CREATE INDEX IF NOT EXISTS snapshots_canonical_chain_tip ON snapshots(pox_valid,block_height DESC,burn_header_hash ASC);",
    "CREATE INDEX IF NOT EXISTS block_arrivals ON snapshots(arrival_index,burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS arrival_indexes ON snapshots(arrival_index);",
    "CREATE INDEX IF NOT EXISTS index_leader_keys_sortition_id_block_height_vtxindex ON leader_keys(sortition_id,block_height,vtxindex);",
    "CREATE INDEX IF NOT EXISTS index_block_commits_sortition_id_vtxindex ON block_commits(sortition_id,vtxindex);",
    "CREATE INDEX IF NOT EXISTS index_block_commits_sortition_id_block_height_vtxindex ON block_commits(sortition_id,block_height,vtxindex);",
    "CREATE INDEX IF NOT EXISTS index_stack_stx_burn_header_hash ON stack_stx(burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_transfer_stx_burn_header_hash ON transfer_stx(burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_missed_commits_intended_sortition_id ON missed_commits(intended_sortition_id);",
    "CREATE INDEX IF NOT EXISTS index_parent_sortition_id ON block_commit_parents(parent_sortition_id);",
    "CREATE INDEX IF NOT EXISTS index_burn_header_hash ON snapshots(burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_parent_burn_header_hash ON snapshots(parent_burn_header_hash,burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_pox_payouts ON snapshots(pox_payouts);",
    "CREATE INDEX IF NOT EXISTS index_burn_header_hash_pox_valid ON snapshots(burn_header_hash,pox_valid);",
    "CREATE INDEX IF NOT EXISTS index_delegate_stx_burn_header_hash ON delegate_stx(burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_vote_for_aggregate_key_burn_header_hash ON vote_for_aggregate_key(burn_header_hash);",
    "CREATE INDEX IF NOT EXISTS index_block_commits_by_burn_height ON block_commits(block_height);",
    "CREATE INDEX IF NOT EXISTS index_block_commits_by_sender ON block_commits(apparent_sender);"
];

/// Handle to the sortition database, a MARF'ed sqlite DB on disk.
/// It stores information pertaining to cryptographic sortitions performed in each Bitcoin block --
/// either to select the next Stacks block (in epoch 2.5 and earlier), or to choose the next Stacks
/// miner (epoch 3.0 and later).
pub struct SortitionDB {
    /// Whether or not write operations are permitted.  Pertains to whether or not transaction
    /// objects can be created or schema migrations can happen on this SortitionDB instance.
    pub readwrite: bool,
    /// If true, then while write operations will be permitted, they will not be committed (and may
    /// even be skipped).  This is not used in production; it's used in the `stacks-inspect` tool
    /// to simulate what could happen (e.g. to replay sortitions with different anti-MEV strategies
    /// without corrupting the underlying DB).
    pub dryrun: bool,
    /// Handle to the MARF which stores an index over each burnchain and PoX fork.
    pub marf: MARF<SortitionId>,
    /// First burnchain block height at which sortitions will be considered.  All Stacks epochs
    /// besides epoch 1.0 must start at or after this height.
    pub first_block_height: u64,
    /// Hash of the first burnchain block at which sortitions will be considered.
    pub first_burn_header_hash: BurnchainHeaderHash,
    /// PoX constants that pertain to this DB, for purposes of (but not limited to) evaluating PoX
    /// reward cycles and evaluating block-commit validity within a PoX reward cycle
    pub pox_constants: PoxConstants,
    /// Path on disk from which this DB was opened (caller-given; not resolved).
    pub path: String,
}

#[derive(Clone)]
pub struct SortitionDBTxContext {
    pub first_block_height: u64,
    pub pox_constants: PoxConstants,
    pub dryrun: bool,
}

#[derive(Clone)]
pub struct SortitionHandleContext {
    pub first_block_height: u64,
    pub pox_constants: PoxConstants,
    pub chain_tip: SortitionId,
    pub dryrun: bool,
}

pub type SortitionDBConn<'a> = IndexDBConn<'a, SortitionDBTxContext, SortitionId>;
pub type SortitionDBTx<'a> = IndexDBTx<'a, SortitionDBTxContext, SortitionId>;

///
/// These structs are used to keep an open "handle" to the
///   sortition db -- this is just the db/marf connection
///   and a chain tip. This mostly just makes the job of callers
///   much simpler, because they don't have to worry about passing
///   around the open chain tip everywhere.
///
pub type SortitionHandleConn<'a> = IndexDBConn<'a, SortitionHandleContext, SortitionId>;
pub type SortitionHandleTx<'a> = IndexDBTx<'a, SortitionHandleContext, SortitionId>;

///
/// This trait is used for functions that
///  can accept either a SortitionHandleConn or a SortitionDBConn
///
pub trait SortitionContext: Clone {
    fn first_block_height(&self) -> u64;
}

impl SortitionContext for SortitionHandleContext {
    fn first_block_height(&self) -> u64 {
        self.first_block_height
    }
}

impl SortitionContext for SortitionDBTxContext {
    fn first_block_height(&self) -> u64 {
        self.first_block_height
    }
}

pub fn get_block_commit_by_txid(
    conn: &Connection,
    sort_id: &SortitionId,
    txid: &Txid,
) -> Result<Option<LeaderBlockCommitOp>, db_error> {
    let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND txid = ?2 LIMIT 1";
    let args = params![sort_id, txid];
    query_row(conn, qry, args)
}

pub fn get_ancestor_sort_id<C: SortitionContext>(
    ic: &IndexDBConn<'_, C, SortitionId>,
    block_height: u64,
    tip_block_hash: &SortitionId,
) -> Result<Option<SortitionId>, db_error> {
    let adjusted_height = match get_adjusted_block_height(&ic.context, block_height) {
        Some(x) => x,
        None => return Ok(None),
    };

    ic.get_ancestor_block_hash(adjusted_height, &tip_block_hash)
}

pub fn get_ancestor_sort_id_tx<C: SortitionContext>(
    ic: &mut IndexDBTx<'_, C, SortitionId>,
    block_height: u64,
    tip_block_hash: &SortitionId,
) -> Result<Option<SortitionId>, db_error> {
    let adjusted_height = match get_adjusted_block_height(&ic.context, block_height) {
        Some(x) => x,
        None => return Ok(None),
    };

    ic.get_ancestor_block_hash(adjusted_height, &tip_block_hash)
}

/// Returns the difference between `block_height` and `context.first_block_height()`, if this
/// is non-negative. Otherwise returns None.
fn get_adjusted_block_height<C: SortitionContext>(context: &C, block_height: u64) -> Option<u64> {
    let first_block_height = context.first_block_height();
    if block_height < first_block_height {
        return None;
    }

    Some(block_height - first_block_height)
}

struct db_keys;
impl db_keys {
    /// store an entry that maps from a PoX anchor's <stacks-block-header-hash> to <sortition-id of last block in prepare phase that chose it>
    pub fn pox_anchor_to_prepare_end(block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::pox_anchor_to_prepare_end::{}", block_hash)
    }

    pub fn pox_last_anchor() -> &'static str {
        "sortition_db::last_anchor_block"
    }

    pub fn pox_last_anchor_txid() -> &'static str {
        "sortition_db::last_anchor_block_txid"
    }

    pub fn pox_last_selected_anchor() -> &'static str {
        "sortition_db::last_selected_anchor_block"
    }

    pub fn pox_last_selected_anchor_txid() -> &'static str {
        "sortition_db::last_selected_anchor_block_txid"
    }

    pub fn pox_affirmation_map() -> &'static str {
        "sortition_db::affirmation_map"
    }

    pub fn pox_reward_cycle_unlocks(cycle: u64) -> String {
        format!("sortition_db::reward_set_unlocks::{}", cycle)
    }

    pub fn pox_reward_set_size() -> &'static str {
        "sortition_db::reward_set::size"
    }

    pub fn pox_reward_set_entry(ix: u16) -> String {
        format!("sortition_db::reward_set::entry::{}", ix)
    }

    pub fn pox_reward_set_payouts_key() -> String {
        format!("sortition_db::reward_set::payouts")
    }

    pub fn pox_reward_set_payouts_value(addrs: Vec<PoxAddress>, payout_per_addr: u128) -> String {
        serde_json::to_string(&(addrs, payout_per_addr)).unwrap()
    }

    pub fn pox_reward_set_payouts_decode(addr_str: &str) -> (Vec<PoxAddress>, u128) {
        let addrs_and_payout: (Vec<PoxAddress>, u128) = serde_json::from_str(addr_str).unwrap();
        addrs_and_payout
    }

    /// store an entry for retrieving the PoX identifier (i.e., the PoX bitvector) for this PoX fork
    pub fn pox_identifier() -> &'static str {
        "sortition_db::pox_identifier"
    }

    pub fn initial_mining_bonus_remaining() -> &'static str {
        "sortition_db::initial_mining::remaining"
    }

    pub fn initial_mining_bonus_per_block() -> &'static str {
        "sortition_db::initial_mining::per_block"
    }

    pub fn sortition_id_for_bhh(bhh: &BurnchainHeaderHash) -> String {
        format!("sortition_db::sortition_id_for_bhh::{}", bhh)
    }
    pub fn vrf_key_status(key: &VRFPublicKey) -> String {
        format!("sortition_db::vrf::{}", key.to_hex())
    }
    pub fn stacks_block_present(block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::sortition_block_hash::{}", block_hash)
    }
    pub fn last_sortition() -> &'static str {
        "sortition_db::last_sortition"
    }

    /// MARF index key for a processed stacks block.  Maps to its height.
    pub fn stacks_block_index(stacks_block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::stacks::block::{}", stacks_block_hash)
    }

    /// MARF index value for a processed stacks block
    fn stacks_block_index_value(height: u64) -> String {
        format!("{}", height)
    }

    /// MARF index key for the highest arrival index processed in a fork
    pub fn stacks_block_max_arrival_index() -> String {
        "sortition_db::stacks::block::max_arrival_index".to_string()
    }

    /// MARF index value for the highest arrival index processed in a fork
    fn stacks_block_max_arrival_index_value(index: u64) -> String {
        format!("{}", index)
    }

    pub fn reward_set_size_to_string(size: usize) -> String {
        to_hex(
            &u16::try_from(size)
                .expect("BUG: maximum reward set size should be u16")
                .to_le_bytes(),
        )
    }

    pub fn reward_set_size_from_string(size: &str) -> u16 {
        let bytes = hex_bytes(size).expect("CORRUPTION: bad format written for reward set size");
        let mut byte_buff = [0; 2];
        byte_buff.copy_from_slice(&bytes[0..2]);
        u16::from_le_bytes(byte_buff)
    }

    /// reward cycle ID that was last processed
    /// NOTE: unused now, but was used in earlier consensus rules.
    /// Preserved for testing compatibility.
    pub fn last_reward_cycle_key() -> &'static str {
        "sortition_db::last_reward_cycle"
    }

    /// NOTE: unused now, but was used in earlier consensus rules.
    /// Preserved for testing compatibility.
    pub fn last_reward_cycle_to_string(rc: u64) -> String {
        to_hex(&rc.to_le_bytes())
    }

    /// NOTE: unused now, but was used in earlier consensus rules.
    /// Preserved for testing compatibility.
    pub fn last_reward_cycle_from_string(rc_str: &str) -> u64 {
        let bytes = hex_bytes(rc_str).expect("CORRUPTION: bad format written for reward cycle ID");
        assert_eq!(
            bytes.len(),
            8,
            "CORRUPTION: expected 8 bytes for reward cycle"
        );
        let mut rc_buff = [0; 8];
        rc_buff.copy_from_slice(&bytes[0..8]);
        u64::from_le_bytes(rc_buff)
    }
}

/// Trait for structs that provide a chaintip-indexed handle into the
///  SortitionDB (i.e., a MARF view from a particular SortitionId)
pub trait SortitionHandle {
    /// Returns a connection to the SQLite db. If this handle is wrapping
    ///  a transaction, this should point to the open transaction.
    fn sqlite(&self) -> &Connection;

    /// Returns the snapshot of the burnchain block at burnchain height `block_height`.
    /// Returns None if there is no block at this height.
    fn get_block_snapshot_by_height(
        &mut self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error>;

    /// Get the first burn block height
    fn first_burn_block_height(&self) -> u64;

    /// Get a ref to the PoX constants
    fn pox_constants(&self) -> &PoxConstants;

    /// Get the sortition ID of the sortition history tip this handle represents
    fn tip(&self) -> SortitionId;

    /// Get the highest-processed Nakamoto block on this sortition history.
    /// Returns Ok(Some(nakamoto-tip-ch, nakamoto-tip-bhh, nakamoto-tip-height))) on success, if
    /// there was a tip found
    /// Returns Ok(None) if no Nakamoto blocks are present on this sortition history
    /// Returns Err(..) on DB errors
    fn get_nakamoto_tip(&self) -> Result<Option<(ConsensusHash, BlockHeaderHash, u64)>, db_error>;

    /// Get the block ID of the highest-processed Nakamoto block on this history.
    fn get_nakamoto_tip_block_id(&self) -> Result<Option<StacksBlockId>, db_error> {
        let Some((ch, bhh, _)) = self.get_nakamoto_tip()? else {
            return Ok(None);
        };
        Ok(Some(StacksBlockId::new(&ch, &bhh)))
    }

    /// is the given block a descendant of `potential_ancestor`?
    ///  * block_at_burn_height: the burn height of the sortition that chose the stacks block to check
    ///  * potential_ancestor: the stacks block hash of the potential ancestor
    fn descended_from(
        &mut self,
        block_at_burn_height: u64,
        potential_ancestor: &BlockHeaderHash,
    ) -> Result<bool, db_error> {
        let earliest_block_height_opt = self.sqlite().query_row(
            "SELECT block_height FROM snapshots WHERE winning_stacks_block_hash = ? ORDER BY block_height ASC LIMIT 1",
            &[potential_ancestor],
            |row| Ok(u64::from_row(row).expect("Expected u64 in database")))
            .optional()?;

        let earliest_block_height = match earliest_block_height_opt {
            Some(h) => h,
            None => {
                return Ok(false);
            }
        };

        let mut sn = self
            .get_block_snapshot_by_height(block_at_burn_height)?
            .ok_or_else(|| {
                test_debug!("No snapshot at height {}", block_at_burn_height);
                db_error::NotFoundError
            })?;

        while sn.block_height >= earliest_block_height {
            if !sn.sortition {
                return Ok(false);
            }
            if &sn.winning_stacks_block_hash == potential_ancestor {
                return Ok(true);
            }

            // step back to the parent
            match SortitionDB::get_block_commit_parent_sortition_id(
                self.sqlite(),
                &sn.winning_block_txid,
                &sn.sortition_id,
            )? {
                Some(parent_sortition_id) => {
                    // we have the block_commit parent memoization data
                    test_debug!(
                        "Parent sortition of {} memoized as {}",
                        &sn.winning_block_txid,
                        &parent_sortition_id
                    );
                    sn = SortitionDB::get_block_snapshot(self.sqlite(), &parent_sortition_id)?
                        .ok_or_else(|| db_error::NotFoundError)?;
                }
                None => {
                    // we do not have the block_commit parent memoization data
                    // step back to the parent
                    test_debug!("No parent sortition memo for {}", &sn.winning_block_txid);
                    let block_commit = get_block_commit_by_txid(
                        &self.sqlite(),
                        &sn.sortition_id,
                        &sn.winning_block_txid,
                    )?
                    .expect("CORRUPTION: winning block commit for snapshot not found");
                    sn = self
                        .get_block_snapshot_by_height(block_commit.parent_block_ptr as u64)?
                        .ok_or_else(|| db_error::NotFoundError)?;
                }
            }
        }
        return Ok(false);
    }
}

impl<'a> SortitionHandleTx<'a> {
    /// begin a MARF transaction with this connection
    ///  this is used by _writing_ contexts
    pub fn begin(
        conn: &'a mut SortitionDB,
        parent_chain_tip: &SortitionId,
    ) -> Result<SortitionHandleTx<'a>, db_error> {
        if !conn.readwrite {
            return Err(db_error::ReadOnly);
        }

        let handle = SortitionHandleTx::new(
            &mut conn.marf,
            SortitionHandleContext {
                chain_tip: parent_chain_tip.clone(),
                first_block_height: conn.first_block_height,
                pox_constants: conn.pox_constants.clone(),
                dryrun: conn.dryrun,
            },
        );

        Ok(handle)
    }

    /// Uses the handle's current fork identifier to get a block snapshot by
    ///   burnchain block header
    /// If the burn header hash is _not_ in the current fork, then this will return Ok(None)
    pub fn get_block_snapshot(
        &mut self,
        burn_header_hash: &BurnchainHeaderHash,
        chain_tip: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let sortition_identifier_key = db_keys::sortition_id_for_bhh(burn_header_hash);
        let sortition_id = match self.get_indexed(&chain_tip, &sortition_identifier_key)? {
            None => return Ok(None),
            Some(x) => SortitionId::from_hex(&x).expect("FATAL: bad Sortition ID stored in DB"),
        };

        SortitionDB::get_block_snapshot(self.tx(), &sortition_id)
    }

    /// Get a leader key at a specific location in the burn chain's fork history, given the
    /// matching block commit's fork index root (block_height and vtxindex are the leader's
    /// calculated location in this fork).
    /// Returns None if there is no leader key at this location.
    pub fn get_leader_key_at(
        &mut self,
        key_block_height: u64,
        key_vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        assert!(key_block_height < BLOCK_HEIGHT_MAX);
        let ancestor_snapshot =
            match SortitionDB::get_ancestor_snapshot_tx(self, key_block_height, tip)? {
                Some(sn) => sn,
                None => {
                    return Ok(None);
                }
            };

        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args = params![
            ancestor_snapshot.sortition_id,
            u64_to_sql(key_block_height)?,
            key_vtxindex,
        ];
        query_row_panic(self.tx(), qry, args, || {
            format!(
                "Multiple keys at {},{} in {}",
                key_block_height, key_vtxindex, tip
            )
        })
    }

    /// Find the VRF public keys consumed by each block candidate in the given list.
    /// The burn DB should have a key for each candidate; otherwise the candidate would not have
    /// been accepted.
    pub fn get_consumed_leader_keys(
        &mut self,
        parent_tip: &BlockSnapshot,
        block_candidates: &[LeaderBlockCommitOp],
    ) -> Result<Vec<LeaderKeyRegisterOp>, db_error> {
        // get the set of VRF keys consumed by these commits
        let mut leader_keys = vec![];
        for i in 0..block_candidates.len() {
            let leader_key_block_height = block_candidates[i].key_block_ptr as u64;
            let leader_key_vtxindex = block_candidates[i].key_vtxindex as u32;
            let leader_key = self
                .get_leader_key_at(
                    leader_key_block_height,
                    leader_key_vtxindex,
                    &parent_tip.sortition_id,
                )?
                .unwrap_or_else(|| {
                    panic!(
                        "FATAL: no leader key for accepted block commit {} (at {},{})",
                        &block_candidates[i].txid, leader_key_block_height, leader_key_vtxindex
                    )
                });

            leader_keys.push(leader_key);
        }

        Ok(leader_keys)
    }

    /// Get a block commit by its content-addressed location in a specific sortition.
    pub fn get_block_commit(
        &self,
        txid: &Txid,
        sortition_id: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        SortitionDB::get_block_commit(self.tx(), txid, sortition_id)
    }

    pub fn get_consensus_at(
        &mut self,
        block_height: u64,
    ) -> Result<Option<ConsensusHash>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();

        match SortitionDB::get_ancestor_snapshot_tx(self, block_height, &chain_tip)? {
            Some(sn) => Ok(Some(sn.consensus_hash)),
            None => Ok(None),
        }
    }

    /// Do we expect a stacks block in this particular fork?
    /// i.e. is this block hash part of the fork history identified by tip_block_hash?
    pub fn expects_stacks_block_in_fork(
        &mut self,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        self.get_indexed(&chain_tip, &db_keys::stacks_block_present(block_hash))
            .map(|result| result.is_some())
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    /// Search snapshots up to (but excluding) the given block height.
    /// Will always return a snapshot -- even if it's the initial sentinel snapshot.
    pub fn get_last_snapshot_with_sortition(
        &mut self,
        burn_block_height: u64,
    ) -> Result<BlockSnapshot, db_error> {
        assert!(burn_block_height < BLOCK_HEIGHT_MAX);
        test_debug!(
            "Get snapshot at from sortition tip {}, expect height {}",
            &self.context.chain_tip,
            burn_block_height
        );
        let chain_tip = self.context.chain_tip.clone();

        let get_from = match get_ancestor_sort_id_tx(self, burn_block_height, &chain_tip)? {
            Some(sortition_id) => sortition_id,
            None => {
                error!(
                    "No blockheight {} ancestor at sortition identifier {}",
                    burn_block_height, &self.context.chain_tip
                );
                return Err(db_error::NotFoundError);
            }
        };

        let ancestor_hash = match self.get_indexed(&get_from, &db_keys::last_sortition())? {
            Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).unwrap_or_else(|_| {
                panic!(
                    "FATAL: corrupt database: failed to parse {} into a hex string",
                    &hex_str
                )
            }),
            None => {
                // no prior sortitions, so get the first
                return SortitionDB::get_first_block_snapshot(self.tx());
            }
        };

        self.get_block_snapshot(&ancestor_hash, &chain_tip)
            .map(|snapshot_opt| {
                snapshot_opt.unwrap_or_else(|| {
                    panic!("FATAL: corrupt index: no snapshot {}", ancestor_hash)
                })
            })
    }

    /// Determine whether or not a leader key has been consumed by a subsequent block commitment in
    /// this fork's history.
    /// Will return false if the leader key does not exist.
    pub fn is_leader_key_consumed(
        &mut self,
        leader_key: &LeaderKeyRegisterOp,
    ) -> Result<bool, db_error> {
        assert!(leader_key.block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();

        let key_status =
            match self.get_indexed(&chain_tip, &db_keys::vrf_key_status(&leader_key.public_key))? {
                Some(status_str) => {
                    if status_str == "1" {
                        // key is still available
                        false
                    } else if status_str == "0" {
                        // key is consumed
                        true
                    } else {
                        panic!("Invalid key status string {}", status_str);
                    }
                }
                None => {
                    // never before seen
                    false
                }
            };

        Ok(key_status)
    }

    /// Get a parent block commit at a specific location in the burn chain on a particular fork.
    /// Returns None if there is no block commit at this location.
    pub fn get_block_commit_parent(
        &mut self,
        block_height: u64,
        vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let ancestor_id = match get_ancestor_sort_id_tx(self, block_height, tip)? {
            Some(id) => id,
            None => {
                return Ok(None);
            }
        };

        SortitionDB::get_block_commit_of_sortition(self.tx(), &ancestor_id, block_height, vtxindex)
    }

    pub fn has_VRF_public_key(&mut self, key: &VRFPublicKey) -> Result<bool, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let key_status = self
            .get_indexed(&chain_tip, &db_keys::vrf_key_status(key))?
            .is_some();
        Ok(key_status)
    }

    fn check_fresh_consensus_hash<F>(
        &mut self,
        consensus_hash_lifetime: u64,
        check: F,
    ) -> Result<bool, db_error>
    where
        F: Fn(&ConsensusHash) -> bool,
    {
        let chain_tip = self.context.chain_tip.clone();
        let first_snapshot = SortitionDB::get_first_block_snapshot(self.tx())?;
        let mut last_snapshot =
            SortitionDB::get_block_snapshot(self.tx(), &self.context.chain_tip)?
                .ok_or_else(|| db_error::NotFoundError)?;
        let current_block_height = last_snapshot.block_height;

        let mut oldest_height = if current_block_height < consensus_hash_lifetime {
            0
        } else {
            current_block_height - consensus_hash_lifetime
        };

        if oldest_height < first_snapshot.block_height {
            oldest_height = first_snapshot.block_height;
        }

        if check(&last_snapshot.consensus_hash) {
            return Ok(true);
        }

        for _i in oldest_height..current_block_height {
            let ancestor_snapshot = self
                .get_block_snapshot(&last_snapshot.parent_burn_header_hash, &chain_tip)?
                .unwrap_or_else(|| {
                    panic!(
                        "Discontiguous index: missing block {}",
                        last_snapshot.parent_burn_header_hash
                    )
                });
            if check(&ancestor_snapshot.consensus_hash) {
                return Ok(true);
            }
            last_snapshot = ancestor_snapshot;
        }

        return Ok(false);
    }

    /// Find out whether or not a given consensus hash is "recent" enough to be used in this fork.
    pub fn is_fresh_consensus_hash(
        &mut self,
        consensus_hash_lifetime: u64,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, db_error> {
        self.check_fresh_consensus_hash(consensus_hash_lifetime, |fresh_hash| {
            fresh_hash == consensus_hash
        })
    }

    /// Find out whether or not a given consensus hash is "recent" enough to be used in this fork.
    /// This function only checks the first 19 bytes
    pub fn is_fresh_consensus_hash_check_19b(
        &mut self,
        consensus_hash_lifetime: u64,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, db_error> {
        self.check_fresh_consensus_hash(consensus_hash_lifetime, |fresh_hash| {
            fresh_hash.as_bytes()[0..19] == consensus_hash.as_bytes()[0..19]
        })
    }
}

impl SortitionHandle for SortitionHandleTx<'_> {
    fn get_block_snapshot_by_height(
        &mut self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();
        SortitionDB::get_ancestor_snapshot_tx(self, block_height, &chain_tip)
    }

    fn first_burn_block_height(&self) -> u64 {
        self.context.first_block_height
    }

    fn pox_constants(&self) -> &PoxConstants {
        &self.context.pox_constants
    }

    fn sqlite(&self) -> &Connection {
        self.tx()
    }

    fn tip(&self) -> SortitionId {
        self.context.chain_tip.clone()
    }

    fn get_nakamoto_tip(&self) -> Result<Option<(ConsensusHash, BlockHeaderHash, u64)>, db_error> {
        let sn = SortitionDB::get_block_snapshot(self.sqlite(), &self.context.chain_tip)?
            .ok_or(db_error::NotFoundError)?;
        SortitionDB::get_canonical_nakamoto_tip_hash_and_height(self.sqlite(), &sn)
    }
}

impl SortitionHandle for SortitionHandleConn<'_> {
    fn get_block_snapshot_by_height(
        &mut self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        SortitionHandleConn::get_block_snapshot_by_height(self, block_height)
    }

    fn first_burn_block_height(&self) -> u64 {
        self.context.first_block_height
    }

    fn pox_constants(&self) -> &PoxConstants {
        &self.context.pox_constants
    }

    fn sqlite(&self) -> &Connection {
        self.conn()
    }

    fn tip(&self) -> SortitionId {
        self.context.chain_tip.clone()
    }

    fn get_nakamoto_tip(&self) -> Result<Option<(ConsensusHash, BlockHeaderHash, u64)>, db_error> {
        let sn = SortitionDB::get_block_snapshot(self.sqlite(), &self.context.chain_tip)?
            .ok_or(db_error::NotFoundError)?;
        SortitionDB::get_canonical_nakamoto_tip_hash_and_height(self.sqlite(), &sn)
    }
}

impl SortitionHandleTx<'_> {
    pub fn set_stacks_block_accepted(
        &mut self,
        consensus_hash: &ConsensusHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        let chain_tip = SortitionDB::get_block_snapshot(self, &self.context.chain_tip)?.expect(
            "FAIL: Setting stacks block accepted in canonical chain tip which cannot be found",
        );

        // record new arrival
        self.set_stacks_block_accepted_at_tip(
            &chain_tip,
            consensus_hash,
            stacks_block_hash,
            stacks_block_height,
        )?;

        if cfg!(test) {
            let (ch, bhh) = SortitionDB::get_canonical_stacks_chain_tip_hash(self).unwrap();
            debug!(
                "Memoized canonical Stacks chain tip is now {}/{}, written to {}",
                &ch, &bhh, &self.context.chain_tip
            );
        }

        Ok(())
    }

    /// Get the expected PoX recipients (reward set) for the next sortition, either by querying information
    ///  from the current reward cycle, or if `next_pox_info` is provided, by querying information
    ///  for the next reward cycle.
    ///
    /// Returns None if:
    ///   * The reward cycle had an anchor block, but it isn't known by this node.
    ///   * The reward cycle did not have anchor block
    ///   * The block is in the prepare phase of a reward cycle, in which case miners must burn
    ///   * The Stacking recipient set is empty (either because this reward cycle has already exhausted the set of addresses or because no one ever Stacked).
    fn pick_recipients(
        &mut self,
        burnchain: &Burnchain,
        block_height: u64,
        reward_set_vrf_seed: &SortitionHash,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<RewardSetInfo>, BurnchainError> {
        let allow_nakamoto_punishment = SortitionDB::get_stacks_epoch(self.sqlite(), block_height)?
            .ok_or_else(|| BurnchainError::NoStacksEpoch)?
            .epoch_id
            .allows_pox_punishment();

        if let Some(next_pox_info) = next_pox_info {
            if let PoxAnchorBlockStatus::SelectedAndKnown(
                ref anchor_block,
                ref _txid,
                ref reward_set,
            ) = next_pox_info.anchor_status
            {
                if burnchain.is_in_prepare_phase(block_height) {
                    debug!(
                        "No recipients for block {}, since in prepare phase",
                        block_height
                    );
                    return Ok(None);
                }

                test_debug!(
                    "Pick recipients for anchor block {} -- {} reward recipient(s)",
                    anchor_block,
                    reward_set.rewarded_addresses.len()
                );
                if reward_set.rewarded_addresses.is_empty() {
                    return Ok(None);
                }

                if OUTPUTS_PER_COMMIT != 2 {
                    unreachable!("BUG: PoX reward address selection only implemented for OUTPUTS_PER_COMMIT = 2");
                }

                let chosen_recipients = reward_set_vrf_seed.choose_two(
                    reward_set
                        .rewarded_addresses
                        .len()
                        .try_into()
                        .expect("BUG: u32 overflow in PoX outputs per commit"),
                );

                Ok(Some(RewardSetInfo {
                    anchor_block: anchor_block.clone(),
                    recipients: chosen_recipients
                        .into_iter()
                        .map(|ix| {
                            let recipient = reward_set.rewarded_addresses[ix as usize].clone();
                            info!("PoX recipient chosen";
                               "recipient" => recipient.to_burnchain_repr(),
                               "block_height" => block_height,
                               "anchor_stacks_block_hash" => &anchor_block,
                            );
                            (recipient, u16::try_from(ix).unwrap())
                        })
                        .collect(),
                    allow_nakamoto_punishment,
                }))
            } else {
                test_debug!(
                    "No anchor block known for this reward cycle (starting at {})",
                    block_height
                );
                Ok(None)
            }
        } else {
            let last_anchor = self.get_last_anchor_block_hash()?;
            if let Some(anchor_block) = last_anchor {
                // known
                // get the reward set size
                let reward_set_size = self.get_reward_set_size()?;
                if reward_set_size == 0 {
                    test_debug!(
                        "No more reward recipients descending from anchor block {}",
                        anchor_block
                    );
                    Ok(None)
                } else {
                    let chosen_recipients = reward_set_vrf_seed.choose_two(reward_set_size as u32);
                    let mut recipients = vec![];
                    for ix in chosen_recipients.into_iter() {
                        let ix = u16::try_from(ix).unwrap();
                        let recipient = self.get_reward_set_entry(ix)?;
                        info!("PoX recipient chosen";
                           "recipient" => recipient.to_burnchain_repr(),
                           "block_height" => block_height,
                           "stacks_block_hash" => %anchor_block
                        );
                        recipients.push((recipient, ix));
                    }
                    Ok(Some(RewardSetInfo {
                        anchor_block,
                        recipients,
                        allow_nakamoto_punishment,
                    }))
                }
            } else {
                // no anchor block selected
                test_debug!("No anchor block selected for this reward cycle");
                Ok(None)
            }
        }
    }

    pub fn get_reward_set_payouts_at(
        &self,
        sortition_id: &SortitionId,
    ) -> Result<(Vec<PoxAddress>, u128), db_error> {
        let sql = "SELECT pox_payouts FROM snapshots WHERE sortition_id = ?1";
        let args = params![sortition_id];
        let pox_addrs_json: String = query_row(self, sql, args)?.ok_or(db_error::NotFoundError)?;

        let pox_addrs: (Vec<PoxAddress>, u128) =
            serde_json::from_str(&pox_addrs_json).expect("FATAL: failed to decode pox payout JSON");
        Ok(pox_addrs)
    }

    pub fn get_reward_set_size_at(&mut self, sortition_id: &SortitionId) -> Result<u16, db_error> {
        self.get_indexed(sortition_id, &db_keys::pox_reward_set_size())
            .map(|x| {
                db_keys::reward_set_size_from_string(
                    &x.expect("CORRUPTION: no current reward set size written"),
                )
            })
    }

    pub fn get_reward_set_entry_at(
        &mut self,
        sortition_id: &SortitionId,
        entry_ix: u16,
    ) -> Result<PoxAddress, db_error> {
        let entry_str = self
            .get_indexed(sortition_id, &db_keys::pox_reward_set_entry(entry_ix))?
            .unwrap_or_else(|| {
                panic!(
                    "CORRUPTION: expected reward set entry at index={}, but not found",
                    entry_ix
                )
            });
        Ok(PoxAddress::from_db_string(&entry_str).expect("FATAL: could not decode PoX address"))
    }

    fn get_reward_set_entry(&mut self, entry_ix: u16) -> Result<PoxAddress, db_error> {
        self.get_reward_set_entry_at(&self.context.chain_tip.clone(), entry_ix)
    }

    fn get_reward_set_size(&mut self) -> Result<u16, db_error> {
        self.get_reward_set_size_at(&self.context.chain_tip.clone())
    }

    pub fn get_last_anchor_block_hash(&mut self) -> Result<Option<BlockHeaderHash>, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(
            self.get_indexed(&chain_tip, &db_keys::pox_last_anchor())?,
        );
        Ok(anchor_block_hash)
    }

    pub fn get_last_anchor_block_txid(&mut self) -> Result<Option<Txid>, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let anchor_block_txid = SortitionDB::parse_last_anchor_block_txid(
            self.get_indexed(&chain_tip, &db_keys::pox_last_anchor_txid())?,
        );
        Ok(anchor_block_txid)
    }

    pub fn get_sortition_affirmation_map(&mut self) -> Result<AffirmationMap, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let affirmation_map = match self.get_indexed(&chain_tip, &db_keys::pox_affirmation_map())? {
            Some(am_str) => {
                AffirmationMap::decode(&am_str).expect("FATAL: corrupt affirmation map")
            }
            None => AffirmationMap::empty(),
        };
        Ok(affirmation_map)
    }

    pub fn get_last_selected_anchor_block_hash(
        &mut self,
    ) -> Result<Option<BlockHeaderHash>, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(
            self.get_indexed(&chain_tip, &db_keys::pox_last_selected_anchor())?,
        );
        Ok(anchor_block_hash)
    }

    pub fn get_last_selected_anchor_block_txid(&mut self) -> Result<Option<Txid>, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let anchor_block_txid = SortitionDB::parse_last_anchor_block_txid(
            self.get_indexed(&chain_tip, &db_keys::pox_last_selected_anchor_txid())?,
        );
        Ok(anchor_block_txid)
    }

    /// Update the canonical Stacks tip
    fn update_canonical_stacks_tip(
        &mut self,
        sort_id: &SortitionId,
        consensus_hash: &ConsensusHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        let sql = "INSERT OR REPLACE INTO stacks_chain_tips (sortition_id,consensus_hash,block_hash,block_height) VALUES (?1,?2,?3,?4)";
        let args = params![
            sort_id,
            consensus_hash,
            stacks_block_hash,
            u64_to_sql(stacks_block_height)?,
        ];
        self.execute(sql, args)?;
        Ok(())
    }

    /// Mark an existing snapshot's stacks block as accepted at a particular burn chain tip within a PoX fork (identified by the consensus hash),
    /// and calculate and store its arrival index.
    /// If this Stacks block extends the canonical stacks chain tip, then also update the memoized canonical
    /// stacks chain tip metadata on the burn chain tip.
    // TODO: this method's inner call to get_indexed() can occur within a MARF transaction, which
    // means it will clone() the underlying TrieRAM.  Until this is rectified, care should be taken
    // to ensure that no keys are inserted until after this method is called.  This should already
    // be the case, since the only time keys are inserted into the sortition DB MARF is when the
    // next snapshot is processed (whereas this method is called when a Stacks epoch is processed).
    fn set_stacks_block_accepted_at_tip(
        &mut self,
        burn_tip: &BlockSnapshot,
        consensus_hash: &ConsensusHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        let block_sn = SortitionDB::get_block_snapshot_consensus(self, consensus_hash)?
            .ok_or(db_error::NotFoundError)?;

        let cur_epoch =
            SortitionDB::get_stacks_epoch(self, block_sn.block_height)?.unwrap_or_else(|| {
                panic!(
                    "FATAL: no epoch defined for burn height {}",
                    block_sn.block_height
                )
            });

        if cur_epoch.epoch_id >= StacksEpochId::Epoch30 {
            // Nakamoto blocks are always processed in order since the chain can't fork
            // arbitrarily.
            //
            // However, a "benign" fork can arise when a late tenure-change is processed.  This
            // would happen if
            //
            // 1. miner A wins sortition and produces a tenure-change;
            // 2. miner B wins sortition, and signers sign its tenure-change;
            // 3. miner C wins sortition by confirming miner A's last-block
            //
            // Depending on the timing of things, signers could end up signing both miner B and
            // miner C's tenure-change blocks, which are in conflict.  The Stacks node must be able
            // to handle this case; it does so simply by processing both blocks (as Stacks forks),
            // and letting signers figure out which one is canonical.
            //
            // As a result, only update the canonical Nakamoto tip if the given block is higher
            // than the existing tip for this sortiton (because it represents more overall signer
            // votes).
            let current_sortition_tip : Option<(ConsensusHash, BlockHeaderHash, u64)> = self.query_row_and_then(
                "SELECT consensus_hash,block_hash,block_height FROM stacks_chain_tips WHERE sortition_id = ?1 ORDER BY block_height DESC LIMIT 1",
                rusqlite::params![&burn_tip.sortition_id],
                |row| Ok((row.get_unwrap(0), row.get_unwrap(1), (u64::try_from(row.get_unwrap::<_, i64>(2)).expect("FATAL: block height too high"))))
            ).optional()?;

            if let Some((cur_ch, cur_bhh, cur_height)) = current_sortition_tip {
                let will_replace = if cur_height < stacks_block_height {
                    true
                } else if cur_height > stacks_block_height {
                    false
                } else if &cur_ch == consensus_hash {
                    // same sortition (i.e. nakamoto block)
                    // no replacement
                    false
                } else {
                    // tips come from different sortitions
                    // break ties by going with the latter-signed block
                    let sn_current = SortitionDB::get_block_snapshot_consensus(self, &cur_ch)?
                        .ok_or(db_error::NotFoundError)?;
                    let sn_accepted =
                        SortitionDB::get_block_snapshot_consensus(self, &consensus_hash)?
                            .ok_or(db_error::NotFoundError)?;
                    sn_current.block_height < sn_accepted.block_height
                };

                debug!("Setting Stacks tip as accepted";
                       "replace?" => will_replace,
                       "current_tip_consensus_hash" => %cur_ch,
                       "current_tip_block_header_hash" => %cur_bhh,
                       "current_tip_block_id" => %StacksBlockId::new(&cur_ch, &cur_bhh),
                       "current_tip_height" => cur_height,
                       "accepted_tip_consensus_hash" => %consensus_hash,
                       "accepted_tip_block_header_hash" => %stacks_block_hash,
                       "accepted_tip_block_id" => %StacksBlockId::new(consensus_hash, stacks_block_hash),
                       "accepted_tip_height" => stacks_block_height);

                if !will_replace {
                    return Ok(());
                }
            }

            self.update_canonical_stacks_tip(
                &burn_tip.sortition_id,
                consensus_hash,
                stacks_block_hash,
                stacks_block_height,
            )?;
            return Ok(());
        }

        // in epoch 2.x, where we track canonical stacks tip via the sortition DB
        let arrival_index = SortitionDB::get_max_arrival_index(self)?;
        let args = params![
            u64_to_sql(stacks_block_height)?,
            u64_to_sql(arrival_index + 1)?,
            consensus_hash,
            stacks_block_hash,
        ];

        debug!(
            "Set Stacks block {}/{} ({}) as arrival #{} on tip {} ({},{})",
            consensus_hash,
            stacks_block_hash,
            stacks_block_height,
            arrival_index + 1,
            &burn_tip.burn_header_hash,
            &burn_tip.consensus_hash,
            burn_tip.block_height
        );

        // NOTE: in Nakamoto, this may return zero rows since blocks are no longer coupled to
        // snapshots.  However, it will update at least one row if the block is a tenure-start
        // block.
        self.execute("UPDATE snapshots SET stacks_block_accepted = 1, stacks_block_height = ?1, arrival_index = ?2 WHERE consensus_hash = ?3 AND winning_stacks_block_hash = ?4", args)?;

        // update arrival data across all Stacks forks
        let (best_ch, best_bhh, best_height) = self.find_new_block_arrivals(burn_tip)?;
        self.update_canonical_stacks_tip(&burn_tip.sortition_id, &best_ch, &best_bhh, best_height)?;
        self.update_new_block_arrivals(burn_tip, best_ch, best_bhh, best_height)?;

        Ok(())
    }
}

impl<'a> SortitionHandleConn<'a> {
    /// open a reader handle from a consensus hash
    pub fn open_reader_consensus(
        connection: &'a SortitionDBConn<'a>,
        chain_tip: &ConsensusHash,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        let sn = match SortitionDB::get_block_snapshot_consensus(&connection.conn(), chain_tip)? {
            Some(sn) => {
                if !sn.pox_valid {
                    warn!(
                        "No such chain tip consensus hash {}: not on a valid PoX fork",
                        chain_tip
                    );
                    return Err(db_error::InvalidPoxSortition);
                }
                sn
            }
            None => {
                test_debug!("No such chain tip consensus hash {}", chain_tip);
                return Err(db_error::NotFoundError);
            }
        };

        SortitionHandleConn::open_reader(connection, &sn.sortition_id)
    }

    pub fn get_reward_set_size_at(&self, sortition_id: &SortitionId) -> Result<u16, db_error> {
        self.get_indexed(sortition_id, &db_keys::pox_reward_set_size())
            .map(|x| {
                db_keys::reward_set_size_from_string(
                    &x.expect("CORRUPTION: no current reward set size written"),
                )
            })
    }

    pub fn get_last_anchor_block_hash(&self) -> Result<Option<BlockHeaderHash>, db_error> {
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(
            self.get_indexed(&self.context.chain_tip, &db_keys::pox_last_anchor())?,
        );
        Ok(anchor_block_hash)
    }

    pub fn get_last_anchor_block_txid(&self) -> Result<Option<Txid>, db_error> {
        let anchor_block_txid = SortitionDB::parse_last_anchor_block_txid(
            self.get_indexed(&self.context.chain_tip, &db_keys::pox_last_anchor_txid())?,
        );
        Ok(anchor_block_txid)
    }

    pub fn get_sortition_affirmation_map(&self) -> Result<AffirmationMap, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let affirmation_map = match self.get_indexed(&chain_tip, &db_keys::pox_affirmation_map())? {
            Some(am_str) => {
                AffirmationMap::decode(&am_str).expect("FATAL: corrupt affirmation map")
            }
            None => AffirmationMap::empty(),
        };
        Ok(affirmation_map)
    }

    pub fn get_last_selected_anchor_block_hash(&self) -> Result<Option<BlockHeaderHash>, db_error> {
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(self.get_indexed(
            &self.context.chain_tip,
            &db_keys::pox_last_selected_anchor(),
        )?);
        Ok(anchor_block_hash)
    }

    pub fn get_last_selected_anchor_block_txid(&self) -> Result<Option<Txid>, db_error> {
        let anchor_block_txid = SortitionDB::parse_last_anchor_block_txid(self.get_indexed(
            &self.context.chain_tip,
            &db_keys::pox_last_selected_anchor_txid(),
        )?);
        Ok(anchor_block_txid)
    }

    pub fn get_reward_cycle_unlocks(
        &mut self,
        cycle: u64,
    ) -> Result<Option<PoxStartCycleInfo>, db_error> {
        let start_info = self
            .get_tip_indexed(&db_keys::pox_reward_cycle_unlocks(cycle))?
            .map(|x| {
                PoxStartCycleInfo::deserialize(&x)
                    .expect("CORRUPTION: Failed to deserialize PoxStartCycleInfo from database")
            });
        Ok(start_info)
    }

    pub fn get_pox_id(&self) -> Result<PoxId, db_error> {
        let pox_id = self
            .get_tip_indexed(db_keys::pox_identifier())?
            .map(|s| s.parse().expect("BUG: Bad PoX identifier stored in DB"))
            .expect("BUG: No PoX identifier stored.");
        Ok(pox_id)
    }

    /// open a reader handle
    pub fn open_reader(
        connection: &'a SortitionDBConn<'a>,
        chain_tip: &SortitionId,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        Ok(SortitionHandleConn {
            context: SortitionHandleContext {
                chain_tip: chain_tip.clone(),
                first_block_height: connection.context.first_block_height,
                pox_constants: connection.context.pox_constants.clone(),
                dryrun: connection.context.dryrun,
            },
            index: &connection.index,
        })
    }

    fn get_tip_indexed(&self, key: &str) -> Result<Option<String>, db_error> {
        self.get_indexed(&self.context.chain_tip, key)
    }

    fn get_sortition_id_for_bhh(
        &self,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<SortitionId>, db_error> {
        let sortition_identifier_key = db_keys::sortition_id_for_bhh(burn_header_hash);
        let sortition_id = match self.get_tip_indexed(&sortition_identifier_key)? {
            None => return Ok(None),
            Some(x) => SortitionId::from_hex(&x).expect("FATAL: bad Sortition ID stored in DB"),
        };
        Ok(Some(sortition_id))
    }

    /// Uses the handle's current fork identifier to get a block snapshot by
    ///   burnchain block header
    /// If the burn header hash is _not_ in the current fork, then this will return Ok(None)
    pub fn get_block_snapshot(
        &self,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let sortition_id = match self.get_sortition_id_for_bhh(burn_header_hash)? {
            None => return Ok(None),
            Some(x) => x,
        };
        SortitionDB::get_block_snapshot(self.conn(), &sortition_id)
    }

    /// Has `consensus_hash` been processed in the current fork?
    pub fn processed_block(&self, consensus_hash: &ConsensusHash) -> Result<bool, db_error> {
        let Some(snapshot) = SortitionDB::get_block_snapshot_consensus(self, consensus_hash)?
        else {
            return Ok(false);
        };
        let Some(expected_sortition_id) =
            self.get_sortition_id_for_bhh(&snapshot.burn_header_hash)?
        else {
            return Ok(false);
        };
        let matched_fork = expected_sortition_id == snapshot.sortition_id;
        Ok(matched_fork)
    }

    pub fn get_tip_snapshot(&self) -> Result<Option<BlockSnapshot>, db_error> {
        SortitionDB::get_block_snapshot(self.conn(), &self.context.chain_tip)
    }

    pub fn get_first_block_snapshot(&self) -> Result<BlockSnapshot, db_error> {
        SortitionDB::get_first_block_snapshot(self.conn())
    }

    /// Get consensus hash from a particular chain tip's history
    /// Returns None if the block height or block hash does not correspond to a
    /// known snapshot.
    pub fn get_consensus_at(&self, block_height: u64) -> Result<Option<ConsensusHash>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        match SortitionDB::get_ancestor_snapshot(self, block_height, &self.context.chain_tip)? {
            Some(sn) => Ok(Some(sn.consensus_hash)),
            None => Ok(None),
        }
    }

    pub fn get_block_snapshot_by_height(
        &self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        // Note: This would return None if `block_height` were the height of `chain_tip`.
        SortitionDB::get_ancestor_snapshot(self, block_height, &self.context.chain_tip)
    }

    /// Get the block snapshot of the parent stacks block of the given stacks block.
    /// The returned block-commit is for the given (consensus_hash, block_hash).
    /// The returned BlockSnapshot is for the parent of the block identified by (consensus_hash,
    /// block_hash).
    pub fn get_block_snapshot_of_parent_stacks_block(
        &self,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<(LeaderBlockCommitOp, BlockSnapshot)>, db_error> {
        let block_commit = match SortitionDB::get_block_commit_for_stacks_block(
            self.conn(),
            consensus_hash,
            &block_hash,
        )? {
            Some(bc) => bc,
            None => {
                // unsoliciated
                debug!("No block commit for {}/{}", consensus_hash, block_hash);
                return Ok(None);
            }
        };

        // get the stacks chain tip this block commit builds off of
        let stacks_chain_tip =
            if block_commit.parent_block_ptr == 0 && block_commit.parent_vtxindex == 0 {
                // no parent -- this is the first-ever Stacks block in this fork
                test_debug!(
                    "Block {}/{} mines off of genesis",
                    consensus_hash,
                    block_hash
                );
                self.get_first_block_snapshot()?
            } else {
                let parent_commit = match self.get_block_commit_parent(
                    block_commit.parent_block_ptr.into(),
                    block_commit.parent_vtxindex.into(),
                )? {
                    Some(commit) => commit,
                    None => {
                        // unsolicited -- orphaned
                        warn!(
                        "Received unsolicited block, could not find parent: {}/{}, parent={}/{}",
                        consensus_hash, block_hash, block_commit.parent_block_ptr, consensus_hash
                    );
                        return Ok(None);
                    }
                };

                debug!(
                    "Block {}/{} mines off of parent {},{}",
                    consensus_hash, block_hash, parent_commit.block_height, parent_commit.vtxindex
                );
                self.get_block_snapshot(&parent_commit.burn_header_hash)?
                    .expect("FATAL: burn DB does not have snapshot for parent block commit")
            };

        Ok(Some((block_commit, stacks_chain_tip)))
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    /// Search snapshots up to (but excluding) the given block height.
    /// Will always return a snapshot -- even if it's the initial sentinel snapshot.
    pub fn get_last_snapshot_with_sortition(
        &self,
        burn_block_height: u64,
    ) -> Result<BlockSnapshot, db_error> {
        assert!(burn_block_height < BLOCK_HEIGHT_MAX);
        test_debug!(
            "Get snapshot at from sortition tip {}, expect height {}",
            &self.context.chain_tip,
            burn_block_height
        );
        let get_from = match get_ancestor_sort_id(self, burn_block_height, &self.context.chain_tip)?
        {
            Some(sortition_id) => sortition_id,
            None => {
                error!(
                    "No blockheight {} ancestor at sortition identifier {}",
                    burn_block_height, &self.context.chain_tip
                );
                return Err(db_error::NotFoundError);
            }
        };

        let ancestor_hash = match self.get_indexed(&get_from, &db_keys::last_sortition())? {
            Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).unwrap_or_else(|_| {
                panic!(
                    "FATAL: corrupt database: failed to parse {} into a hex string",
                    &hex_str
                )
            }),
            None => {
                // no prior sortitions, so get the first
                return self.get_first_block_snapshot();
            }
        };

        self.get_block_snapshot(&ancestor_hash).map(|snapshot_opt| {
            snapshot_opt
                .unwrap_or_else(|| panic!("FATAL: corrupt index: no snapshot {}", ancestor_hash))
        })
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    pub fn get_last_snapshot_with_sortition_from_tip(&self) -> Result<BlockSnapshot, db_error> {
        let ancestor_hash =
            match self.get_indexed(&self.context.chain_tip, &db_keys::last_sortition())? {
                Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).unwrap_or_else(|_| {
                    panic!(
                        "FATAL: corrupt database: failed to parse {} into a hex string",
                        &hex_str
                    )
                }),
                None => {
                    // no prior sortitions, so get the first
                    return self.get_first_block_snapshot();
                }
            };

        self.get_block_snapshot(&ancestor_hash).map(|snapshot_opt| {
            snapshot_opt
                .unwrap_or_else(|| panic!("FATAL: corrupt index: no snapshot {}", ancestor_hash))
        })
    }

    pub fn get_leader_key_at(
        &self,
        key_block_height: u64,
        key_vtxindex: u32,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        SortitionDB::get_leader_key_at(
            self,
            key_block_height,
            key_vtxindex,
            &self.context.chain_tip,
        )
    }

    pub fn get_block_commit_parent(
        &self,
        block_height: u64,
        vtxindex: u32,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        SortitionDB::get_block_commit_parent(self, block_height, vtxindex, &self.context.chain_tip)
    }

    /// Get a block commit by txid. In the event of a burnchain fork, this may not be unique.
    ///   this function simply returns one of those block commits: only use data that is
    ///   immutable across burnchain/pox forks, e.g., parent block ptr,
    pub fn get_block_commit_by_txid(
        &self,
        sort_id: &SortitionId,
        txid: &Txid,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        get_block_commit_by_txid(self.conn(), sort_id, txid)
    }

    /// Return a vec of sortition winner's burn header hash and stacks header hash, ordered by
    ///   increasing block height in the range (block_height_begin, block_height_end]
    fn get_sortition_winners_in_fork(
        &self,
        block_height_begin: u32,
        block_height_end: u32,
    ) -> Result<Vec<(SortitionId, Txid, u64)>, BurnchainError> {
        let mut result = vec![];
        for height in (block_height_begin + 1)..(block_height_end + 1) {
            debug!("Looking for winners at height = {}", height);
            let snapshot =
                SortitionDB::get_ancestor_snapshot(self, height as u64, &self.context.chain_tip)?
                    .ok_or_else(|| {
                    warn!("Missing parent"; "sortition_height" => %height);
                    BurnchainError::MissingParentBlock
                })?;
            if snapshot.sortition {
                result.push((
                    snapshot.sortition_id,
                    snapshot.winning_block_txid,
                    snapshot.block_height,
                ));
            }
        }
        Ok(result)
    }

    /// Helper method to get the burn block height of the end of a prepare phase block.
    /// Returns Ok(Some((effective_height, absolute_height))) on success
    /// Returns Ok(None) if the effective height of this block was 0, meaning that it's the first
    /// block.
    /// Returns Err(BurnchainError::MissingParentBlock) if we couldn't find the sortition for this
    /// burnchain block hash
    /// Returns Err(CoordiantorError::NotPrepareEndBlock) if this wasn't the last block in a
    /// prepare phase.
    fn get_heights_for_prepare_phase_end_block(
        &self,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
        check_position: bool,
    ) -> Result<Option<(u32, u32)>, CoordinatorError> {
        let prepare_end_sortid =
            self.get_sortition_id_for_bhh(prepare_end_bhh)?
                .ok_or_else(|| {
                    warn!("Missing parent"; "burn_header_hash" => %prepare_end_bhh, "sortition_tip" => %&self.context.chain_tip);
                    BurnchainError::MissingParentBlock
                })?;
        let block_height = SortitionDB::get_block_height(self.deref(), &prepare_end_sortid)?
            .expect("CORRUPTION: SortitionID known, but no block height in SQL store");

        // if this block is the _end_ of a prepare phase,
        let effective_height = block_height - self.context.first_block_height as u32;
        let position_in_cycle = effective_height % pox_consts.reward_cycle_length;
        if position_in_cycle != 0 {
            debug!(
                "effective_height = {}, reward cycle length == {}",
                effective_height, pox_consts.reward_cycle_length
            );
            if check_position {
                return Err(CoordinatorError::NotPrepareEndBlock);
            }
        }

        if effective_height == 0 {
            debug!(
                "effective_height = {}, reward cycle length == {}",
                effective_height, pox_consts.reward_cycle_length
            );
            return Ok(None);
        }

        Ok(Some((effective_height, block_height)))
    }

    /// Get the chosen PoX anchor block for a reward cycle, given the last block of its prepare
    /// phase.
    ///
    /// In epochs 2.05 and earlier, this was the Stacks block that received F*w confirmations.
    ///
    /// In epoch 2.1 and later, this was the Stacks block whose block-commit received not only F*w
    /// confirmations from subsequent block-commits in the prepare phase, but also the most BTC
    /// burnt from all such candidates (and if there is still a tie, then the higher block-commit
    /// is chosen).  In particular, the block-commit is not required to be the winning block-commit
    /// or even a valid block-commit, unlike in 2.05.  However, this will be a winning block-commit
    /// if at least 20% of the BTC was spent honestly.
    ///
    /// Here, instead of reasoning about which epoch we're in, the caller will instead supply an
    /// optional handle to the burnchain database.  If it's `Some(..)`, then the epoch 2.1 rules
    /// are used -- the PoX anchor block will be determined from block-commits.  If it's `None`,
    /// then the epoch 2.05 rules are used -- the PoX anchor block will be determined from present
    /// Stacks blocks.
    pub fn get_chosen_pox_anchor(
        &self,
        burnchain_db_conn: Option<&DBConn>,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, Txid)>, CoordinatorError> {
        match burnchain_db_conn {
            Some(conn) => self.get_chosen_pox_anchor_v210(conn, prepare_end_bhh, pox_consts),
            None => self.get_chosen_pox_anchor_v205(prepare_end_bhh, pox_consts),
        }
    }

    /// Use the epoch 2.1 method for choosing a PoX anchor block.
    /// The PoX anchor block corresponds to the block-commit that received F*w confirmations in its
    /// prepare phase, and had the most BTC of all such candidates, and was the highest of all such
    /// candidates.  This information is stored in the burnchain DB.
    ///
    /// Note that it does not matter if the anchor block-commit does not correspond to a valid
    /// Stacks block, or even won sortition.  The result is the same for the honest network
    /// participants: they mark the anchor block as absent in their affirmation maps, and this PoX
    /// fork's quality is degraded as such.
    pub fn get_chosen_pox_anchor_v210(
        &self,
        burnchain_db_conn: &DBConn,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, Txid)>, CoordinatorError> {
        let rc = match self.get_heights_for_prepare_phase_end_block(
            prepare_end_bhh,
            pox_consts,
            true,
        )? {
            Some((_, block_height)) => {
                let rc = pox_consts
                    .block_height_to_reward_cycle(
                        self.context.first_block_height,
                        block_height.into(),
                    )
                    .ok_or(CoordinatorError::NotPrepareEndBlock)?;
                rc
            }
            None => {
                // there can't be an anchor block
                return Ok(None);
            }
        };
        let (anchor_block_op, anchor_block_metadata) = {
            let mut res = None;
            let metadatas = BurnchainDB::get_anchor_block_commit_metadatas(burnchain_db_conn, rc)?;

            // find the one on this fork
            for metadata in metadatas {
                let sn = SortitionDB::get_ancestor_snapshot(
                    self,
                    metadata.block_height,
                    &self.context.chain_tip,
                )?
                .expect("FATAL: accepted block-commit but no sortition at height");
                if sn.burn_header_hash == metadata.burn_block_hash {
                    // this is the metadata on this burnchain fork
                    res = match BurnchainDB::get_anchor_block_commit(
                        burnchain_db_conn,
                        &sn.burn_header_hash,
                        rc,
                    )? {
                        Some(x) => Some(x),
                        None => {
                            continue;
                        }
                    };
                    if res.is_some() {
                        break;
                    }
                }
            }
            if let Some(x) = res {
                x
            } else {
                // no anchor block
                test_debug!("No anchor block for reward cycle {}", rc);
                return Ok(None);
            }
        };

        // sanity check: we must have processed this burnchain block already
        let anchor_sort_id = self.get_sortition_id_for_bhh(&anchor_block_metadata.burn_block_hash)?
            .ok_or_else(|| {
                warn!("Missing anchor block sortition"; "burn_header_hash" => %anchor_block_metadata.burn_block_hash, "sortition_tip" => %&self.context.chain_tip);
                BurnchainError::MissingParentBlock
            })?;

        let anchor_sn = SortitionDB::get_block_snapshot(self, &anchor_sort_id)?
            .ok_or(BurnchainError::MissingParentBlock)?;

        // the sortition does not even need to have picked this anchor block; all that matters is
        // that miners confirmed it.  If the winning block hash doesn't even correspond to a Stacks
        // block, then the honest miners in the network will affirm that it's absent.
        let ch = anchor_sn.consensus_hash;
        Ok(Some((
            ch,
            anchor_block_op.block_header_hash,
            anchor_block_op.txid,
        )))
    }

    /// This is the method for calculating the PoX anchor block for a reward cycle in epoch 2.05 and earlier.
    /// Return identifying information for a PoX anchor block for the reward cycle that
    ///   begins the block after `prepare_end_bhh`.
    /// If a PoX anchor block is chosen, this returns Some, if a PoX anchor block was not
    ///   selected, return `None`
    /// `prepare_end_bhh`: this is the burn block which is the last block in the prepare phase
    ///                 for the corresponding reward cycle
    fn get_chosen_pox_anchor_v205(
        &self,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, Txid)>, CoordinatorError> {
        match self.get_chosen_pox_anchor_check_position_v205(prepare_end_bhh, pox_consts, true) {
            Ok(Ok((c_hash, bh_hash, txid, _))) => Ok(Some((c_hash, bh_hash, txid))),
            Ok(Err(_)) => Ok(None),
            Err(e) => Err(e),
        }
    }

    /// This is the method for calculating the PoX anchor block for a reward cycle in epoch 2.05 and earlier.
    /// If no PoX anchor block is found, it returns Ok(Err(maximum confirmations of all candidates))
    pub fn get_chosen_pox_anchor_check_position_v205(
        &self,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
        check_position: bool,
    ) -> Result<Result<(ConsensusHash, BlockHeaderHash, Txid, u32), u32>, CoordinatorError> {
        let (effective_height, block_height) = match self.get_heights_for_prepare_phase_end_block(
            prepare_end_bhh,
            pox_consts,
            check_position,
        )? {
            Some(x) => x,
            None => {
                // effective height was 0
                return Ok(Err(0));
            }
        };

        let prepare_end = block_height;
        let prepare_begin = prepare_end.saturating_sub(pox_consts.prepare_length);

        let mut candidate_anchors = HashMap::new();
        let mut memoized_candidates: HashMap<_, (SortitionId, Txid, u64)> = HashMap::new();

        // iterate over every sortition winner in the prepare phase
        //   looking for their highest ancestor _before_ prepare_begin.
        let winners = self.get_sortition_winners_in_fork(prepare_begin, prepare_end)?;
        for (winner_sort_id, winner_commit_txid, winner_block_height) in winners.into_iter() {
            let mut cursor = (winner_sort_id, winner_commit_txid, winner_block_height);
            let mut found_ancestor = true;

            while cursor.2 > (prepare_begin as u64) {
                // check if we've already discovered the candidate for this block
                if let Some(ancestor) = memoized_candidates.get(&cursor.2) {
                    cursor = ancestor.clone();
                } else {
                    // get the block commit
                    let block_commit = self.get_block_commit_by_txid(&cursor.0, &cursor.1)?.expect(
                        "CORRUPTED: Failed to fetch block commit for known sortition winner",
                    );
                    // is this a height=1 block?
                    if block_commit.is_parent_genesis() {
                        debug!("First parent before prepare phase for block winner is the genesis block, dropping block's PoX anchor vote";
                               "sortition_id" => %&cursor.0,
                               "winner_txid" => %&cursor.1,
                               "burn_block_height" => cursor.2);
                        found_ancestor = false;
                        break;
                    }

                    // find the parent sortition
                    let sn = SortitionDB::get_ancestor_snapshot(
                        self,
                        block_commit.parent_block_ptr as u64,
                        &self.context.chain_tip,
                    )?
                    .expect(
                        "CORRUPTED: accepted block commit, but parent pointer not in sortition set",
                    );
                    assert!(sn.sortition, "CORRUPTED: accepted block commit, but parent pointer not a sortition winner");

                    cursor = (sn.sortition_id, sn.winning_block_txid, sn.block_height);
                }
            }
            if !found_ancestor {
                continue;
            }
            // this is the burn block height of the sortition that chose the
            //   highest ancestor of winner_stacks_bh whose sortition occurred before prepare_begin
            //  the winner of that sortition is the PoX anchor block candidate that winner_stacks_bh is "voting for"
            let highest_ancestor = cursor.2;
            memoized_candidates.insert(winner_block_height, cursor);
            if let Some(x) = candidate_anchors.get_mut(&highest_ancestor) {
                *x += 1;
            } else {
                candidate_anchors.insert(highest_ancestor, 1u32);
            }
        }

        // did any candidate receive >= F*w?
        let mut result = None;
        let mut max_confirmed_by = 0;
        for (candidate, confirmed_by) in candidate_anchors.into_iter() {
            if confirmed_by > max_confirmed_by {
                max_confirmed_by = confirmed_by;
            }
            if confirmed_by >= pox_consts.anchor_threshold {
                // find the sortition at height
                let sn =
                    SortitionDB::get_ancestor_snapshot(self, candidate, &self.context.chain_tip)?
                        .expect("BUG: cannot find chosen PoX candidate's sortition");
                assert!(
                    result
                        .replace((
                            sn.consensus_hash,
                            sn.winning_stacks_block_hash,
                            sn.winning_block_txid,
                            confirmed_by
                        ))
                        .is_none(),
                    "BUG: multiple anchor blocks received more confirmations than anchor_threshold"
                );
            }
        }

        let reward_cycle_id = effective_height / pox_consts.reward_cycle_length;
        match result {
            None => {
                info!(
                    "Reward cycle #{} ({}): (F*w) not reached, expecting consensus over proof of burn",
                    reward_cycle_id, block_height
                );
                Ok(Err(max_confirmed_by))
            }
            Some(response) => {
                info!("Reward cycle #{} ({}): {:?} reached (F*w), expecting consensus over proof of transfer", reward_cycle_id, block_height, result);
                Ok(Ok(response))
            }
        }
    }

    pub fn get_reward_set_payouts_at(
        &self,
        sortition_id: &SortitionId,
    ) -> Result<(Vec<PoxAddress>, u128), db_error> {
        let sql = "SELECT pox_payouts FROM snapshots WHERE sortition_id = ?1";
        let args = params![sortition_id];
        let pox_addrs_json: String = query_row(self, sql, args)?.ok_or(db_error::NotFoundError)?;

        let pox_addrs: (Vec<PoxAddress>, u128) =
            serde_json::from_str(&pox_addrs_json).expect("FATAL: failed to decode pox payout JSON");
        Ok(pox_addrs)
    }

    /// Is a consensus hash's sortition valid on the fork represented by this handle?
    /// Return Ok(true) if so
    /// Return Ok(false) if not (including if there is no sortition with this consensus hash)
    /// Return Err(..) on DB error
    pub fn has_consensus_hash(&self, consensus_hash: &ConsensusHash) -> Result<bool, db_error> {
        let Some(sn) = SortitionDB::get_block_snapshot_consensus(self, consensus_hash)? else {
            // no sortition with this consensus hash
            return Ok(false);
        };

        let Some(expected_sortition_id) =
            get_ancestor_sort_id(self, sn.block_height, &self.context.chain_tip)?
        else {
            // no ancestor at this sortition height relative to this chain tip
            // (e.g. perhaps this consensus hash is in the "future" relative to this chain tip)
            return Ok(false);
        };

        Ok(sn.sortition_id == expected_sortition_id)
    }
}

// Connection methods
impl SortitionDB {
    /// Begin a transaction.
    pub fn tx_begin(&mut self) -> Result<SortitionDBTx<'_>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }

        let index_tx = SortitionDBTx::new(
            &mut self.marf,
            SortitionDBTxContext {
                first_block_height: self.first_block_height,
                pox_constants: self.pox_constants.clone(),
                dryrun: self.dryrun,
            },
        );
        Ok(index_tx)
    }

    /// Make an indexed connection
    pub fn index_conn(&self) -> SortitionDBConn<'_> {
        SortitionDBConn::new(
            &self.marf,
            SortitionDBTxContext {
                first_block_height: self.first_block_height,
                pox_constants: self.pox_constants.clone(),
                dryrun: self.dryrun,
            },
        )
    }

    pub fn index_handle<'a>(&'a self, chain_tip: &SortitionId) -> SortitionHandleConn<'a> {
        SortitionHandleConn::new(
            &self.marf,
            SortitionHandleContext {
                first_block_height: self.first_block_height,
                chain_tip: chain_tip.clone(),
                pox_constants: self.pox_constants.clone(),
                dryrun: self.dryrun,
            },
        )
    }

    pub fn index_handle_at_block<'a>(
        &'a self,
        chainstate: &StacksChainState,
        stacks_block_id: &StacksBlockId,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        let lookup_block_id = if let Some(ref unconfirmed_state) = chainstate.unconfirmed_state {
            if &unconfirmed_state.unconfirmed_chain_tip == stacks_block_id {
                &unconfirmed_state.confirmed_chain_tip
            } else {
                stacks_block_id
            }
        } else {
            stacks_block_id
        };
        let header = match NakamotoChainState::get_block_header(chainstate.db(), lookup_block_id) {
            Ok(Some(x)) => x,
            x => {
                debug!("Failed to get block header: {:?}", x);
                return Err(db_error::NotFoundError);
            }
        };
        // if its a nakamoto block, we want to use the burnchain view of the block
        let burn_view = match &header.anchored_header {
            StacksBlockHeaderTypes::Epoch2(_) => header.consensus_hash,
            StacksBlockHeaderTypes::Nakamoto(_) => header.burn_view.ok_or_else(|| {
                error!("Loaded nakamoto block header without a burn view"; "block_id" => %stacks_block_id);
                db_error::Other("Nakamoto block header without burn view".into())
            })?,
        };

        let snapshot = SortitionDB::get_block_snapshot_consensus(&self.conn(), &burn_view)?
            .ok_or(db_error::NotFoundError)?;
        Ok(self.index_handle(&snapshot.sortition_id))
    }

    pub fn tx_handle_begin<'a>(
        &'a mut self,
        chain_tip: &SortitionId,
    ) -> Result<SortitionHandleTx<'a>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }
        Ok(SortitionHandleTx::new(
            &mut self.marf,
            SortitionHandleContext {
                first_block_height: self.first_block_height,
                chain_tip: chain_tip.clone(),
                pox_constants: self.pox_constants.clone(),
                dryrun: self.dryrun,
            },
        ))
    }

    pub fn conn(&self) -> &Connection {
        self.marf.sqlite_conn()
    }

    fn open_index(index_path: &str) -> Result<MARF<SortitionId>, db_error> {
        test_debug!("Open index at {}", index_path);
        let open_opts = MARFOpenOpts::default();
        let marf = MARF::from_path(index_path, open_opts).map_err(|_e| db_error::Corruption)?;
        sql_pragma(marf.sqlite_conn(), "foreign_keys", &true)?;
        Ok(marf)
    }

    /// Open the database on disk.  It must already exist and be instantiated.
    /// It's best not to call this if you are able to call connect().  If you must call this, do so
    /// after you call connect() somewhere else, since connect() performs additional validations.
    pub fn open(
        path: &str,
        readwrite: bool,
        pox_constants: PoxConstants,
    ) -> Result<SortitionDB, db_error> {
        let index_path = db_mkdirs(path)?;
        debug!(
            "Open sortdb as '{}', with index as '{}'",
            if readwrite { "readwrite" } else { "readonly" },
            index_path
        );

        let marf = SortitionDB::open_index(&index_path)?;
        let (first_block_height, first_burn_header_hash) =
            SortitionDB::get_first_block_height_and_hash(marf.sqlite_conn())?;

        let mut db = SortitionDB {
            path: path.to_string(),
            marf,
            readwrite,
            dryrun: false,
            pox_constants,
            first_block_height,
            first_burn_header_hash,
        };

        db.check_schema_version_or_error()?;
        Ok(db)
    }

    /// Open a new copy of this SortitionDB. Will use the same `readwrite` flag
    ///  of `self`.
    pub fn reopen(&self) -> Result<SortitionDB, db_error> {
        Self::open(&self.path, self.readwrite, self.pox_constants.clone())
    }

    /// Open the burn database at the given path.  Open read-only or read/write.
    /// If opened for read/write and it doesn't exist, instantiate it.
    pub fn connect(
        path: &str,
        first_block_height: u64,
        first_burn_hash: &BurnchainHeaderHash,
        first_burn_header_timestamp: u64,
        epochs: &[StacksEpoch],
        pox_constants: PoxConstants,
        migrator: Option<SortitionDBMigrator>,
        readwrite: bool,
    ) -> Result<SortitionDB, db_error> {
        let create_flag = match fs::metadata(path) {
            Err(e) => {
                if e.kind() == ErrorKind::NotFound {
                    // need to create
                    if readwrite {
                        true
                    } else {
                        return Err(db_error::NoDBError);
                    }
                } else {
                    return Err(db_error::IOError(e));
                }
            }
            Ok(_md) => false,
        };

        let index_path = db_mkdirs(path)?;
        debug!(
            "Connect/Open {} sortdb as '{}', with index as '{}'",
            if create_flag { "(create)" } else { "" },
            if readwrite { "readwrite" } else { "readonly" },
            index_path
        );

        let marf = SortitionDB::open_index(&index_path)?;

        let mut db = SortitionDB {
            path: path.to_string(),
            marf,
            readwrite,
            dryrun: false,
            first_block_height,
            pox_constants,
            first_burn_header_hash: first_burn_hash.clone(),
        };

        if create_flag {
            // instantiate!
            db.instantiate(
                first_block_height,
                first_burn_hash,
                first_burn_header_timestamp,
                epochs,
            )?;
        }

        db.check_schema_version_and_update(epochs, migrator)?;

        // validate -- must contain the given first block and first block hash
        let snapshot = SortitionDB::get_first_block_snapshot(db.conn())?;
        if !snapshot.is_initial()
            || snapshot.block_height != first_block_height
            || snapshot.burn_header_hash != *first_burn_hash
        {
            error!("Invalid genesis snapshot: sn.is_initial = {}, sn.block_height = {}, sn.burn_hash = {}, expect.block_height = {}, expect.burn_hash = {}",
                   snapshot.is_initial(), snapshot.block_height, &snapshot.burn_header_hash, first_block_height, first_burn_hash);
            return Err(db_error::Corruption);
        }

        if readwrite {
            db.add_indexes()?;
        }

        Ok(db)
    }

    fn instantiate(
        &mut self,
        first_block_height: u64,
        first_burn_header_hash: &BurnchainHeaderHash,
        first_burn_header_timestamp: u64,
        epochs_ref: &[StacksEpoch],
    ) -> Result<(), db_error> {
        debug!(
            "Instantiate SortDB: first block is {},{}",
            first_block_height, first_burn_header_hash
        );

        sql_pragma(self.conn(), "journal_mode", &"WAL")?;
        sql_pragma(self.conn(), "foreign_keys", &true)?;

        let mut db_tx = SortitionHandleTx::begin(self, &SortitionId::sentinel())?;

        // create first (sentinel) snapshot
        debug!("Make first snapshot");
        let mut first_snapshot = BlockSnapshot::initial(
            first_block_height,
            first_burn_header_hash,
            first_burn_header_timestamp,
        );

        assert!(first_snapshot.parent_burn_header_hash != first_snapshot.burn_header_hash);
        assert_eq!(
            first_snapshot.parent_burn_header_hash,
            BurnchainHeaderHash::sentinel()
        );

        for row_text in SORTITION_DB_INITIAL_SCHEMA {
            db_tx.execute_batch(row_text)?;
        }
        SortitionDB::apply_schema_2(&db_tx, epochs_ref)?;
        SortitionDB::apply_schema_3(&db_tx)?;
        SortitionDB::apply_schema_4(&db_tx)?;
        SortitionDB::apply_schema_5(&db_tx, epochs_ref)?;
        SortitionDB::apply_schema_6(&db_tx, epochs_ref)?;
        SortitionDB::apply_schema_7(&db_tx, epochs_ref)?;
        SortitionDB::apply_schema_8_tables(&db_tx, epochs_ref)?;

        db_tx.instantiate_index()?;

        let mut first_sn = first_snapshot.clone();
        first_sn.sortition_id = SortitionId::sentinel();
        let (index_root, pox_payout) =
            db_tx.index_add_fork_info(&mut first_sn, &first_snapshot, &[], None, None, None)?;
        first_snapshot.index_root = index_root;

        db_tx.insert_block_snapshot(&first_snapshot, pox_payout)?;
        db_tx.store_transition_ops(
            &first_snapshot.sortition_id,
            &BurnchainStateTransition::noop(),
        )?;

        db_tx.commit()?;

        // NOTE: we don't need to provide a migrator here because we're not migrating
        self.apply_schema_8_migration(None)?;

        let db_tx = SortitionHandleTx::begin(self, &SortitionId::sentinel())?;
        SortitionDB::apply_schema_9(&db_tx, epochs_ref)?;

        db_tx.commit()?;

        self.add_indexes()?;

        debug!("Instantiated SortDB");
        Ok(())
    }

    /// Validates given StacksEpochs (will runtime panic if there is any invalid StacksEpoch structuring) and
    ///  inserts them into the SortitionDB's epochs table.
    fn validate_and_insert_epochs(
        db_tx: &Transaction,
        epochs: &[StacksEpoch],
    ) -> Result<(), db_error> {
        let epochs = StacksEpoch::validate_epochs(epochs);
        for epoch in epochs.into_iter() {
            let args = params![
                (epoch.epoch_id as u32),
                u64_to_sql(epoch.start_height)?,
                u64_to_sql(epoch.end_height)?,
                epoch.block_limit,
                epoch.network_epoch,
            ];
            db_tx.execute(
                "INSERT INTO epochs (epoch_id,start_block_height,end_block_height,block_limit,network_epoch) VALUES (?1,?2,?3,?4,?5)",
                args
            )?;
        }
        Ok(())
    }

    /// Validates given StacksEpochs (will runtime panic if there is any invalid StacksEpoch structuring) and
    /// replaces them into the SortitionDB's epochs table
    fn validate_and_replace_epochs(
        db_tx: &Transaction,
        epochs: &[StacksEpoch],
    ) -> Result<(), db_error> {
        let epochs: &[StacksEpoch] = &StacksEpoch::validate_epochs(epochs);
        let existing_epochs = Self::get_stacks_epochs(db_tx)?;
        if &existing_epochs == epochs {
            return Ok(());
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db_tx)?;
        let existing_epoch_idx = StacksEpoch::find_epoch(&existing_epochs, tip.block_height)
            .unwrap_or_else(|| {
                panic!(
                    "FATAL: Sortition tip {} has no epoch in its existing epochs table",
                    tip.block_height
                );
            });

        let new_epoch_idx =
            StacksEpoch::find_epoch(&epochs, tip.block_height).unwrap_or_else(|| {
                panic!(
                    "FATAL: Sortition tip {} has no epoch in the configured epochs list",
                    tip.block_height
                );
            });

        // can't retcon epochs -- all epochs up to (but excluding) the tip's epoch in both epoch
        // lists must be the same.
        for i in 0..existing_epoch_idx.min(new_epoch_idx) {
            if existing_epochs[i] != epochs[i] {
                panic!(
                    "FATAL: tried to retcon epoch {:?} into epoch {:?}",
                    &existing_epochs[i], &epochs[i]
                );
            }
        }

        // can't change parameters of the current epoch in either epoch list,
        // except for the end height (and only if it hasn't been reached yet)
        let mut diff_epoch = existing_epochs[existing_epoch_idx].clone();
        diff_epoch.end_height = epochs[new_epoch_idx].end_height;

        if diff_epoch != epochs[new_epoch_idx] {
            panic!(
                "FATAL: tried to change current epoch {:?} into {:?}",
                &existing_epochs[existing_epoch_idx], &epochs[new_epoch_idx]
            );
        }

        if tip.block_height >= epochs[new_epoch_idx].end_height {
            panic!("FATAL: tip has reached or passed the end of the configured epoch");
        }

        info!("Replace existing epochs with new epochs");
        db_tx.execute("DELETE FROM epochs;", NO_PARAMS)?;
        for epoch in epochs.into_iter() {
            let args = params![
                (epoch.epoch_id as u32),
                u64_to_sql(epoch.start_height)?,
                u64_to_sql(epoch.end_height)?,
                epoch.block_limit,
                epoch.network_epoch,
            ];
            db_tx.execute(
                "INSERT INTO epochs (epoch_id,start_block_height,end_block_height,block_limit,network_epoch) VALUES (?1,?2,?3,?4,?5)",
                args
            )?;
        }
        Ok(())
    }

    /// Get a block commit by its content-addressed location in a specific sortition.
    pub fn get_block_commit(
        conn: &Connection,
        txid: &Txid,
        sortition_id: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        let qry = "SELECT * FROM block_commits WHERE txid = ?1 AND sortition_id = ?2";
        let args = params![txid, sortition_id];
        query_row(conn, qry, args)
    }

    /// Get the Sortition ID for the burnchain block containing `txid`'s parent.
    /// `txid` is the burnchain txid of a block-commit.
    pub fn get_block_commit_parent_sortition_id(
        conn: &Connection,
        txid: &Txid,
        sortition_id: &SortitionId,
    ) -> Result<Option<SortitionId>, db_error> {
        let qry = "SELECT parent_sortition_id AS sortition_id FROM block_commit_parents WHERE block_commit_parents.block_commit_txid = ?1 AND block_commit_parents.block_commit_sortition_id = ?2";
        let args = params![txid, sortition_id];
        query_row(conn, qry, args)
    }

    /// Load up all snapshots, in ascending order by block height.  Great for testing!
    pub fn get_all_snapshots(&self) -> Result<Vec<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots ORDER BY block_height ASC";
        query_rows(self.conn(), qry, NO_PARAMS)
    }

    /// Get all snapshots for a burn block hash, even if they're not on the canonical PoX fork.
    pub fn get_all_snapshots_for_burn_block(
        conn: &DBConn,
        bhh: &BurnchainHeaderHash,
    ) -> Result<Vec<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE burn_header_hash = ?1";
        query_rows(conn, qry, &[bhh])
    }

    /// Get all snapshots for a burn block height, even if they're not on the canonical PoX fork
    pub fn get_all_snapshots_by_burn_height(
        conn: &DBConn,
        height: u64,
    ) -> Result<Vec<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE block_height = ?1";
        query_rows(conn, qry, params![u64_to_sql(height)?])
    }

    /// Get all preprocessed reward sets and their associated anchor blocks
    pub fn get_all_preprocessed_reward_sets(
        conn: &DBConn,
    ) -> Result<Vec<(SortitionId, RewardCycleInfo)>, db_error> {
        let sql = "SELECT * FROM preprocessed_reward_sets;";
        let mut stmt = conn.prepare(sql)?;
        let mut qry = stmt.query(NO_PARAMS)?;
        let mut ret = vec![];
        while let Some(row) = qry.next()? {
            let sort_id: SortitionId = row.get("sortition_id")?;
            let reward_set_str: String = row.get("reward_set")?;
            let reward_set: RewardCycleInfo =
                serde_json::from_str(&reward_set_str).map_err(|_| db_error::ParseError)?;
            ret.push((sort_id, reward_set));
        }
        Ok(ret)
    }

    /// Get the height of a consensus hash, even if it's not on the canonical PoX fork.
    #[cfg_attr(test, mutants::skip)]
    pub fn get_consensus_hash_height(&self, ch: &ConsensusHash) -> Result<Option<u64>, db_error> {
        let qry = "SELECT block_height FROM snapshots WHERE consensus_hash = ?1";
        let mut heights: Vec<u64> = query_rows(self.conn(), qry, &[ch])?;
        if let Some(height) = heights.pop() {
            for next_height in heights {
                if height != next_height {
                    panic!("BUG: consensus hash {} has two different heights", ch);
                }
            }
            Ok(Some(height))
        } else {
            Ok(None)
        }
    }

    /// Get the schema version of a sortition DB, given the path to it.
    /// Returns the version string, if it exists.
    ///
    /// Does **not** migrate the database (like `open()` or `connect()` would)
    pub fn get_db_version_from_path(path: &str) -> Result<Option<String>, db_error> {
        if fs::metadata(path).is_err() {
            return Err(db_error::NoDBError);
        }
        let index_path = db_mkdirs(path)?;
        let marf = SortitionDB::open_index(&index_path)?;
        SortitionDB::get_schema_version(marf.sqlite_conn())
    }

    /// Get the height of the highest burnchain block, given the DB path.
    /// Importantly, this will *not* apply any schema migrations.
    /// This is used to check if the DB is compatible with the current epoch.
    pub fn get_highest_block_height_from_path(path: &str) -> Result<u64, db_error> {
        if fs::metadata(path).is_err() {
            return Err(db_error::NoDBError);
        }
        let index_path = db_mkdirs(path)?;
        let marf = SortitionDB::open_index(&index_path)?;
        let sql = "SELECT MAX(block_height) FROM snapshots";
        Ok(query_rows(&marf.sqlite_conn(), sql, NO_PARAMS)?
            .pop()
            .expect("BUG: no snapshots in block_snapshots"))
    }

    /// Is a particular database version supported by a given epoch?
    pub fn is_db_version_supported_in_epoch(epoch: StacksEpochId, version: &str) -> bool {
        let version_u32: u32 = version.parse().unwrap_or_else(|e| {
            error!("Failed to parse sortdb version as u32: {e}");
            0
        });
        match epoch {
            StacksEpochId::Epoch10 => true,
            StacksEpochId::Epoch20 => version_u32 >= 1,
            StacksEpochId::Epoch2_05 => version_u32 >= 2,
            StacksEpochId::Epoch21 => version_u32 >= 3,
            StacksEpochId::Epoch22 => version_u32 >= 3,
            StacksEpochId::Epoch23 => version_u32 >= 3,
            StacksEpochId::Epoch24 => version_u32 >= 3,
            StacksEpochId::Epoch25 => version_u32 >= 3,
            StacksEpochId::Epoch30 => version_u32 >= 3,
            StacksEpochId::Epoch31 => version_u32 >= 3,
        }
    }

    /// Get the database schema version, given a DB connection
    fn get_schema_version(conn: &Connection) -> Result<Option<String>, db_error> {
        let version = conn
            .query_row("SELECT MAX(version) from db_config", NO_PARAMS, |row| {
                row.get(0)
            })
            .optional()?;
        Ok(version)
    }

    fn apply_schema_2(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_2 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_insert_epochs(&tx, epochs)?;

        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["2"],
        )?;

        Ok(())
    }

    fn apply_schema_3(tx: &DBTx) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_3 {
            tx.execute_batch(sql_exec)?;
        }
        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["3"],
        )?;
        Ok(())
    }

    fn apply_schema_4(tx: &DBTx) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_4 {
            tx.execute_batch(sql_exec)?;
        }

        let typical_rules = params![(ASTRules::Typical as u8), 0i64];

        let precheck_size_rules = params![
            (ASTRules::PrecheckSize as u8),
            u64_to_sql(AST_RULES_PRECHECK_SIZE)?,
        ];

        tx.execute(
            "INSERT INTO ast_rule_heights (ast_rule_id,block_height) VALUES (?1, ?2)",
            typical_rules,
        )?;
        tx.execute(
            "INSERT INTO ast_rule_heights (ast_rule_id,block_height) VALUES (?1, ?2)",
            precheck_size_rules,
        )?;
        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["4"],
        )?;
        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_5(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        // the schema 5 changes simply **replace** the contents of the epochs table
        //  by dropping all the current rows and then revalidating and inserting
        //  `epochs`
        for sql_exec in SORTITION_DB_SCHEMA_5 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_insert_epochs(&tx, epochs)?;

        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["5"],
        )?;

        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_6(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_6 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_insert_epochs(&tx, epochs)?;

        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["6"],
        )?;

        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_7(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_7 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_insert_epochs(&tx, epochs)?;

        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["7"],
        )?;

        Ok(())
    }

    /// Apply just the table creation/alterations for schema 8.  Don't attempt migration yet.
    fn apply_schema_8_tables(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        if table_exists(tx, "stacks_chain_tips")? {
            info!("Schema 8 tables appear to have been created already; skipping this step");
            return Ok(());
        }

        for sql_exec in SORTITION_DB_SCHEMA_8 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_insert_epochs(&tx, epochs)?;
        Ok(())
    }

    /// When applying schema 8, instantiate the `stacks_chain_tips` table
    /// NOTE: this only works in epochs 2.5 and earlier
    pub(crate) fn apply_schema_8_stacks_chain_tips(
        &mut self,
        canonical_tip: &BlockSnapshot,
    ) -> Result<(), db_error> {
        let first_block_height = self.first_block_height;
        let tx = self.tx_begin()?;

        // skip if this step was done
        if table_exists(&tx, "stacks_chain_tips")? {
            let sql = "SELECT 1 FROM stacks_chain_tips WHERE sortition_id = ?1";
            let args = params![canonical_tip.sortition_id];
            if let Ok(Some(_)) = query_row::<i64, _>(&tx, sql, args) {
                info!("`stacks_chain_tips` appears to have been populated already; skipping this step");
                return Ok(());
            }
        }

        for height in first_block_height..=canonical_tip.block_height {
            let snapshots = SortitionDB::get_all_snapshots_by_burn_height(&tx, height)?;
            debug!(
                "Populate stacks_chain_tips for {} sortition(s) at height {}",
                snapshots.len(),
                height
            );
            for snapshot in snapshots.into_iter() {
                let sql = "INSERT OR REPLACE INTO stacks_chain_tips (sortition_id,consensus_hash,block_hash,block_height) VALUES (?1,?2,?3,?4)";
                let args = params![
                    snapshot.sortition_id,
                    snapshot.canonical_stacks_tip_consensus_hash,
                    snapshot.canonical_stacks_tip_hash,
                    u64_to_sql(snapshot.canonical_stacks_tip_height)?,
                ];
                tx.execute(sql, args)?;
            }
        }
        tx.commit()?;
        Ok(())
    }

    /// When applying schema 8, instantiate the `preprocessed_reward_sets` table
    pub(crate) fn apply_schema_8_preprocessed_reward_sets(
        &mut self,
        canonical_tip: &BlockSnapshot,
        mut migrator: SortitionDBMigrator,
    ) -> Result<(), db_error> {
        let pox_constants = self.pox_constants.clone();
        for rc in 0..=(canonical_tip.block_height / u64::from(pox_constants.reward_cycle_length)) {
            let rc_start = pox_constants.reward_cycle_to_block_height(self.first_block_height, rc);
            if rc_start > canonical_tip.block_height {
                break;
            }
            let epoch_at_height = SortitionDB::get_stacks_epoch(self.conn(), rc_start)?
                .unwrap_or_else(|| panic!("FATAL: no epoch defined for burn height {}", rc_start))
                .epoch_id;

            if epoch_at_height >= StacksEpochId::Epoch30 {
                break;
            }

            info!("Regenerating reward set for cycle {}", &rc);
            migrator.regenerate_reward_cycle_info(self, rc)?;
        }

        Ok(())
    }

    /// Apply schema 8 migration.  Call after `apply_schema_8_tables()`.
    /// This migration path is different from the others in that it manages sortition DB
    /// transactions on its own (namely, it needs access to the SortitionDB MARF).
    ///
    /// To _migrate_ the sortition DB from schema 7, it needs access to the Stacks chainstate in
    /// order to obtain prior reward sets.  This is encapsulated in the `SortitionDBMigrator`
    /// implementation.  However, to _instantiate_ the sortition DB, no migrator is needed (since
    /// the chainstate will also be empty).
    fn apply_schema_8_migration(
        &mut self,
        mut migrator: Option<SortitionDBMigrator>,
    ) -> Result<(), db_error> {
        let canonical_tip = SortitionDB::get_canonical_burn_chain_tip(self.conn())?;

        // port over `stacks_chain_tips` table
        info!("Instantiating `stacks_chain_tips` table...");
        self.apply_schema_8_stacks_chain_tips(&canonical_tip)?;

        // port over `preprocessed_reward_sets` table
        if let Some(migrator) = migrator.take() {
            info!("Instantiating `preprocessed_reward_sets` table...");
            self.apply_schema_8_preprocessed_reward_sets(&canonical_tip, migrator)?;
        } else {
            // NOTE: if we're instantiating the DB, this is fine.
            info!("No migrator implementation given; `preprocessed_reward_sets` will not be prepopulated");
        }

        let tx = self.tx_begin()?;
        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["8"],
        )?;
        tx.commit()?;

        Ok(())
    }

    #[cfg_attr(test, mutants::skip)]
    fn apply_schema_9(tx: &DBTx, epochs: &[StacksEpoch]) -> Result<(), db_error> {
        for sql_exec in SORTITION_DB_SCHEMA_9 {
            tx.execute_batch(sql_exec)?;
        }

        SortitionDB::validate_and_replace_epochs(&tx, epochs)?;

        tx.execute(
            "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
            &["9"],
        )?;

        Ok(())
    }

    fn check_schema_version_or_error(&mut self) -> Result<(), db_error> {
        match SortitionDB::get_schema_version(self.conn()) {
            Ok(Some(version)) => {
                let expected_version = SORTITION_DB_VERSION.to_string();
                if version == expected_version {
                    Ok(())
                } else {
                    let version_u64 = version.parse::<u64>().unwrap();
                    Err(db_error::OldSchema(version_u64))
                }
            }
            Ok(None) => panic!("The schema version of the sortition DB is not recorded."),
            Err(e) => panic!("Error obtaining the version of the sortition DB: {:?}", e),
        }
    }

    /// Migrate the sortition DB to its latest version, given the set of system epochs.
    /// The `migrator` should only be `None` if the DB is being instantiated, or if the DB is
    /// instantiated and migrated to the latest schema.
    /// Otherwise, it should be `Some(..)`.
    fn check_schema_version_and_update(
        &mut self,
        epochs: &[StacksEpoch],
        mut migrator: Option<SortitionDBMigrator>,
    ) -> Result<(), db_error> {
        let expected_version = SORTITION_DB_VERSION.to_string();
        loop {
            match SortitionDB::get_schema_version(self.conn()) {
                Ok(Some(version)) => {
                    if version == "1" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_2(&tx.deref(), epochs)?;
                        tx.commit()?;
                    } else if version == "2" {
                        // add the tables of schema 3, but do not populate them.
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_3(&tx.deref())?;
                        tx.commit()?;
                    } else if version == "3" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_4(&tx.deref())?;
                        tx.commit()?;
                    } else if version == "4" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_5(&tx.deref(), epochs)?;
                        tx.commit()?;
                    } else if version == "5" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_6(&tx.deref(), epochs)?;
                        tx.commit()?;
                    } else if version == "6" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_7(&tx.deref(), epochs)?;
                        tx.commit()?;
                    } else if version == "7" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_8_tables(&tx.deref(), epochs)?;
                        tx.commit()?;

                        self.apply_schema_8_migration(migrator.take())?;
                    } else if version == "8" {
                        let tx = self.tx_begin()?;
                        SortitionDB::apply_schema_9(&tx.deref(), epochs)?;
                        tx.commit()?;
                    } else if version == expected_version {
                        // this transaction is almost never needed
                        let validated_epochs: &[StacksEpoch] =
                            &StacksEpoch::validate_epochs(epochs);
                        let existing_epochs = Self::get_stacks_epochs(self.conn())?;
                        if &existing_epochs == validated_epochs {
                            return Ok(());
                        }

                        // epochs are out of date
                        let tx = self.tx_begin()?;
                        SortitionDB::validate_and_replace_epochs(&tx, epochs)?;
                        tx.commit()?;

                        return Ok(());
                    } else {
                        panic!("The schema version of the sortition DB is invalid.")
                    }
                }
                Ok(None) => panic!("The schema version of the sortition DB is not recorded."),
                Err(e) => panic!("Error obtaining the version of the sortition DB: {:?}", e),
            }
        }
    }

    /// Open and migrate the sortition DB if it exists.
    pub fn migrate_if_exists(
        path: &str,
        epochs: &[StacksEpoch],
        migrator: SortitionDBMigrator,
    ) -> Result<(), db_error> {
        // NOTE: the sortition DB created here will not be used for anything, so it's safe to use
        // the mainnet_default PoX constants
        if let Err(db_error::OldSchema(_)) =
            SortitionDB::open(path, false, PoxConstants::mainnet_default())
        {
            let index_path = db_mkdirs(path)?;
            let marf = SortitionDB::open_index(&index_path)?;
            let mut db = SortitionDB {
                path: path.to_string(),
                marf,
                readwrite: true,
                dryrun: false,
                first_block_height: migrator.get_burnchain().first_block_height,
                first_burn_header_hash: migrator.get_burnchain().first_block_hash.clone(),
                pox_constants: migrator.get_burnchain().pox_constants.clone(),
            };
            db.check_schema_version_and_update(epochs, Some(migrator))
        } else {
            debug!("SortitionDB is at the latest schema");
            Ok(())
        }
    }

    fn add_indexes(&mut self) -> Result<(), db_error> {
        // do we need to instantiate indexes?
        // only do a transaction if we need to, since this gets called each time the sortition DB
        // is opened.
        let exists: i64 = query_row(
            self.conn(),
            "SELECT 1 FROM sqlite_master WHERE type = 'index' AND name = ?1",
            &[LAST_SORTITION_DB_INDEX],
        )?
        .unwrap_or(0);
        if exists == 0 {
            let tx = self.tx_begin()?;
            for row_text in SORTITION_DB_INDEXES {
                tx.execute_batch(row_text)?;
            }
            tx.commit()?;
        }
        Ok(())
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn override_ast_rule_height(
        tx: &mut DBTx<'_>,
        ast_rules: ASTRules,
        height: u64,
    ) -> Result<(), db_error> {
        let rules = params![u64_to_sql(height)?, (ast_rules as u8)];

        tx.execute(
            "UPDATE ast_rule_heights SET block_height = ?1 WHERE ast_rule_id = ?2",
            rules,
        )?;
        Ok(())
    }

    #[cfg(not(any(test, feature = "testing")))]
    pub fn override_ast_rule_height<'a>(
        _tx: &mut DBTx<'a>,
        _ast_rules: ASTRules,
        _height: u64,
    ) -> Result<(), db_error> {
        Ok(())
    }

    /// What's the default AST rules at the given block height?
    pub fn get_ast_rules(conn: &DBConn, height: u64) -> Result<ASTRules, db_error> {
        let ast_rule_sets: Vec<(ASTRules, u64)> = query_rows(
            conn,
            "SELECT * FROM ast_rule_heights ORDER BY block_height ASC",
            NO_PARAMS,
        )?;

        assert!(!ast_rule_sets.is_empty());
        let mut last_height = ast_rule_sets[0].1;
        let mut last_rules = ast_rule_sets[0].0;
        for (ast_rules, ast_rule_height) in ast_rule_sets.into_iter() {
            if last_height <= height && height < ast_rule_height {
                return Ok(last_rules);
            }
            last_height = ast_rule_height;
            last_rules = ast_rules;
        }

        return Ok(last_rules);
    }

    /// Store a pre-processed reward set.
    /// `sortition_id` is the first sortition ID of the prepare phase.
    /// No-op if the reward set has a selected-and-unknown anchor block.
    pub fn store_preprocessed_reward_set(
        sort_tx: &mut DBTx,
        sortition_id: &SortitionId,
        rc_info: &RewardCycleInfo,
    ) -> Result<(), db_error> {
        if !rc_info.is_reward_info_known() {
            return Ok(());
        }
        let sql = "REPLACE INTO preprocessed_reward_sets (sortition_id,reward_set) VALUES (?1,?2)";
        let rc_json = serde_json::to_string(rc_info).map_err(db_error::SerializationError)?;
        let args = params![sortition_id, rc_json];
        sort_tx.execute(sql, args)?;
        Ok(())
    }

    /// Figure out the reward cycle for `tip` and lookup the preprocessed
    /// reward set (if it exists) for the active reward cycle during `tip`.
    /// Returns the reward cycle info on success.
    /// Returns Error on DB errors, as well as if the reward set is not yet processed.
    /// Wrapper around SortitionDBConn::get_preprocessed_reward_set_for_reward_cycle().
    pub fn get_preprocessed_reward_set_for_reward_cycle(
        &self,
        tip: &SortitionId,
        reward_cycle_id: u64,
    ) -> Result<(RewardCycleInfo, SortitionId), db_error> {
        self.index_conn()
            .get_preprocessed_reward_set_for_reward_cycle(
                &self.pox_constants,
                self.first_block_height,
                tip,
                reward_cycle_id,
            )
    }

    /// Figure out the reward cycle for `tip` and lookup the preprocessed
    /// reward set (if it exists) for the active reward cycle during `tip`.
    /// Returns the reward cycle info on success.
    /// Returns Error on DB errors, as well as if the reward set is not yet processed.
    /// Wrapper around SortitionDBConn::get_preprocessed_reward_set_of().
    pub fn get_preprocessed_reward_set_of(
        &self,
        tip: &SortitionId,
    ) -> Result<RewardCycleInfo, db_error> {
        Ok(self.index_conn().get_preprocessed_reward_set_of(
            &self.pox_constants,
            self.first_block_height,
            tip,
        )?)
    }

    /// Get a pre-processed reawrd set.
    /// `sortition_id` is the first sortition ID of the prepare phase.
    pub fn get_preprocessed_reward_set(
        sortdb: &DBConn,
        sortition_id: &SortitionId,
    ) -> Result<Option<RewardCycleInfo>, db_error> {
        let sql = "SELECT reward_set FROM preprocessed_reward_sets WHERE sortition_id = ?1";
        let args = params![sortition_id];
        let reward_set_opt: Option<String> =
            sortdb.query_row(sql, args, |row| row.get(0)).optional()?;

        let rc_info = reward_set_opt
            .map(|reward_set_str| serde_json::from_str(&reward_set_str))
            .transpose()
            .map_err(|_| db_error::ParseError)?;

        Ok(rc_info)
    }

    /// Get the number of entries in the reward set, given a sortition ID within the reward cycle
    /// for which this set is active.
    pub fn get_preprocessed_reward_set_size(&self, tip: &SortitionId) -> Option<u16> {
        let Ok(reward_info) = &self.get_preprocessed_reward_set_of(&tip) else {
            return None;
        };
        let Some(reward_set) = reward_info.known_selected_anchor_block() else {
            return None;
        };

        reward_set
            .signers
            .clone()
            .map(|x| x.len())
            .unwrap_or(0)
            .try_into()
            .ok()
    }

    /// Get the Stacks block ID for the canonical tip.
    pub fn get_canonical_stacks_tip_block_id(&self) -> StacksBlockId {
        let (ch, bh) = SortitionDB::get_canonical_stacks_chain_tip_hash(self.conn()).unwrap();
        StacksBlockId::new(&ch, &bh)
    }
}

impl SortitionDBTx<'_> {
    pub fn find_sortition_tip_affirmation_map(
        &mut self,
        chain_tip: &SortitionId,
    ) -> Result<AffirmationMap, db_error> {
        let affirmation_map = match self.get_indexed(chain_tip, &db_keys::pox_affirmation_map())? {
            Some(am_str) => {
                AffirmationMap::decode(&am_str).expect("FATAL: corrupt affirmation map")
            }
            None => AffirmationMap::empty(),
        };

        // remove the first entry -- it's always `n` based on the way we construct it, while the
        // heaviest affirmation map just has nothing.
        Ok(match affirmation_map.as_slice() {
            [] => AffirmationMap::empty(),
            a => AffirmationMap::new(a[1..].to_vec()),
        })
    }
}

impl SortitionDBConn<'_> {
    pub fn as_handle<'b>(&'b self, chain_tip: &SortitionId) -> SortitionHandleConn<'b> {
        SortitionHandleConn {
            index: self.index,
            context: SortitionHandleContext {
                first_block_height: self.context.first_block_height.clone(),
                chain_tip: chain_tip.clone(),
                pox_constants: self.context.pox_constants.clone(),
                dryrun: self.context.dryrun,
            },
        }
    }

    /// Given a burnchain consensus hash,
    /// go get the last N Stacks block headers that won sortition
    /// leading up to the given header hash.  The ith slot in the vector will be Some(...) if there
    /// was a sortition, and None if not.
    /// Returns up to num_headers prior block header hashes.
    /// The list of hashes will be in ascending order -- the lowest-height block is item 0.
    /// The last hash will be the hash for the given consensus hash.
    pub fn get_stacks_header_hashes(
        &self,
        num_headers: u64,
        tip_consensus_hash: &ConsensusHash,
        cache: &BlockHeaderCache,
    ) -> Result<Vec<(ConsensusHash, Option<BlockHeaderHash>)>, db_error> {
        let mut ret = vec![];
        let tip_snapshot = SortitionDB::get_block_snapshot_consensus(self, tip_consensus_hash)?
            .ok_or_else(|| db_error::NotFoundError)?;

        if !tip_snapshot.pox_valid {
            warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", tip_consensus_hash);
            return Err(db_error::InvalidPoxSortition);
        }

        assert!(
            tip_snapshot.block_height >= self.context.first_block_height,
            "DB corruption: have snapshot with a smaller block height than the first block height"
        );

        let db_handle = self.as_handle(&tip_snapshot.sortition_id);

        let headers_count =
            if tip_snapshot.block_height - self.context.first_block_height < num_headers {
                tip_snapshot.block_height - self.context.first_block_height
            } else {
                num_headers
            };

        let mut ancestor_consensus_hash = tip_snapshot.consensus_hash;

        for _i in 0..headers_count {
            if let Some((header_hash_opt, prev_consensus_hash)) =
                cache.get(&ancestor_consensus_hash)
            {
                // cache hit
                ret.push((ancestor_consensus_hash, header_hash_opt.clone()));
                ancestor_consensus_hash = prev_consensus_hash.clone();
                continue;
            }

            // cache miss
            let ancestor_snapshot = SortitionDB::get_block_snapshot_consensus(
                db_handle.conn(),
                &ancestor_consensus_hash,
            )?
            .unwrap_or_else(|| {
                panic!(
                    "Discontiguous index: missing block for consensus hash {}",
                    ancestor_consensus_hash
                )
            });

            // this can happen if this call is interleaved with a PoX invalidation transaction
            if !ancestor_snapshot.pox_valid {
                warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", ancestor_consensus_hash);
                return Err(db_error::InvalidPoxSortition);
            }

            let header_hash_opt = if ancestor_snapshot.sortition {
                Some(ancestor_snapshot.winning_stacks_block_hash.clone())
            } else {
                None
            };

            debug!(
                "CACHE MISS {} (height {}): {:?}",
                &ancestor_consensus_hash, ancestor_snapshot.block_height, &header_hash_opt
            );

            ret.push((ancestor_snapshot.consensus_hash, header_hash_opt.clone()));

            let ancestor_snapshot_parent = SortitionDB::get_block_snapshot(
                db_handle.conn(),
                &ancestor_snapshot.parent_sortition_id,
            )?
            .unwrap_or_else(|| {
                panic!(
                    "Discontiguous index: missing parent block of parent burn header hash {}",
                    &ancestor_snapshot.parent_burn_header_hash
                )
            });

            ancestor_consensus_hash = ancestor_snapshot_parent.consensus_hash;
        }

        ret.reverse();
        Ok(ret)
    }

    pub fn find_parent_snapshot_for_stacks_block(
        &self,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let db_handle = SortitionHandleConn::open_reader_consensus(self, consensus_hash)?;
        let parent_block_snapshot = match db_handle
            .get_block_snapshot_of_parent_stacks_block(consensus_hash, &block_hash)
        {
            Ok(Some((_, sn))) => {
                debug!(
                    "Parent of {}/{} is {}/{}",
                    consensus_hash, block_hash, sn.consensus_hash, sn.winning_stacks_block_hash
                );
                sn
            }
            Ok(None) => {
                debug!(
                    "Received block with unknown parent snapshot: {}/{}",
                    consensus_hash, block_hash,
                );
                return Ok(None);
            }
            Err(db_error::InvalidPoxSortition) => {
                warn!(
                    "Received block {}/{} on a non-canonical PoX sortition",
                    consensus_hash, block_hash,
                );
                return Ok(None);
            }
            Err(e) => {
                return Err(e);
            }
        };

        Ok(Some(parent_block_snapshot))
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn get_reward_set_size_at(&mut self, sortition_id: &SortitionId) -> Result<u16, db_error> {
        self.get_indexed(sortition_id, &db_keys::pox_reward_set_size())
            .map(|x| {
                db_keys::reward_set_size_from_string(
                    &x.expect("CORRUPTION: no current reward set size written"),
                )
            })
    }

    pub fn get_reward_set_entry_at(
        &mut self,
        sortition_id: &SortitionId,
        entry_ix: u16,
    ) -> Result<PoxAddress, db_error> {
        let entry_str = self
            .get_indexed(sortition_id, &db_keys::pox_reward_set_entry(entry_ix))?
            .unwrap_or_else(|| {
                panic!(
                    "CORRUPTION: expected reward set entry at index={}, but not found",
                    entry_ix
                )
            });
        Ok(PoxAddress::from_db_string(&entry_str).expect("FATAL: could not decode PoX address"))
    }

    pub fn get_reward_set_payouts_at(
        &self,
        sortition_id: &SortitionId,
    ) -> Result<(Vec<PoxAddress>, u128), db_error> {
        let sql = "SELECT pox_payouts FROM snapshots WHERE sortition_id = ?1";
        let args = params![sortition_id];
        let pox_addrs_json: String =
            query_row(self.conn(), sql, args)?.ok_or(db_error::NotFoundError)?;

        let pox_addrs: (Vec<PoxAddress>, u128) =
            serde_json::from_str(&pox_addrs_json).expect("FATAL: failed to decode pox payout JSON");
        Ok(pox_addrs)
    }

    /// Figure out the reward cycle for `tip` and lookup the preprocessed
    /// reward set (if it exists) for the active reward cycle during `tip`.
    /// Returns the reward cycle info on success.
    /// Returns Error on DB errors, as well as if the reward set is not yet processed.
    pub fn get_preprocessed_reward_set_of(
        &self,
        pox_constants: &PoxConstants,
        first_block_height: u64,
        tip: &SortitionId,
    ) -> Result<RewardCycleInfo, db_error> {
        let tip_sn = SortitionDB::get_block_snapshot(self, tip)?.ok_or_else(|| {
            error!(
                "Could not find snapshot for sortition while fetching reward set";
                "tip_sortition_id" => %tip,
            );
            db_error::NotFoundError
        })?;

        let reward_cycle_id = pox_constants
            .block_height_to_reward_cycle(first_block_height, tip_sn.block_height)
            .expect("FATAL: stored snapshot with block height < first_block_height");

        self.get_preprocessed_reward_set_for_reward_cycle(
            pox_constants,
            first_block_height,
            tip,
            reward_cycle_id,
        )
        .map(|(reward_cycle_info, _anchor_sortition_id)| reward_cycle_info)
    }

    /// Get the prepare phase start sortition ID of a reward cycle.  This is the first prepare
    /// phase sortition for the prepare phase that began this reward cycle (i.e. the returned
    /// sortition will be in the preceding reward cycle)
    pub fn get_prepare_phase_start_sortition_id_for_reward_cycle(
        &self,
        pox_constants: &PoxConstants,
        first_block_height: u64,
        tip: &SortitionId,
        reward_cycle_id: u64,
    ) -> Result<SortitionId, db_error> {
        let reward_cycle_of_prepare_phase = reward_cycle_id
            .checked_sub(1)
            .ok_or_else(|| db_error::Other("No prepare phase exists for cycle 0".into()))?;
        let prepare_phase_start =
            pox_constants.prepare_phase_start(first_block_height, reward_cycle_of_prepare_phase);

        let first_sortition =
            get_ancestor_sort_id(self, prepare_phase_start, tip)?.ok_or_else(|| {
                error!(
                    "Could not find prepare phase start ancestor while fetching reward set";
                    "tip_sortition_id" => %tip,
                    "reward_cycle_id" => reward_cycle_id,
                    "prepare_phase_start_height" => prepare_phase_start
                );
                db_error::NotFoundError
            })?;
        Ok(first_sortition)
    }

    /// Get the reward set for a reward cycle, given the reward cycle tip.  The reward cycle info
    /// will be returned for the reward set in which `tip` belongs (i.e. the reward set calculated
    /// in the preceding reward cycle).
    /// Return the reward cycle info for this reward cycle, as well as the first prepare-phase
    /// sortition ID under which this reward cycle info is stored.
    /// Returns Error on DB Error, or if the reward cycle info is not processed yet.
    pub fn get_preprocessed_reward_set_for_reward_cycle(
        &self,
        pox_constants: &PoxConstants,
        first_block_height: u64,
        tip: &SortitionId,
        reward_cycle_id: u64,
    ) -> Result<(RewardCycleInfo, SortitionId), db_error> {
        let first_sortition = self.get_prepare_phase_start_sortition_id_for_reward_cycle(
            pox_constants,
            first_block_height,
            tip,
            reward_cycle_id,
        )?;
        debug!("Fetching preprocessed reward set";
              "tip_sortition_id" => %tip,
              "reward_cycle_id" => reward_cycle_id,
              "prepare_phase_start_sortition_id" => %first_sortition,
        );

        Ok((
            SortitionDB::get_preprocessed_reward_set(self, &first_sortition)?
                .ok_or(db_error::NotFoundError)?,
            first_sortition,
        ))
    }
}

// High-level functions used by ChainsCoordinator
impl SortitionDB {
    pub fn get_sortition_id(
        &self,
        burnchain_header_hash: &BurnchainHeaderHash,
        sortition_tip: &SortitionId,
    ) -> Result<Option<SortitionId>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        handle
            .get_sortition_id_for_bhh(burnchain_header_hash)
            .map_err(BurnchainError::from)
    }

    pub fn is_sortition_processed(
        &self,
        burnchain_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<SortitionId>, BurnchainError> {
        let qry = "SELECT sortition_id FROM snapshots WHERE burn_header_hash = ? AND pox_valid = 1";
        query_row(self.conn(), qry, &[burnchain_header_hash]).map_err(BurnchainError::from)
    }

    fn get_block_height(
        conn: &Connection,
        sortition_id: &SortitionId,
    ) -> Result<Option<u32>, db_error> {
        let qry = "SELECT block_height FROM snapshots WHERE sortition_id = ? LIMIT 1";
        conn.query_row(qry, &[sortition_id], |row| row.get(0))
            .optional()
            .map_err(db_error::from)
    }

    /// Is the given block an expected PoX anchor in this sortition history?
    ///  if so, return the Stacks block hash
    pub fn is_stacks_block_pox_anchor(
        &mut self,
        block: &BlockHeaderHash,
        sortition_tip: &SortitionId,
    ) -> Result<Option<BlockHeaderHash>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        let expects_block_as_anchor = handle
            .get_tip_indexed(&db_keys::pox_anchor_to_prepare_end(block))?
            .map(|_| block.clone());

        return Ok(expects_block_as_anchor);
    }

    fn parse_last_anchor_block_hash(s: Option<String>) -> Option<BlockHeaderHash> {
        s.and_then(|s| {
            if s.is_empty() {
                None
            } else {
                Some(BlockHeaderHash::from_hex(&s).expect("BUG: Bad BlockHeaderHash stored in DB"))
            }
        })
    }

    fn parse_last_anchor_block_txid(s: Option<String>) -> Option<Txid> {
        s.and_then(|s| {
            if s.is_empty() {
                None
            } else {
                Some(Txid::from_hex(&s).expect("BUG: Bad Txid stored in DB"))
            }
        })
    }

    /// Mark a Stacks block snapshot as valid again, but update its memoized canonical Stacks tip
    /// height and block-accepted flag.
    #[cfg_attr(test, mutants::skip)]
    pub fn revalidate_snapshot_with_block(
        tx: &DBTx,
        sortition_id: &SortitionId,
        canonical_stacks_ch: &ConsensusHash,
        canonical_stacks_bhh: &BlockHeaderHash,
        canonical_stacks_height: u64,
        stacks_block_accepted: Option<bool>,
    ) -> Result<(), BurnchainError> {
        if let Some(stacks_block_accepted) = stacks_block_accepted {
            let args = params![
                sortition_id,
                u64_to_sql(canonical_stacks_height)?,
                canonical_stacks_bhh,
                canonical_stacks_ch,
                stacks_block_accepted,
            ];
            tx.execute(
                "UPDATE snapshots SET pox_valid = 1, canonical_stacks_tip_height = ?2, canonical_stacks_tip_hash = ?3, canonical_stacks_tip_consensus_hash = ?4, stacks_block_accepted = ?5 WHERE sortition_id = ?1",
                args
            )?;
        } else {
            let args = params![
                sortition_id,
                u64_to_sql(canonical_stacks_height)?,
                canonical_stacks_bhh,
                canonical_stacks_ch,
            ];
            tx.execute(
                "UPDATE snapshots SET pox_valid = 1, canonical_stacks_tip_height = ?2, canonical_stacks_tip_hash = ?3, canonical_stacks_tip_consensus_hash = ?4 WHERE sortition_id = ?1",
                args
            )?;
        }
        Ok(())
    }

    /// Invalidate all block snapshots that descend from the given burnchain block, and for each
    /// invalidated snapshot, apply `cls` to it with the given sortition DB transaction, the
    /// current burnchain block being considered, and the list of burnchain blocks still to be
    /// considered.  That last argument will have length 0 on the last call to `cls`.
    ///
    /// Run `after` with the sorition handle tx right before committing.
    pub fn invalidate_descendants_with_closures<F, G>(
        &mut self,
        burn_block: &BurnchainHeaderHash,
        mut cls: F,
        mut after: G,
    ) -> Result<(), BurnchainError>
    where
        F: FnMut(&mut SortitionDBTx, &BurnchainHeaderHash, &[BurnchainHeaderHash]),
        G: FnMut(&mut SortitionDBTx),
    {
        let mut db_tx = self.tx_begin()?;
        let mut queue = vec![burn_block.clone()];

        while let Some(header) = queue.pop() {
            {
                // scope this to keep the borrow-checker happy
                let mut stmt = db_tx.prepare(
                    "SELECT DISTINCT burn_header_hash FROM snapshots WHERE parent_burn_header_hash = ?",
                )?;
                for next_header in stmt.query_map(&[&header], |row| row.get(0))? {
                    queue.push(next_header?);
                }
            }
            cls(&mut db_tx, &header, &queue);

            debug!("Invalidate descendants of burn block {}", &header);

            #[cfg(any(test, feature = "testing"))]
            {
                let to_invalidate: Vec<BlockSnapshot> = query_rows(
                    &db_tx,
                    "SELECT * FROM snapshots WHERE parent_burn_header_hash = ?1",
                    &[&header],
                )?;
                for invalid in to_invalidate {
                    debug!("Invalidate child of {}: {:?}", &header, &invalid);
                }
            }

            db_tx.tx().execute(
                r#"UPDATE snapshots SET
                pox_valid = 0,
                arrival_index = 0,
                canonical_stacks_tip_height = 0,
                canonical_stacks_tip_hash = "0000000000000000000000000000000000000000000000000000000000000000",
                canonical_stacks_tip_consensus_hash = "0000000000000000000000000000000000000000",
                stacks_block_accepted = 0
                WHERE parent_burn_header_hash = ?"#,
                &[&header],
            )?;
        }

        after(&mut db_tx);

        db_tx.commit()?;
        Ok(())
    }

    pub fn invalidate_descendants_of(
        &mut self,
        burn_block: &BurnchainHeaderHash,
    ) -> Result<(), BurnchainError> {
        self.invalidate_descendants_with_closures(burn_block, |_tx, _bhh, _queue| {}, |_tx| {})
    }

    /// Find all sortition IDs with memoized canonical stacks block pointers that are higher than the
    /// given height.  This is used to identify "dirty" but still valid snapshots whose memoized
    /// pointers are no longer valid.
    pub fn find_snapshots_with_dirty_canonical_block_pointers(
        conn: &DBConn,
        canonical_stacks_height: u64,
    ) -> Result<Vec<SortitionId>, db_error> {
        let dirty_sortitions : Vec<SortitionId> = query_rows(conn, "SELECT sortition_id FROM snapshots WHERE canonical_stacks_tip_height > ?1 AND pox_valid = 1", &[&u64_to_sql(canonical_stacks_height)?])?;
        Ok(dirty_sortitions)
    }

    /// Get the last sortition in the prepare phase that chose a particular Stacks block as the anchor,
    ///   or if the anchor is not expected, return None
    pub fn get_prepare_end_for(
        &mut self,
        sortition_tip: &SortitionId,
        anchor: &BlockHeaderHash,
    ) -> Result<Option<BlockSnapshot>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        let prepare_end_sortid = match handle
            .get_tip_indexed(&db_keys::pox_anchor_to_prepare_end(anchor))?
        {
            Some(s) => SortitionId::from_hex(&s).expect("CORRUPTION: DB stored bad sortition ID"),
            None => return Ok(None),
        };
        let snapshot =
            SortitionDB::get_block_snapshot(self.conn(), &prepare_end_sortid)?.unwrap_or_else(|| panic!("BUG: Sortition ID for prepare phase end is known, but no BlockSnapshot is stored: {}",
            &prepare_end_sortid));
        Ok(Some(snapshot))
    }

    /// Get the PoX ID at the particular sortition_tip
    pub fn get_pox_id(&mut self, sortition_tip: &SortitionId) -> Result<PoxId, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        handle.get_pox_id().map_err(BurnchainError::from)
    }

    pub fn get_sortition_result(
        &self,
        id: &SortitionId,
    ) -> Result<Option<(BlockSnapshot, BurnchainStateTransitionOps)>, BurnchainError> {
        let snapshot = match SortitionDB::get_block_snapshot(self.conn(), id)? {
            Some(x) => x,
            None => return Ok(None),
        };

        let sql_transition_ops = "SELECT accepted_ops, consumed_keys FROM snapshot_transition_ops WHERE sortition_id = ?";
        let transition_ops = self
            .conn()
            .query_row(sql_transition_ops, &[id], |row| {
                let accepted_ops: String = row.get_unwrap(0);
                let consumed_leader_keys: String = row.get_unwrap(1);
                Ok(BurnchainStateTransitionOps {
                    accepted_ops: serde_json::from_str(&accepted_ops)
                        .expect("CORRUPTION: DB stored bad transition ops"),
                    consumed_leader_keys: serde_json::from_str(&consumed_leader_keys)
                        .expect("CORRUPTION: DB stored bad transition ops"),
                })
            })
            .optional()?
            .expect("CORRUPTION: DB stored BlockSnapshot, but not the transition ops");

        Ok(Some((snapshot, transition_ops)))
    }

    /// Compute the next PoX ID
    pub fn make_next_pox_id(parent_pox: PoxId, next_pox_info: Option<&RewardCycleInfo>) -> PoxId {
        let mut next_pox = parent_pox;
        if let Some(ref next_pox_info) = next_pox_info {
            if next_pox_info.is_reward_info_known() {
                info!(
                    "Begin reward-cycle sortition with present anchor block={:?}",
                    &next_pox_info.selected_anchor_block(),
                );
                next_pox.extend_with_present_block();
            } else {
                info!(
                    "Begin reward-cycle sortition with absent anchor block={:?}",
                    &next_pox_info.selected_anchor_block(),
                );
                next_pox.extend_with_not_present_block();
            }
        };
        next_pox
    }

    /// Calculate the next sortition ID, given the PoX ID so far and the reward info
    pub fn make_next_sortition_id(
        parent_pox: PoxId,
        this_block_hash: &BurnchainHeaderHash,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> SortitionId {
        let next_pox = Self::make_next_pox_id(parent_pox, next_pox_info);
        let next_sortition_id = SortitionId::new(this_block_hash, &next_pox);
        next_sortition_id
    }

    /// Evaluate the sortition (SIP-001 miner block election) in the burnchain block defined by
    /// `burn_header`. Returns the new snapshot and burnchain state
    /// transition.
    ///
    /// # Arguments
    /// * `burn_header` - the burnchain block header to process sortition for
    /// * `ops` - the parsed blockstack operations (will be validated in this function)
    /// * `burnchain` - a reference to the burnchain information struct
    /// * `from_tip` - tip of the "sortition chain" that is being built on
    /// * `next_pox_info` - iff this sortition is the first block in a reward cycle, this should be Some
    /// * `announce_to` - a function that will be invoked with the calculated reward set before this method
    ///                   commits its results. This is used to post the calculated reward set to an event observer.
    pub fn evaluate_sortition<F: FnOnce(Option<RewardSetInfo>, ConsensusHash)>(
        &mut self,
        mainnet: bool,
        burn_header: &BurnchainBlockHeader,
        ops: Vec<BlockstackOperationType>,
        burnchain: &Burnchain,
        from_tip: &SortitionId,
        next_pox_info: Option<RewardCycleInfo>,
        announce_to: F,
    ) -> Result<(BlockSnapshot, BurnchainStateTransition), BurnchainError> {
        let dryrun = self.dryrun;
        let parent_sort_id = self
            .get_sortition_id(&burn_header.parent_block_hash, from_tip)?
            .ok_or_else(|| {
                warn!("Unknown block {:?}", burn_header.parent_block_hash);
                BurnchainError::MissingParentBlock
            })?;

        let cur_epoch = SortitionDB::get_stacks_epoch(self.conn(), burn_header.block_height)?
            .unwrap_or_else(|| {
                panic!(
                    "FATAL: no epoch defined for burn height {}",
                    burn_header.block_height
                )
            });

        let mut sortition_db_handle = SortitionHandleTx::begin(self, &parent_sort_id)?;
        let parent_snapshot = sortition_db_handle
            .get_block_snapshot(&burn_header.parent_block_hash, &parent_sort_id)?
            .ok_or_else(|| {
                warn!("Unknown block {:?}", burn_header.parent_block_hash);
                BurnchainError::MissingParentBlock
            })?;

        let parent_pox = sortition_db_handle.get_pox_id()?;
        test_debug!(
            "parent PoX ID of {:?} off of {} is {}",
            &burn_header.parent_block_hash,
            &from_tip,
            &parent_pox
        );

        let reward_set_vrf_hash = parent_snapshot
            .sortition_hash
            .mix_burn_header(&parent_snapshot.burn_header_hash);

        let reward_set_info = if burnchain
            .pox_constants
            .is_after_pox_sunset_end(burn_header.block_height, cur_epoch.epoch_id)
        {
            test_debug!(
                "No recipients for burn height {}: epoch = {}, sunset_end = {}",
                burnchain.pox_constants.sunset_end,
                cur_epoch.epoch_id,
                burn_header.block_height
            );
            None
        } else {
            sortition_db_handle.pick_recipients(
                burnchain,
                burn_header.block_height,
                &reward_set_vrf_hash,
                next_pox_info.as_ref(),
            )?
        };

        // Get any initial mining bonus which would be due to the winner of this block.
        let bonus_remaining =
            sortition_db_handle.get_initial_mining_bonus_remaining(&parent_sort_id)?;

        let initial_mining_bonus = if bonus_remaining > 0 {
            let mining_bonus_per_block = sortition_db_handle
                .get_initial_mining_bonus_per_block(&parent_sort_id)?
                .expect("BUG: initial mining bonus amount written, but not the per block amount.");
            cmp::min(bonus_remaining, mining_bonus_per_block)
        } else {
            0
        };

        let new_snapshot = sortition_db_handle.process_block_txs(
            mainnet,
            &parent_snapshot,
            burn_header,
            burnchain,
            ops,
            next_pox_info,
            parent_pox,
            reward_set_info.as_ref(),
            initial_mining_bonus,
        )?;

        if !dryrun {
            sortition_db_handle
                .store_transition_ops(&new_snapshot.0.sortition_id, &new_snapshot.1)?;
        }

        announce_to(reward_set_info, new_snapshot.0.consensus_hash);

        if !dryrun {
            // commit everything!
            sortition_db_handle.commit().expect(
                "Failed to commit to sortition db after announcing reward set info, state corrupted.",
            );
        }
        Ok((new_snapshot.0, new_snapshot.1))
    }

    pub fn get_next_block_recipients(
        &mut self,
        burnchain: &Burnchain,
        parent_snapshot: &BlockSnapshot,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<RewardSetInfo>, BurnchainError> {
        let reward_set_vrf_hash = parent_snapshot
            .sortition_hash
            .mix_burn_header(&parent_snapshot.burn_header_hash);

        let cur_epoch =
            SortitionDB::get_stacks_epoch(self.conn(), parent_snapshot.block_height + 1)?
                .unwrap_or_else(|| {
                    panic!(
                        "FATAL: no epoch defined for burn height {}",
                        parent_snapshot.block_height + 1
                    )
                });

        let mut sortition_db_handle =
            SortitionHandleTx::begin(self, &parent_snapshot.sortition_id)?;
        if cur_epoch.epoch_id < StacksEpochId::Epoch21
            && parent_snapshot.block_height + 1 >= burnchain.pox_constants.sunset_end
        {
            Ok(None)
        } else {
            sortition_db_handle.pick_recipients(
                burnchain,
                parent_snapshot.block_height + 1,
                &reward_set_vrf_hash,
                next_pox_info,
            )
        }
    }

    pub fn is_stacks_block_in_sortition_set(
        &self,
        sortition_id: &SortitionId,
        block_to_check: &BlockHeaderHash,
    ) -> Result<bool, BurnchainError> {
        let result = self
            .index_handle(sortition_id)
            .get_tip_indexed(&db_keys::stacks_block_present(block_to_check))?;
        Ok(result.is_some())
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn latest_stacks_blocks_processed(
        &self,
        sortition_id: &SortitionId,
    ) -> Result<u64, BurnchainError> {
        let db_handle = self.index_handle(sortition_id);
        SortitionDB::get_max_arrival_index(&db_handle).map_err(BurnchainError::from)
    }

    /// Get a burn blockchain snapshot, given a burnchain configuration struct.
    /// Used mainly by the network code to determine what the chain tip currently looks like.
    pub fn get_burnchain_view(
        conn: &SortitionDBConn,
        burnchain: &Burnchain,
        chain_tip: &BlockSnapshot,
    ) -> Result<BurnchainView, db_error> {
        if chain_tip.block_height < burnchain.first_block_height {
            // should never happen, but don't panic since this is network-callable code
            error!(
                "Invalid block height from DB: {}: expected at least {}",
                chain_tip.block_height, burnchain.first_block_height
            );
            return Err(db_error::Corruption);
        }

        if chain_tip.block_height < burnchain.stable_confirmations as u64 {
            // should never happen, but don't panic since this is network-callable code
            error!(
                "Invalid block height from DB: {}: expected at least {}",
                chain_tip.block_height, burnchain.stable_confirmations
            );
            return Err(db_error::Corruption);
        }

        let stable_block_height = cmp::max(
            burnchain.first_block_height,
            chain_tip.block_height - (burnchain.stable_confirmations as u64),
        );

        // get all burn block hashes between the chain tip, and the stable height back
        // MAX_NEIGHBOR_BLOCK_DELAY
        let oldest_height = if stable_block_height < MAX_NEIGHBOR_BLOCK_DELAY {
            0
        } else {
            stable_block_height - MAX_NEIGHBOR_BLOCK_DELAY
        };

        let mut last_burn_block_hashes = HashMap::new();
        let tip_height = chain_tip.block_height;

        let mut cursor = chain_tip.clone();
        let mut cur_height = cursor.block_height;

        for _height in oldest_height..(tip_height + 1) {
            let (ancestor_hash, ancestor_height) =
                if cursor.block_height > burnchain.first_block_height {
                    match SortitionDB::get_block_snapshot(conn, &cursor.parent_sortition_id) {
                        Ok(Some(new_cursor)) => {
                            let ret = (cursor.burn_header_hash.clone(), cursor.block_height);

                            cursor = new_cursor;
                            assert_eq!(cursor.block_height + 1, cur_height);

                            cur_height = cursor.block_height;
                            ret
                        }
                        _ => {
                            cur_height = cur_height.saturating_sub(1);
                            (burnchain.first_block_hash.clone(), cur_height)
                        }
                    }
                } else {
                    cur_height = cur_height.saturating_sub(1);
                    (burnchain.first_block_hash.clone(), cur_height)
                };

            last_burn_block_hashes.insert(ancestor_height, ancestor_hash);
        }

        let burn_stable_block_hash = last_burn_block_hashes
            .get(&stable_block_height)
            .unwrap_or(&burnchain.first_block_hash)
            .clone();

        test_debug!(
            "Chain view: {},{}-{},{},{}",
            chain_tip.block_height,
            chain_tip.burn_header_hash,
            stable_block_height,
            &burn_stable_block_hash,
            &chain_tip.canonical_stacks_tip_consensus_hash,
        );
        Ok(BurnchainView {
            burn_block_height: chain_tip.block_height,
            burn_block_hash: chain_tip.burn_header_hash,
            burn_stable_block_height: stable_block_height,
            burn_stable_block_hash,
            last_burn_block_hashes,
            rc_consensus_hash: chain_tip.canonical_stacks_tip_consensus_hash,
        })
    }
}

// Querying methods
impl SortitionDB {
    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_canonical_burn_chain_tip(conn: &Connection) -> Result<BlockSnapshot, db_error> {
        let qry = "SELECT * FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        query_row(conn, qry, NO_PARAMS)
            .map(|opt| opt.expect("CORRUPTION: No canonical burnchain tip"))
    }

    /// Get the highest burn chain tip even if it's not PoX-valid.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_highest_known_burn_chain_tip(conn: &Connection) -> Result<BlockSnapshot, db_error> {
        let qry =
            "SELECT * FROM snapshots ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        query_row(conn, qry, NO_PARAMS).map(|opt| opt.expect("CORRUPTION: No burnchain tips"))
    }

    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_canonical_chain_tip_bhh(conn: &Connection) -> Result<BurnchainHeaderHash, db_error> {
        let qry = "SELECT burn_header_hash FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        match conn.query_row(qry, NO_PARAMS, |row| row.get(0)).optional() {
            Ok(opt) => Ok(opt.expect("CORRUPTION: No canonical burnchain tip")),
            Err(e) => Err(db_error::from(e)),
        }
    }

    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    ///
    /// Returns Err if the underlying SQLite call fails.
    pub fn get_canonical_sortition_tip(conn: &Connection) -> Result<SortitionId, db_error> {
        let qry = "SELECT sortition_id FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        match conn.query_row(qry, NO_PARAMS, |row| row.get(0)).optional() {
            Ok(opt) => Ok(opt.expect("CORRUPTION: No canonical burnchain tip")),
            Err(e) => Err(db_error::from(e)),
        }
    }

    /// Find the affirmation map represented by a given sortition ID.
    pub fn find_sortition_tip_affirmation_map(
        &self,
        tip_id: &SortitionId,
    ) -> Result<AffirmationMap, db_error> {
        let ih = self.index_handle(tip_id);
        let am = ih.get_sortition_affirmation_map()?;

        // remove the first entry -- it's always `n` based on the way we construct it, while the
        // heaviest affirmation map just has nothing.
        if am.is_empty() {
            Ok(AffirmationMap::empty())
        } else {
            Ok(AffirmationMap::new(am.as_slice()[1..].to_vec()))
        }
    }

    /// Get the list of Stack-STX operations processed in a given burnchain block.
    /// This will be the same list in each PoX fork; it's up to the Stacks block-processing logic
    /// to reject them.
    pub fn get_stack_stx_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<StackStxOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM stack_stx WHERE burn_header_hash = ? ORDER BY vtxindex",
            &[burn_header_hash],
        )
    }

    /// Get the list of Delegate-STX operations processed in a given burnchain block.
    /// This will be the same list in each PoX fork; it's up to the Stacks block-processing logic
    /// to reject them.
    pub fn get_delegate_stx_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<DelegateStxOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM delegate_stx WHERE burn_header_hash = ? ORDER BY vtxindex",
            &[burn_header_hash],
        )
    }

    /// Get the list of `vote-for-aggregate-key` operations processed in a given burnchain block.
    /// This will be the same list in each PoX fork; it's up to the Stacks block-processing logic
    /// to reject them.
    pub fn get_vote_for_aggregate_key_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<VoteForAggregateKeyOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM vote_for_aggregate_key WHERE burn_header_hash = ? ORDER BY vtxindex",
            &[burn_header_hash],
        )
    }

    /// Get the list of Transfer-STX operations processed in a given burnchain block.
    /// This will be the same list in each PoX fork; it's up to the Stacks block-processing logic
    /// to reject them.
    pub fn get_transfer_stx_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<TransferStxOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM transfer_stx WHERE burn_header_hash = ? ORDER BY vtxindex",
            &[burn_header_hash],
        )
    }

    /// Get the parent burnchain header hash of a given burnchain header hash
    fn get_parent_burnchain_header_hash(
        conn: &Connection,
        burnchain_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<BurnchainHeaderHash>, db_error> {
        let sql = "SELECT parent_burn_header_hash AS burn_header_hash FROM snapshots WHERE burn_header_hash = ?1";
        let args = params![burnchain_header_hash];
        let mut rows = query_rows::<BurnchainHeaderHash, _>(conn, sql, args)?;

        // there can be more than one if there was a PoX reorg.  If so, make sure they're _all the
        // same_ (otherwise we have corruption and must panic)
        if let Some(bhh) = rows.pop() {
            for row in rows.into_iter() {
                if row != bhh {
                    panic!(
                        "FATAL: burnchain header hash {} has two parents: {} and {}",
                        burnchain_header_hash, &bhh, &row
                    );
                }
            }
            Ok(Some(bhh))
        } else {
            Ok(None)
        }
    }

    /// Get the last N ancestor burnchain header hashes, given a burnchain header hash.
    /// This is done without regards to PoX forks.
    ///
    /// The returned list will be formatted as follows:
    ///
    /// * burn_header_hash
    /// * 1st ancestor of burn_header_hash
    /// * 2nd ancestor of burn_header_hash
    /// ...
    /// * Nth ancestor of burn_header_hash
    ///
    /// That is, the resulting list will have up to N+1 items.
    ///
    /// If an ancestor is not found, then return early.
    /// The returned list always starts with `burn_header_hash`.
    pub fn get_ancestor_burnchain_header_hashes(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
        count: u64,
    ) -> Result<Vec<BurnchainHeaderHash>, db_error> {
        let mut ret = vec![burn_header_hash.clone()];
        for _i in 0..count {
            let parent_bhh = match SortitionDB::get_parent_burnchain_header_hash(
                conn,
                ret.last().expect("FATAL: empty burn header hash list"),
            )? {
                Some(bhh) => bhh,
                None => {
                    break;
                }
            };
            ret.push(parent_bhh);
        }
        Ok(ret)
    }

    /// DO NOT CALL during Stacks block processing (including during Clarity VM evaluation). This function returns the latest data known to the node, which may not have been at the time of original block assembly.
    pub fn index_handle_at_tip(&self) -> SortitionHandleConn<'_> {
        let sortition_id = SortitionDB::get_canonical_sortition_tip(self.conn()).unwrap();
        self.index_handle(&sortition_id)
    }

    /// Open an index handle at the given consensus hash
    /// Returns a db_error::NotFoundError if `ch` cannot be found
    pub fn index_handle_at_ch<'a>(
        &'a self,
        ch: &ConsensusHash,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        let sortition_id = Self::get_sortition_id_by_consensus(self.conn(), ch)?
            .ok_or_else(|| db_error::NotFoundError)?;
        Ok(self.index_handle(&sortition_id))
    }

    /// Open a tx handle at the burn chain tip
    /// DO NOT CALL during Stacks block processing (including during Clarity VM evaluation). This function returns the latest data known to the node, which may not have been at the time of original block assembly.
    pub fn tx_begin_at_tip(&mut self) -> SortitionHandleTx<'_> {
        let sortition_id = SortitionDB::get_canonical_sortition_tip(self.conn()).unwrap();
        self.tx_handle_begin(&sortition_id).unwrap()
    }

    /// Given a starting sortition ID, go and find the canonical Nakamoto tip
    /// Returns Ok(Some(tip info)) on success
    /// Returns Ok(None) if there are no Nakamoto blocks in this tip
    /// Returns Err(..) on other DB error
    /// DO NOT CALL during Stacks block processing (including during Clarity VM evaluation). This function returns the latest data known to the node, which may not have been at the time of original block assembly.
    pub fn get_canonical_nakamoto_tip_hash_and_height(
        conn: &Connection,
        tip: &BlockSnapshot,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, u64)>, db_error> {
        let mut cursor = tip.clone();
        loop {
            let result_at_tip : Option<(ConsensusHash, BlockHeaderHash, u64)> = conn.query_row_and_then(
                "SELECT consensus_hash,block_hash,block_height FROM stacks_chain_tips WHERE sortition_id = ? ORDER BY block_height DESC LIMIT 1",
                &[&cursor.sortition_id],
                |row| Ok((row.get_unwrap(0), row.get_unwrap(1), (u64::try_from(row.get_unwrap::<_, i64>(2)).expect("FATAL: block height too high"))))
            ).optional()?;
            if let Some(stacks_tip) = result_at_tip {
                return Ok(Some(stacks_tip));
            }
            let Some(next_cursor) =
                SortitionDB::get_block_snapshot(conn, &cursor.parent_sortition_id)?
            else {
                return Ok(None);
            };
            cursor = next_cursor
        }
    }

    /// Get the canonical Stacks chain tip -- this gets memoized on the canonical burn chain tip.
    /// DO NOT CALL during Stacks block processing (including during Clarity VM evaluation). This function returns the latest data known to the node, which may not have been at the time of original block assembly.
    pub fn get_canonical_stacks_chain_tip_hash_and_height(
        conn: &Connection,
    ) -> Result<(ConsensusHash, BlockHeaderHash, u64), db_error> {
        let sn = SortitionDB::get_canonical_burn_chain_tip(conn)?;
        let cur_epoch =
            SortitionDB::get_stacks_epoch(conn, sn.block_height)?.unwrap_or_else(|| {
                panic!(
                    "FATAL: no epoch defined for burn height {}",
                    sn.block_height
                )
            });

        if cur_epoch.epoch_id >= StacksEpochId::Epoch30 {
            // nakamoto behavior -- look to the stacks_chain_tip table
            //  if the chain tip of the current sortition hasn't been set, have to iterate to parent
            return Self::get_canonical_nakamoto_tip_hash_and_height(conn, &sn)?
                .ok_or(db_error::NotFoundError);
        }

        // epoch 2.x behavior -- look at the snapshot itself
        let stacks_block_hash = sn.canonical_stacks_tip_hash;
        let consensus_hash = sn.canonical_stacks_tip_consensus_hash;
        let stacks_block_height = sn.canonical_stacks_tip_height;
        Ok((consensus_hash, stacks_block_hash, stacks_block_height))
    }

    /// Get the canonical Stacks chain tip -- this gets memoized on the canonical burn chain tip.
    /// DO NOT CALL during Stacks block processing (including during Clarity VM evaluation). This function returns the latest data known to the node, which may not have been at the time of original block assembly.
    pub fn get_canonical_stacks_chain_tip_hash(
        conn: &Connection,
    ) -> Result<(ConsensusHash, BlockHeaderHash), db_error> {
        Self::get_canonical_stacks_chain_tip_hash_and_height(conn)
            .map(|(ch, bhh, _height)| (ch, bhh))
    }

    /// Get the maximum arrival index for any known snapshot.
    fn get_max_arrival_index(conn: &Connection) -> Result<u64, db_error> {
        match conn
            .query_row(
                "SELECT IFNULL(MAX(arrival_index), 1) FROM snapshots",
                NO_PARAMS,
                |row| Ok(u64::from_row(row).expect("Expected u64 in database")),
            )
            .optional()?
        {
            Some(arrival_index) => Ok(if arrival_index == 0 { 1 } else { arrival_index }),
            None => Ok(1),
        }
    }

    /// Get a snapshot with an arrived block (i.e. a block that was marked as processed)
    fn get_snapshot_by_arrival_index(
        conn: &Connection,
        arrival_index: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        query_row_panic(
            conn,
            "SELECT * FROM snapshots WHERE arrival_index = ?1 AND stacks_block_accepted > 0 AND pox_valid = 1",
            &[&u64_to_sql(arrival_index)?],
            || "BUG: multiple snapshots have the same non-zero arrival index".to_string(),
        )
    }

    pub fn get_burnchain_header_hash_by_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<BurnchainHeaderHash>, db_error> {
        let qry = "SELECT burn_header_hash FROM snapshots WHERE consensus_hash = ?1 AND pox_valid = 1 LIMIT 1";
        let args = [&consensus_hash];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })
    }

    pub fn get_sortition_id_by_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<SortitionId>, db_error> {
        let qry = "SELECT sortition_id FROM snapshots WHERE consensus_hash = ?1 AND pox_valid = 1 LIMIT 1";
        let args = [&consensus_hash];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })
    }

    /// Get a snapshot for an existing burn chain block given its consensus hash.
    /// The snapshot may not be valid.
    pub fn get_block_snapshot_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE consensus_hash = ?1";
        let args = [&consensus_hash];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })
    }

    /// Determine if a burnchain block has been processed
    pub fn has_block_snapshot_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, db_error> {
        let qry = "SELECT 1 FROM snapshots WHERE consensus_hash = ?1";
        let args = [&consensus_hash];
        let res: Option<i64> = query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })?;
        Ok(res.is_some())
    }

    /// Get a snapshot for an processed sortition.
    /// The snapshot may not be valid
    pub fn get_block_snapshot(
        conn: &Connection,
        sortition_id: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE sortition_id = ?1";
        let args = [&sortition_id];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block {}",
                sortition_id
            )
        })
        .map(|x| {
            if x.is_none() {
                test_debug!("No snapshot with sortition ID {}", sortition_id);
            }
            x
        })
    }

    /// Get the first snapshot
    pub fn get_first_block_snapshot(conn: &Connection) -> Result<BlockSnapshot, db_error> {
        let qry = "SELECT * FROM snapshots WHERE consensus_hash = ?1";
        let result = query_row_panic(conn, qry, &[&ConsensusHash::empty()], || {
            "FATAL: multiple first-block snapshots".into()
        })?;
        match result {
            None => {
                // should never happen
                panic!("FATAL: no first snapshot");
            }
            Some(snapshot) => Ok(snapshot),
        }
    }

    /// Get the first-ever block height and hash
    pub(crate) fn get_first_block_height_and_hash(
        conn: &Connection,
    ) -> Result<(u64, BurnchainHeaderHash), db_error> {
        let sql = "SELECT block_height, burn_header_hash FROM snapshots WHERE consensus_hash = ?1";
        let args = params![ConsensusHash::empty()];
        let mut stmt = conn.prepare(sql)?;
        let mut rows = stmt.query(args)?;
        while let Some(row) = rows.next()? {
            let height_i64: i64 = row.get("block_height")?;
            let hash: BurnchainHeaderHash = row.get("burn_header_hash")?;
            let height = u64::try_from(height_i64).map_err(|_| {
                warn!("Height does not fit into a u64");
                db_error::ParseError
            })?;
            return Ok((height, hash));
        }
        // NOTE: shouldn't be reachable because we instantiate with a first snapshot
        return Err(db_error::NotFoundError);
    }

    pub fn is_pox_active(
        &self,
        burnchain: &Burnchain,
        block: &BlockSnapshot,
    ) -> Result<bool, db_error> {
        let mut reward_start_height = burnchain.reward_cycle_to_block_height(
            burnchain
                .block_height_to_reward_cycle(block.block_height)
                .ok_or_else(|| {
                    warn!(
                        "block height {} does not have a reward cycle",
                        block.block_height
                    );
                    db_error::NotFoundError
                })?,
        );

        // N.B. the reward cycle start height is 1 + (reward_cycle_number * reward_cycle_length),
        // which can be bigger than block.block_height. If this is true, then we really meant the
        // last reward cycle
        if reward_start_height > block.block_height && block.block_height > 0 {
            reward_start_height = burnchain.reward_cycle_to_block_height(
                burnchain
                    .block_height_to_reward_cycle(block.block_height - 1)
                    .ok_or_else(|| {
                        warn!(
                            "block height {} does not have a reward cycle",
                            block.block_height - 1
                        );
                        db_error::NotFoundError
                    })?,
            );
        }

        let sort_id_of_start =
            get_ancestor_sort_id(&self.index_conn(), reward_start_height, &block.sortition_id)?
                .ok_or_else(|| {
                    warn!(
                "reward start height {} (from block height {}) does not have a sortition from {}",
                reward_start_height, block.block_height, &block.sortition_id
            );
                    db_error::NotFoundError
                })?;

        let handle = self.index_handle(&sort_id_of_start);
        Ok(handle.get_reward_set_size_at(&sort_id_of_start)? > 0)
    }

    /// Find out how any burn tokens were destroyed in a given block on a given fork.
    pub fn get_block_burn_amount(
        conn: &Connection,
        block_snapshot: &BlockSnapshot,
    ) -> Result<u64, db_error> {
        let block_commits =
            SortitionDB::get_block_commits_by_block(conn, &block_snapshot.sortition_id)?;
        let mut burn_total: u64 = 0;

        for i in 0..block_commits.len() {
            burn_total = burn_total
                .checked_add(block_commits[i].burn_fee)
                .expect("Way too many tokens burned");
        }
        Ok(burn_total)
    }

    /// Get all block commitments registered in a block on the burn chain's history in this fork.
    /// Returns the list of block commits in order by vtxindex.
    pub fn get_block_commits_by_block(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<LeaderBlockCommitOp>, db_error> {
        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 ORDER BY vtxindex ASC";
        let args = params![sortition];

        query_rows(conn, qry, args)
    }

    /// Get all the missed block commits that were intended to be included in the given
    ///  block but were not
    pub fn get_missed_commits_by_intended(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<MissedBlockCommit>, db_error> {
        let qry = "SELECT * FROM missed_commits WHERE intended_sortition_id = ?1";
        let args = params![sortition];

        query_rows(conn, qry, args)
    }

    /// Get all leader keys registered in a block on the burn chain's history in this fork.
    /// Returns the list of leader keys in order by vtxindex.
    pub fn get_leader_keys_by_block(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<LeaderKeyRegisterOp>, db_error> {
        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 ORDER BY vtxindex ASC";
        let args = params![sortition];

        query_rows(conn, qry, args)
    }

    /// Get the vtxindex of the winning sortition.
    /// The sortition may not be valid.
    pub fn get_block_winning_vtxindex(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Option<u16>, db_error> {
        let qry = "SELECT vtxindex FROM block_commits WHERE sortition_id = ?1
                    AND txid = (
                      SELECT winning_block_txid FROM snapshots WHERE sortition_id = ?2 LIMIT 1) LIMIT 1";
        let args = params![sortition, sortition];
        conn.query_row(qry, args, |row| row.get(0))
            .optional()
            .map_err(db_error::from)
    }

    /// Given the fork index hash of a chain tip, and a block height that is an ancestor of the last
    /// block in this fork, find the snapshot of the block at that height.
    ///
    /// Returns None if there is no ancestor at this height.
    pub fn get_ancestor_snapshot<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        ancestor_block_height: u64,
        tip_block_hash: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(ancestor_block_height < BLOCK_HEIGHT_MAX);

        let ancestor = match get_ancestor_sort_id(ic, ancestor_block_height, tip_block_hash)? {
            Some(id) => id,
            None => {
                debug!(
                    "No ancestor block {} from {} in index",
                    ancestor_block_height, tip_block_hash
                );
                return Ok(None);
            }
        };

        SortitionDB::get_block_snapshot(ic, &ancestor)
    }

    /// Given the fork index hash of a chain tip, and a block height that is an ancestor of the last
    /// block in this fork, find the snapshot of the block at that height.
    pub fn get_ancestor_snapshot_tx<C: SortitionContext>(
        ic: &mut IndexDBTx<'_, C, SortitionId>,
        ancestor_block_height: u64,
        tip_block_hash: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(ancestor_block_height < BLOCK_HEIGHT_MAX);

        let ancestor = match get_ancestor_sort_id_tx(ic, ancestor_block_height, tip_block_hash)? {
            Some(id) => id,
            None => {
                debug!(
                    "No ancestor block {} from {} in index",
                    ancestor_block_height, tip_block_hash
                );
                return Ok(None);
            }
        };

        SortitionDB::get_block_snapshot(ic.tx(), &ancestor)
    }

    /// Get a parent block commit at a specific location in the burn chain on a particular fork.
    /// Returns None if there is no block commit at this location.
    pub fn get_block_commit_parent<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        block_height: u64,
        vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let ancestor_id = match get_ancestor_sort_id(ic, block_height, tip)? {
            Some(id) => id,
            None => {
                return Ok(None);
            }
        };

        SortitionDB::get_block_commit_of_sortition(ic, &ancestor_id, block_height, vtxindex)
    }

    fn get_block_commit_of_sortition(
        conn: &Connection,
        sortition: &SortitionId,
        block_height: u64,
        vtxindex: u32,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args = params![sortition, u64_to_sql(block_height)?, vtxindex];
        query_row_panic(conn, qry, args, || {
            format!(
                "Multiple parent blocks at {},{} in {}",
                block_height, vtxindex, sortition
            )
        })
    }

    /// Get a leader key at a specific location in the burn chain's fork history, given the
    /// matching block commit's fork index root (block_height and vtxindex are the leader's
    /// calculated location in this fork).
    /// Returns None if there is no leader key at this location.
    pub fn get_leader_key_at<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        key_block_height: u64,
        key_vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        assert!(key_block_height < BLOCK_HEIGHT_MAX);
        let ancestor_snapshot = match SortitionDB::get_ancestor_snapshot(ic, key_block_height, tip)?
        {
            Some(sn) => sn,
            None => {
                return Ok(None);
            }
        };

        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args = params![
            ancestor_snapshot.sortition_id,
            u64_to_sql(key_block_height)?,
            key_vtxindex,
        ];
        query_row_panic(ic, qry, args, || {
            format!(
                "Multiple keys at {},{} in {}",
                key_block_height, key_vtxindex, tip
            )
        })
    }

    /// Get a block commit by its committed block.
    /// For Stacks 2.x, `block_hash` is just the hash of the block
    /// For Nakamoto, `block_hash` is the StacksBlockId of the last tenure's first block
    pub fn get_block_commit_for_stacks_block(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        let (sortition_id, winning_txid) = match SortitionDB::get_block_snapshot_consensus(
            conn,
            consensus_hash,
        )? {
            Some(sn) => {
                if !sn.pox_valid {
                    warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", consensus_hash);
                    return Err(db_error::InvalidPoxSortition);
                }
                (sn.sortition_id, sn.winning_block_txid)
            }
            None => {
                return Ok(None);
            }
        };

        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND block_header_hash = ?2 AND txid = ?3";
        let args = params![sortition_id, block_hash, winning_txid];
        query_row_panic(conn, qry, args, || {
            format!("FATAL: multiple block commits for {}", &block_hash)
        })
    }

    /// Get a block snapshot for a winning block hash in a given burn chain fork.
    pub fn get_block_snapshot_for_winning_stacks_block(
        ic: &SortitionDBConn,
        tip: &SortitionId,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        match ic.get_indexed(tip, &db_keys::stacks_block_present(block_hash))? {
            Some(sortition_id_hex) => {
                let sortition_id = SortitionId::from_hex(&sortition_id_hex)
                    .expect("FATAL: DB stored non-parseable sortition id");
                SortitionDB::get_block_snapshot(ic, &sortition_id)
            }
            None => Ok(None),
        }
    }

    /// Merge the result of get_stacks_header_hashes() into a BlockHeaderCache
    pub fn merge_block_header_cache(
        cache: &mut BlockHeaderCache,
        header_data: &[(ConsensusHash, Option<BlockHeaderHash>)],
    ) {
        if !header_data.is_empty() {
            let mut i = header_data.len() - 1;
            while i > 0 {
                let cur_consensus_hash = &header_data[i].0;
                let cur_block_opt = &header_data[i].1;

                if let Some((ref cached_block_opt, _)) = cache.get(cur_consensus_hash) {
                    assert_eq!(cached_block_opt, cur_block_opt);
                } else {
                    let prev_consensus_hash = header_data[i - 1].0.clone();
                    cache.insert(
                        (*cur_consensus_hash).clone(),
                        ((*cur_block_opt).clone(), prev_consensus_hash.clone()),
                    );
                }

                i -= 1;
            }
        }
        debug!("Block header cache has {} items", cache.len());
    }

    /// Get the StacksEpoch for a given burn block height
    pub fn get_stacks_epoch(
        conn: &DBConn,
        burn_block_height: u64,
    ) -> Result<Option<StacksEpoch>, db_error> {
        let sql =
            "SELECT * FROM epochs WHERE start_block_height <= ?1 AND ?2 < end_block_height LIMIT 1";
        let args = params![
            u64_to_sql(burn_block_height)?,
            u64_to_sql(burn_block_height)?,
        ];
        query_row(conn, sql, args)
    }

    /// Get all sortition IDs at the given burnchain block height (including ones that aren't on
    /// the canonical PoX fork)
    pub fn get_sortition_ids_at_height(
        conn: &DBConn,
        height: u64,
    ) -> Result<Vec<SortitionId>, db_error> {
        query_rows(
            conn,
            "SELECT sortition_id FROM snapshots WHERE block_height = ?1",
            &[&u64_to_sql(height)?],
        )
    }

    /// Get all StacksEpochs, in order by ascending start height
    pub fn get_stacks_epochs(conn: &DBConn) -> Result<Vec<StacksEpoch>, db_error> {
        let sql = "SELECT * FROM epochs ORDER BY start_block_height ASC";
        query_rows(conn, sql, NO_PARAMS)
    }

    pub fn get_stacks_epoch_by_epoch_id(
        conn: &DBConn,
        epoch_id: &StacksEpochId,
    ) -> Result<Option<StacksEpoch>, db_error> {
        let sql = "SELECT * FROM epochs WHERE epoch_id = ?1 LIMIT 1";
        let args = params![*epoch_id as u32];
        query_row(conn, sql, args)
    }

    // TODO: add tests from mutation testing results #4849
    #[cfg_attr(test, mutants::skip)]
    /// Are microblocks disabled by Epoch 2.5 at the height specified
    /// in `at_burn_height`?
    pub fn are_microblocks_disabled(conn: &DBConn, at_burn_height: u64) -> Result<bool, db_error> {
        match Self::get_stacks_epoch_by_epoch_id(conn, &StacksEpochId::Epoch25)? {
            Some(epoch_25) => Ok(at_burn_height >= epoch_25.start_height),
            None => {
                // Epoch 2.5 is not defined, so it cannot disable microblocks
                Ok(false)
            }
        }
    }

    /// Get the last reward cycle in epoch 2.05
    pub fn get_last_epoch_2_05_reward_cycle(&self) -> Result<u64, db_error> {
        Self::static_get_last_epoch_2_05_reward_cycle(
            self.conn(),
            self.first_block_height,
            &self.pox_constants,
        )
    }

    /// Get the last reward cycle in epoch 2.05
    pub fn static_get_last_epoch_2_05_reward_cycle(
        conn: &DBConn,
        first_block_height: u64,
        pox_constants: &PoxConstants,
    ) -> Result<u64, db_error> {
        let epochs = SortitionDB::get_stacks_epochs(conn)?;

        for epoch in epochs {
            if epoch.epoch_id == StacksEpochId::Epoch2_05 {
                return Ok(pox_constants
                    .block_height_to_reward_cycle(first_block_height, epoch.end_height)
                    .expect("FATAL: end block of epoch 2.05 is before system start height"));
            }
        }

        Ok(u64::MAX)
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    /// Search snapshots up to (but excluding) the given block height.
    /// Will always return a snapshot -- even if it's the initial sentinel snapshot.
    pub fn get_last_snapshot_with_sortition_tx(
        tx: &mut SortitionDBTx,
        burn_block_height: u64,
        chain_tip: &SortitionId,
    ) -> Result<BlockSnapshot, db_error> {
        assert!(burn_block_height < BLOCK_HEIGHT_MAX);
        test_debug!(
            "Get snapshot at from sortition tip {}, expect height {}",
            chain_tip,
            burn_block_height
        );
        let get_from = match get_ancestor_sort_id_tx(tx, burn_block_height, chain_tip)? {
            Some(sortition_id) => sortition_id,
            None => {
                error!(
                    "No blockheight {} ancestor at sortition identifier {}",
                    burn_block_height, &chain_tip
                );
                return Err(db_error::NotFoundError);
            }
        };

        let ancestor_hash = match tx.get_indexed(&get_from, &db_keys::last_sortition())? {
            Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).unwrap_or_else(|_| {
                panic!(
                    "FATAL: corrupt database: failed to parse {} into a hex string",
                    &hex_str
                )
            }),
            None => {
                // no prior sortitions, so get the first
                return SortitionDB::get_first_block_snapshot(tx);
            }
        };

        let sortition_identifier_key = db_keys::sortition_id_for_bhh(&ancestor_hash);
        let sortition_id = match tx.get_indexed(chain_tip, &sortition_identifier_key)? {
            None => return SortitionDB::get_first_block_snapshot(tx),
            Some(x) => SortitionId::from_hex(&x).expect("FATAL: bad Sortition ID stored in DB"),
        };

        SortitionDB::get_block_snapshot(tx, &sortition_id)
            .map(|x| x.expect("FATAL: no snapshot for MARF'ed sortition ID"))
    }
}

impl SortitionHandleTx<'_> {
    /// Append a snapshot to a chain tip, and update various chain tip statistics.
    /// Returns the new state root of this fork.
    /// `initialize_bonus` - if Some(..), then this snapshot is the first mined snapshot,
    ///    and this method should initialize the `initial_mining_bonus` fields in the sortition db.
    pub fn append_chain_tip_snapshot(
        &mut self,
        parent_snapshot: &BlockSnapshot,
        snapshot: &BlockSnapshot,
        block_ops: &[BlockstackOperationType],
        missed_commits: &[MissedBlockCommit],
        next_pox_info: Option<RewardCycleInfo>,
        reward_info: Option<&RewardSetInfo>,
        initialize_bonus: Option<InitialMiningBonus>,
    ) -> Result<TrieHash, db_error> {
        assert_eq!(
            snapshot.parent_burn_header_hash,
            parent_snapshot.burn_header_hash
        );
        assert_eq!(snapshot.parent_sortition_id, parent_snapshot.sortition_id);
        assert_eq!(parent_snapshot.block_height + 1, snapshot.block_height);
        if snapshot.sortition {
            assert_eq!(parent_snapshot.num_sortitions + 1, snapshot.num_sortitions);
        } else {
            assert_eq!(parent_snapshot.num_sortitions, snapshot.num_sortitions);
        }

        let mut parent_sn = parent_snapshot.clone();
        let (root_hash, pox_payout) = self.index_add_fork_info(
            &mut parent_sn,
            snapshot,
            block_ops,
            next_pox_info,
            reward_info,
            initialize_bonus,
        )?;

        let mut sn = snapshot.clone();
        sn.index_root = root_hash.clone();

        let cur_epoch =
            SortitionDB::get_stacks_epoch(self, snapshot.block_height)?.unwrap_or_else(|| {
                panic!(
                    "FATAL: no epoch defined for burn height {}",
                    snapshot.block_height
                )
            });

        if cur_epoch.epoch_id >= StacksEpochId::Epoch30 {
            // nakamoto behavior
            // look at stacks_chain_tips table
            let res: Result<_, db_error> = self.deref().query_row_and_then(
                "SELECT consensus_hash,block_hash,block_height FROM stacks_chain_tips WHERE sortition_id = ? ORDER BY block_height DESC LIMIT 1",
                &[&parent_snapshot.sortition_id],
                |row| Ok((row.get_unwrap(0), row.get_unwrap(1), (u64::try_from(row.get_unwrap::<_, i64>(2)).expect("FATAL: block height too high"))))
            );
            let (
                canonical_stacks_tip_consensus_hash,
                canonical_stacks_tip_block_hash,
                canonical_stacks_tip_height,
            ) = res?;
            debug!(
                "Setting stacks_chain_tips values";
                "sortition_id" => %sn.sortition_id,
                "parent_sortition_id" => %parent_snapshot.sortition_id,
                "stacks_tip_height" => canonical_stacks_tip_height,
                "stacks_tip_hash" => %canonical_stacks_tip_block_hash,
                "stacks_tip_consensus" => %canonical_stacks_tip_consensus_hash
            );
            sn.canonical_stacks_tip_height = canonical_stacks_tip_height;
            sn.canonical_stacks_tip_hash = canonical_stacks_tip_block_hash;
            sn.canonical_stacks_tip_consensus_hash = canonical_stacks_tip_consensus_hash;
        } else {
            // epoch 2.x behavior
            // preserve memoized stacks chain tip from this burn chain fork
            sn.canonical_stacks_tip_height = parent_sn.canonical_stacks_tip_height;
            sn.canonical_stacks_tip_hash = parent_sn.canonical_stacks_tip_hash;
            sn.canonical_stacks_tip_consensus_hash = parent_sn.canonical_stacks_tip_consensus_hash;
        }

        if self.context.dryrun {
            // don't do any inserts
            return Ok(root_hash);
        }

        self.insert_block_snapshot(&sn, pox_payout)?;

        for block_op in block_ops {
            self.store_burnchain_transaction(block_op, &sn.sortition_id)?;
        }

        for missed_commit in missed_commits {
            self.insert_missed_block_commit(missed_commit)?;
        }

        self.update_canonical_stacks_tip(
            &sn.sortition_id,
            &sn.canonical_stacks_tip_consensus_hash,
            &sn.canonical_stacks_tip_hash,
            sn.canonical_stacks_tip_height,
        )?;

        #[cfg(test)]
        {
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(self).unwrap();

            debug!(
                "After sortition {}, canonical Stacks tip is {}/{}",
                &snapshot.consensus_hash, &block_consensus_hash, &block_bhh
            );
        }
        Ok(root_hash)
    }

    pub fn get_initial_mining_bonus_remaining(
        &mut self,
        chain_tip: &SortitionId,
    ) -> Result<u128, db_error> {
        self.get_indexed(&chain_tip, db_keys::initial_mining_bonus_remaining())?
            .map(|s| Ok(s.parse().expect("BUG: bad mining bonus stored in DB")))
            .unwrap_or(Ok(0))
    }

    pub fn get_initial_mining_bonus_per_block(
        &mut self,
        chain_tip: &SortitionId,
    ) -> Result<Option<u128>, db_error> {
        Ok(self
            .get_indexed(&chain_tip, db_keys::initial_mining_bonus_per_block())?
            .map(|s| s.parse().expect("BUG: bad mining bonus stored in DB")))
    }

    #[cfg(any(test, feature = "testing"))]
    fn store_burn_distribution(
        &mut self,
        new_sortition: &SortitionId,
        transition: &BurnchainStateTransition,
    ) {
        let create = "CREATE TABLE IF NOT EXISTS snapshot_burn_distributions (sortition_id TEXT PRIMARY KEY, data TEXT NOT NULL);";
        self.execute(create, NO_PARAMS).unwrap();
        let sql = "INSERT INTO snapshot_burn_distributions (sortition_id, data) VALUES (?, ?)";
        let args = params![
            new_sortition,
            serde_json::to_string(&transition.burn_dist).unwrap(),
        ];
        self.execute(sql, args).unwrap();
    }

    #[cfg(not(any(test, feature = "testing")))]
    fn store_burn_distribution(
        &mut self,
        _new_sortition: &SortitionId,
        _transition: &BurnchainStateTransition,
    ) {
    }

    fn store_transition_ops(
        &mut self,
        new_sortition: &SortitionId,
        transition: &BurnchainStateTransition,
    ) -> Result<(), db_error> {
        let sql = "INSERT INTO snapshot_transition_ops (sortition_id, accepted_ops, consumed_keys) VALUES (?, ?, ?)";
        let args = params![
            new_sortition,
            serde_json::to_string(&transition.accepted_ops).unwrap(),
            serde_json::to_string(&transition.consumed_leader_keys).unwrap(),
        ];
        self.execute(sql, args)?;
        self.store_burn_distribution(new_sortition, transition);
        Ok(())
    }

    pub fn get_pox_id(&mut self) -> Result<PoxId, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let pox_id = self
            .get_indexed(&chain_tip, db_keys::pox_identifier())?
            .map(|s| s.parse().expect("BUG: Bad PoX identifier stored in DB"))
            .expect("BUG: No PoX identifier stored.");
        Ok(pox_id)
    }

    /// Store a blockstack burnchain operation
    fn store_burnchain_transaction(
        &mut self,
        blockstack_op: &BlockstackOperationType,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        match blockstack_op {
            BlockstackOperationType::LeaderKeyRegister(ref op) => {
                info!(
                    "ACCEPTED({}) leader key register {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex;
                    "consensus_hash" => %op.consensus_hash,
                    "burn_header_hash" => %op.burn_header_hash
                );
                self.insert_leader_key(op, sort_id)
            }
            BlockstackOperationType::LeaderBlockCommit(ref op) => {
                info!(
                    "ACCEPTED({}) leader block commit {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex;
                    "apparent_sender" => %op.apparent_sender,
                    "stacks_block_hash" => %op.block_header_hash
                );
                self.insert_block_commit(op, sort_id)
            }
            BlockstackOperationType::StackStx(ref op) => {
                info!(
                    "ACCEPTED({}) stack stx opt {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_stack_stx(op)
            }
            BlockstackOperationType::TransferStx(ref op) => {
                info!(
                    "ACCEPTED({}) transfer stx opt {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_transfer_stx(op)
            }
            BlockstackOperationType::PreStx(ref op) => {
                info!(
                    "ACCEPTED({}) pre stack stx op {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex;
                    "burn_header_hash" => %op.burn_header_hash
                );
                // no need to store this op in the sortition db.
                Ok(())
            }
            BlockstackOperationType::DelegateStx(ref op) => {
                info!(
                    "ACCEPTED({}) delegate stx opt {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_delegate_stx(op)
            }
            BlockstackOperationType::VoteForAggregateKey(ref op) => {
                info!(
                    "ACCEPTED({}) vote for aggregate key {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_vote_for_aggregate_key(op)
            }
        }
    }

    /// Insert a leader key registration.
    /// No validity checking will be done, beyond what is encoded in the leader_keys table
    /// constraints.  That is, type mismatches and serialization issues will be caught, but nothing else.
    /// The corresponding snapshot must already be inserted
    fn insert_leader_key(
        &mut self,
        leader_key: &LeaderKeyRegisterOp,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        assert!(leader_key.block_height < BLOCK_HEIGHT_MAX);

        let args = params![
            leader_key.txid,
            leader_key.vtxindex,
            u64_to_sql(leader_key.block_height)?,
            leader_key.burn_header_hash,
            leader_key.consensus_hash,
            leader_key.public_key.to_hex(),
            to_hex(&leader_key.memo),
            sort_id,
        ];

        self.execute("INSERT INTO leader_keys (txid, vtxindex, block_height, burn_header_hash, consensus_hash, public_key, memo, sortition_id) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)", args)?;

        Ok(())
    }

    /// Insert a stack-stx op
    fn insert_stack_stx(&mut self, op: &StackStxOp) -> Result<(), db_error> {
        let args = params![
            op.txid,
            op.vtxindex,
            u64_to_sql(op.block_height)?,
            op.burn_header_hash,
            op.sender.to_string(),
            op.reward_addr.to_db_string(),
            op.stacked_ustx.to_string(),
            op.num_cycles,
            serde_json::to_string(&op.signer_key).unwrap(),
            serde_json::to_string(&op.max_amount).unwrap(),
            op.auth_id,
        ];

        self.execute("REPLACE INTO stack_stx (txid, vtxindex, block_height, burn_header_hash, sender_addr, reward_addr, stacked_ustx, num_cycles, signer_key, max_amount, auth_id) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)", args)?;

        Ok(())
    }

    /// Insert a delegate-stx op
    fn insert_delegate_stx(&mut self, op: &DelegateStxOp) -> Result<(), db_error> {
        let args = params![
            op.txid,
            op.vtxindex,
            u64_to_sql(op.block_height)?,
            op.burn_header_hash,
            op.sender.to_string(),
            op.delegate_to.to_string(),
            serde_json::to_string(&op.reward_addr).unwrap(),
            op.delegated_ustx.to_string(),
            opt_u64_to_sql(op.until_burn_height)?,
        ];

        self.execute("REPLACE INTO delegate_stx (txid, vtxindex, block_height, burn_header_hash, sender_addr, delegate_to, reward_addr, delegated_ustx, until_burn_height) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)", args)?;

        Ok(())
    }

    /// Insert a vote-for-aggregate-key op
    fn insert_vote_for_aggregate_key(
        &mut self,
        op: &VoteForAggregateKeyOp,
    ) -> Result<(), db_error> {
        let args = params![
            op.txid,
            op.vtxindex,
            u64_to_sql(op.block_height)?,
            op.burn_header_hash,
            op.sender.to_string(),
            serde_json::to_string(&op.aggregate_key).unwrap(),
            op.round,
            u64_to_sql(op.reward_cycle)?,
            op.signer_index,
            serde_json::to_string(&op.signer_key).unwrap(),
        ];

        self.execute("REPLACE INTO vote_for_aggregate_key (txid, vtxindex, block_height, burn_header_hash, sender_addr, aggregate_key, round, reward_cycle, signer_index, signer_key) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)", args)?;

        Ok(())
    }

    /// Insert a transfer-stx op
    fn insert_transfer_stx(&mut self, op: &TransferStxOp) -> Result<(), db_error> {
        let args = params![
            op.txid,
            op.vtxindex,
            u64_to_sql(op.block_height)?,
            op.burn_header_hash,
            op.sender.to_string(),
            op.recipient.to_string(),
            op.transfered_ustx.to_string(),
            to_hex(&op.memo),
        ];

        self.execute("REPLACE INTO transfer_stx (txid, vtxindex, block_height, burn_header_hash, sender_addr, recipient_addr, transfered_ustx, memo) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)", args)?;

        Ok(())
    }

    /// Insert a leader block commitment.
    /// No validity checking will be done, beyond what is encoded in the block_commits table
    /// constraints.  That is, type mismatches and serialization issues will be caught, but nothing else.
    /// The corresponding snapshot must already be inserted
    fn insert_block_commit(
        &mut self,
        block_commit: &LeaderBlockCommitOp,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        assert!(block_commit.block_height < BLOCK_HEIGHT_MAX);

        // serialize tx input to JSON
        let tx_input_str =
            serde_json::to_string(&block_commit.input).map_err(db_error::SerializationError)?;

        // serialize apparent sender to JSON
        let apparent_sender_str = serde_json::to_string(&block_commit.apparent_sender)
            .map_err(db_error::SerializationError)?;

        // find parent block commit's snapshot's sortition ID.
        // If the parent_block_ptr doesn't point to a valid snapshot, then store an empty
        // sortition.  If we're not testing, then this should never happen.
        let parent_sortition_id = self
            .get_block_snapshot_by_height(block_commit.parent_block_ptr as u64)?
            .map(|parent_commit_sn| parent_commit_sn.sortition_id)
            .unwrap_or(SortitionId([0x00; 32]));

        if !cfg!(test) && (block_commit.parent_block_ptr != 0 || block_commit.parent_vtxindex != 0)
        {
            assert!(parent_sortition_id != SortitionId([0x00; 32]));
        }

        let args = params![
            block_commit.txid,
            block_commit.vtxindex,
            u64_to_sql(block_commit.block_height)?,
            block_commit.burn_header_hash,
            block_commit.block_header_hash,
            block_commit.new_seed,
            block_commit.parent_block_ptr,
            block_commit.parent_vtxindex,
            block_commit.key_block_ptr,
            block_commit.key_vtxindex,
            to_hex(&block_commit.memo[..]),
            block_commit.burn_fee.to_string(),
            tx_input_str,
            sort_id,
            serde_json::to_value(&block_commit.commit_outs).unwrap(),
            block_commit.sunset_burn.to_string(),
            apparent_sender_str,
            block_commit.burn_parent_modulus,
            serde_json::to_string(&block_commit.treatment).unwrap(),
        ];

        self.execute("INSERT INTO block_commits (txid, vtxindex, block_height, burn_header_hash, block_header_hash, new_seed, parent_block_ptr, parent_vtxindex, key_block_ptr, key_vtxindex, memo, burn_fee, input, sortition_id, commit_outs, sunset_burn, apparent_sender, burn_parent_modulus, punished) \
                      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19)", args)?;

        let parent_args = params![sort_id, block_commit.txid, parent_sortition_id];

        debug!(
            "Parent sortition of {},{},{} is {} (parent at {},{})",
            &block_commit.txid,
            block_commit.block_height,
            block_commit.vtxindex,
            &parent_sortition_id,
            block_commit.parent_block_ptr,
            block_commit.parent_vtxindex
        );
        let res = self.execute("INSERT INTO block_commit_parents (block_commit_sortition_id, block_commit_txid, parent_sortition_id) VALUES (?1, ?2, ?3)", parent_args);

        // in tests, this table doesn't always exist.  Do nothing in that case, but in prod, error
        // out if this fails.
        if !cfg!(test) {
            res?;
        }

        Ok(())
    }

    /// Insert a missed block commit
    fn insert_missed_block_commit(&mut self, op: &MissedBlockCommit) -> Result<(), db_error> {
        // serialize tx input to JSON
        let tx_input_str =
            serde_json::to_string(&op.input).map_err(db_error::SerializationError)?;

        let args = params![op.txid, op.intended_sortition, tx_input_str];

        self.execute(
            "INSERT OR REPLACE INTO missed_commits (txid, intended_sortition_id, input) \
                      VALUES (?1, ?2, ?3)",
            args,
        )?;
        info!(
            "ACCEPTED missed block commit";
            "txid" => %op.txid,
            "intended_sortition" => %op.intended_sortition,
        );

        Ok(())
    }

    /// Insert a snapshots row from a block's-worth of operations.
    /// Do not call directly -- use append_chain_tip_snapshot to preserve the fork table structure.
    fn insert_block_snapshot(
        &self,
        snapshot: &BlockSnapshot,
        total_pox_payouts: (Vec<PoxAddress>, u128),
    ) -> Result<(), db_error> {
        assert!(snapshot.block_height < BLOCK_HEIGHT_MAX);
        assert!(snapshot.num_sortitions < BLOCK_HEIGHT_MAX);

        let pox_payouts_json = serde_json::to_string(&total_pox_payouts)
            .expect("FATAL: could not encode `total_pox_payouts` as JSON");

        test_debug!(
            "Insert block snapshot state {} for block {} ({},{}) {}, winner = {}",
            snapshot.index_root,
            snapshot.block_height,
            snapshot.burn_header_hash,
            snapshot.parent_burn_header_hash,
            snapshot.num_sortitions,
            &snapshot.winning_stacks_block_hash
        );

        // there had better not be any other valid snapshots for this block
        if snapshot.pox_valid {
            let all_valid_sortitions: Vec<i64> = query_rows(
                self,
                "SELECT 1 FROM snapshots WHERE burn_header_hash = ?1 AND pox_valid = 1 LIMIT 1",
                &[&snapshot.burn_header_hash],
            )?;
            if !all_valid_sortitions.is_empty() {
                error!("FATAL: Tried to insert snapshot {:?}, but already have pox-valid sortition for {:?}", &snapshot, &snapshot.burn_header_hash);
                panic!();
            }
        }

        let args = params![
            u64_to_sql(snapshot.block_height)?,
            snapshot.burn_header_hash,
            u64_to_sql(snapshot.burn_header_timestamp)?,
            snapshot.parent_burn_header_hash,
            snapshot.consensus_hash,
            snapshot.ops_hash,
            snapshot.total_burn.to_string(),
            snapshot.sortition,
            snapshot.sortition_hash,
            snapshot.winning_block_txid,
            snapshot.winning_stacks_block_hash,
            snapshot.index_root,
            u64_to_sql(snapshot.num_sortitions)?,
            snapshot.stacks_block_accepted,
            u64_to_sql(snapshot.stacks_block_height)?,
            u64_to_sql(snapshot.arrival_index)?,
            u64_to_sql(snapshot.canonical_stacks_tip_height)?,
            snapshot.canonical_stacks_tip_hash,
            snapshot.canonical_stacks_tip_consensus_hash,
            snapshot.sortition_id,
            snapshot.parent_sortition_id,
            snapshot.pox_valid,
            snapshot.accumulated_coinbase_ustx.to_string(),
            pox_payouts_json,
            snapshot.miner_pk_hash,
        ];

        self.execute("INSERT INTO snapshots \
                      (block_height, burn_header_hash, burn_header_timestamp, parent_burn_header_hash, consensus_hash, ops_hash, total_burn, sortition, sortition_hash, winning_block_txid, winning_stacks_block_hash, index_root, num_sortitions, \
                      stacks_block_accepted, stacks_block_height, arrival_index, canonical_stacks_tip_height, canonical_stacks_tip_hash, canonical_stacks_tip_consensus_hash, sortition_id, parent_sortition_id, pox_valid, accumulated_coinbase_ustx, \
                      pox_payouts, miner_pk_hash) \
                      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, ?20, ?21, ?22, ?23, ?24, ?25)", args)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Get the expected number of PoX payouts per output
    fn get_num_pox_payouts(&self, burn_block_height: u64) -> usize {
        let op_num_outputs = if PoxConstants::static_is_in_prepare_phase(
            self.context.first_block_height,
            u64::from(self.context.pox_constants.reward_cycle_length),
            u64::from(self.context.pox_constants.prepare_length),
            burn_block_height,
        ) {
            1
        } else {
            OUTPUTS_PER_COMMIT
        };
        op_num_outputs
    }

    /// Given all of a snapshot's block ops, calculate how many burnchain tokens were sent to each
    /// PoX payout.  Note that this value is *per payout*:
    /// * in a reward phase, multiply this by OUTPUTS_PER_COMMIT to get the total amount of tokens
    /// sent across all miners.
    /// * in a prepare phase, where there is only one output, this value is the total amount of
    /// tokens sent across all miners.
    fn get_pox_payout_per_output(&self, block_ops: &[BlockstackOperationType]) -> u128 {
        let mut total = 0u128;
        for block_op in block_ops.iter() {
            if let BlockstackOperationType::LeaderBlockCommit(ref op) = block_op {
                // burn_fee = pox_fee * OUTPUTS_PER_COMMIT
                // we're finding sum(pox_fee)
                let num_outputs = self.get_num_pox_payouts(op.block_height);
                total += (op.burn_fee as u128) / (num_outputs as u128);
            }
        }

        total
    }

    /// Record fork information to the index and calculate the new fork index root hash.
    /// * sortdb::vrf::${VRF_PUBLIC_KEY} --> 0 or 1 (1 if available, 0 if consumed), for each VRF public key we process
    /// * sortdb::last_sortition --> $BURN_BLOCK_HASH, for each block that had a sortition
    /// * sortdb::sortition_block_hash::${STACKS_BLOCK_HASH} --> $BURN_BLOCK_HASH for each winning block sortition
    /// * sortdb::stacks::block::${STACKS_BLOCK_HASH} --> ${STACKS_BLOCK_HEIGHT} for each block that has been accepted so far
    /// * sortdb::stacks::block::max_arrival_index --> ${ARRIVAL_INDEX} to set the maximum arrival index processed in this fork
    /// * sortdb::pox_reward_set::${n} --> recipient Bitcoin address, to track the reward set as the permutation progresses
    ///
    /// `recipient_info` is used to pass information to this function about which reward set addresses were consumed
    ///   during this sortition. this object will be None in the following cases:
    ///    * The reward cycle had an anchor block, but it isn't known by this node.
    ///    * The reward cycle did not have anchor block
    ///    * The Stacking recipient set is empty (either because this reward cycle has already exhausted the set of addresses or because no one ever Stacked).
    ///
    /// NOTE: the resulting index root must be globally unique.  This is guaranteed because each
    /// burn block hash is unique, no matter what fork it's on (and this index uses burn block
    /// hashes as its index's block hash data).
    fn index_add_fork_info(
        &mut self,
        parent_snapshot: &mut BlockSnapshot,
        snapshot: &BlockSnapshot,
        block_ops: &[BlockstackOperationType],
        next_pox_info: Option<RewardCycleInfo>,
        recipient_info: Option<&RewardSetInfo>,
        initialize_bonus: Option<InitialMiningBonus>,
    ) -> Result<(TrieHash, (Vec<PoxAddress>, u128)), db_error> {
        if !snapshot.is_initial() {
            assert_eq!(
                snapshot.parent_burn_header_hash,
                parent_snapshot.burn_header_hash
            );
            assert_eq!(&parent_snapshot.sortition_id, &self.context.chain_tip);
        }

        // data we want to store
        let mut keys = vec![];
        let mut values = vec![];

        // record each new VRF key, and each consumed VRF key
        for block_op in block_ops.iter() {
            if let BlockstackOperationType::LeaderKeyRegister(ref data) = block_op {
                keys.push(db_keys::vrf_key_status(&data.public_key));
                values.push("1".to_string()); // the value is no longer used, but the key needs to exist to figure whether a key was registered
            }
        }

        // map burnchain header hashes to sortition ids
        keys.push(db_keys::sortition_id_for_bhh(&snapshot.burn_header_hash));
        values.push(snapshot.sortition_id.to_hex());

        // if this commit has a sortition, record its burn block hash and stacks block hash
        if snapshot.sortition {
            keys.push(db_keys::last_sortition().to_string());
            values.push(snapshot.burn_header_hash.to_hex());

            keys.push(db_keys::stacks_block_present(
                &snapshot.winning_stacks_block_hash,
            ));
            values.push(snapshot.sortition_id.to_hex());
        }

        if let Some(initialize_bonus) = initialize_bonus {
            debug!("Add initial mining bonus: {:?}", &initialize_bonus);
            // first sortition with a winner, set the initial mining bonus fields
            keys.push(db_keys::initial_mining_bonus_per_block().into());
            values.push(initialize_bonus.per_block.to_string());

            let total_reward_remaining = initialize_bonus
                .total_reward
                .saturating_sub(initialize_bonus.per_block);
            keys.push(db_keys::initial_mining_bonus_remaining().into());
            values.push(total_reward_remaining.to_string());
        } else if parent_snapshot.total_burn > 0 {
            // mining has started, check if there's still any remaining bonus that this
            //  block consumed, and then decrement
            let prior_bonus_remaining =
                self.get_initial_mining_bonus_remaining(&parent_snapshot.sortition_id)?;
            if prior_bonus_remaining > 0 {
                let mining_bonus_per_block = self
                    .get_initial_mining_bonus_per_block(&parent_snapshot.sortition_id)?
                    .expect(
                        "BUG: initial mining bonus amount written, but not the per block amount.",
                    );
                let bonus_remaining = prior_bonus_remaining.saturating_sub(mining_bonus_per_block);
                keys.push(db_keys::initial_mining_bonus_remaining().into());
                values.push(bonus_remaining.to_string());
            }
        }

        // if this is the start of a reward cycle, store the new PoX keys.
        // Get the PoX payouts while doing so.
        let pox_payout = self.get_pox_payout_per_output(block_ops);
        let mut pox_payout_addrs = if !snapshot.is_initial() {
            if let Some(reward_info) = next_pox_info {
                let mut pox_id = self.get_pox_id()?;
                let pox_payout_addrs;

                // update the PoX bit vector with whether or not
                //  this reward cycle is aware of its anchor (if one wasn't selected,
                //   mark this as "known")
                if reward_info.is_reward_info_known() {
                    pox_id.extend_with_present_block();
                } else {
                    pox_id.extend_with_not_present_block();
                }

                let mut cur_affirmation_map = self.get_sortition_affirmation_map()?;
                let mut selected_anchor_block = false;

                // if we have selected an anchor block (known or unknown), write that info
                if let Some((anchor_block, anchor_block_txid)) = reward_info.selected_anchor_block()
                {
                    selected_anchor_block = true;

                    keys.push(db_keys::pox_anchor_to_prepare_end(anchor_block));
                    values.push(parent_snapshot.sortition_id.to_hex());

                    keys.push(db_keys::pox_last_anchor().to_string());
                    values.push(anchor_block.to_hex());

                    keys.push(db_keys::pox_last_anchor_txid().to_string());
                    values.push(anchor_block_txid.to_hex());

                    keys.push(db_keys::pox_affirmation_map().to_string());
                    values.push(cur_affirmation_map.encode());

                    keys.push(db_keys::pox_last_selected_anchor().to_string());
                    values.push(anchor_block.to_hex());

                    keys.push(db_keys::pox_last_selected_anchor_txid().to_string());
                    values.push(anchor_block_txid.to_hex());

                    debug!(
                        "Known anchor block {} txid {} at reward cycle starting at burn height {}",
                        anchor_block, anchor_block_txid, snapshot.block_height
                    );
                } else {
                    keys.push(db_keys::pox_last_anchor().to_string());
                    values.push("".to_string());

                    keys.push(db_keys::pox_last_anchor_txid().to_string());
                    values.push("".to_string());

                    cur_affirmation_map.push(AffirmationMapEntry::Nothing);

                    debug!(
                        "No anchor block at reward cycle starting at burn height {}",
                        snapshot.block_height
                    );
                }

                let _reward_cycle = reward_info.reward_cycle;

                // if we've selected an anchor _and_ know of the anchor,
                //  write the reward set information
                if let Some(mut reward_set) = reward_info.known_selected_anchor_block_owned() {
                    // record payouts separately from the remaining addresses, since some of them
                    // could have just been consumed.
                    if reward_set.rewarded_addresses.is_empty() {
                        // no payouts
                        pox_payout_addrs = vec![];
                    } else {
                        // if we have a reward set, then we must also have produced a recipient
                        //   info for this block
                        let mut recipients_to_remove: Vec<_> = recipient_info
                            .unwrap()
                            .recipients
                            .iter()
                            .map(|(addr, ix)| (addr.clone(), *ix))
                            .collect();
                        recipients_to_remove.sort_unstable_by(|(_, a), (_, b)| b.cmp(a));
                        // remove from the reward set any consumed addresses in this first reward block
                        let mut addrs = vec![];
                        for (addr, ix) in recipients_to_remove.iter() {
                            addrs.push(addr.clone());
                            assert_eq!(reward_set.rewarded_addresses.remove(*ix as usize).to_burnchain_repr(), addr.to_burnchain_repr(),
                                       "BUG: Attempted to remove used address from reward set, but failed to do so safely");
                        }
                        pox_payout_addrs = addrs;
                    }

                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(
                        reward_set.rewarded_addresses.len(),
                    ));

                    // NOTE: the pox_addr _must_ come from the reward set (i.e. from the PoX
                    // contract), since we _must_ know the hash modes for standard addresses.  This
                    // information cannot be learned from the burnchain alone.
                    for (ix, pox_addr) in reward_set.rewarded_addresses.iter().enumerate() {
                        keys.push(db_keys::pox_reward_set_entry(ix as u16));
                        values.push(pox_addr.to_db_string());
                    }
                    // if there are qualifying auto-unlocks, record them
                    if !reward_set.start_cycle_state.is_empty() {
                        let cycle_number = PoxConstants::static_block_height_to_reward_cycle(
                            snapshot.block_height,
                            self.context.first_block_height,
                            self.context.pox_constants.reward_cycle_length.into(),
                        )
                        .expect("FATAL: PoX reward cycle started before first block height");

                        keys.push(db_keys::pox_reward_cycle_unlocks(cycle_number));
                        values.push(reward_set.start_cycle_state.serialize());
                    }

                    cur_affirmation_map.push(AffirmationMapEntry::PoxAnchorBlockPresent);
                } else {
                    // no anchor block; we're burning
                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(0));

                    if selected_anchor_block {
                        cur_affirmation_map.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                    }

                    pox_payout_addrs = vec![];
                }

                // in all cases, write the new PoX bit vector
                keys.push(db_keys::pox_identifier().to_string());
                values.push(pox_id.to_string());

                keys.push(db_keys::pox_affirmation_map().to_string());
                values.push(cur_affirmation_map.encode());

                pox_payout_addrs
            } else {
                // if this snapshot consumed some reward set entries AND
                //  this isn't the start of a new reward cycle,
                //   update the reward set
                if let Some(reward_info) = recipient_info {
                    let mut current_len = self.get_reward_set_size()?;
                    let payout_addrs: Vec<_> = reward_info
                        .recipients
                        .iter()
                        .map(|(addr, _)| addr.clone())
                        .collect();
                    let mut recipient_indexes: Vec<_> =
                        reward_info.recipients.iter().map(|(_, x)| *x).collect();
                    let mut remapped_entries = HashMap::new();
                    // sort in decrementing order
                    recipient_indexes.sort_unstable_by(|a, b| b.cmp(a));
                    for index in recipient_indexes.into_iter() {
                        // sanity check
                        if index >= current_len {
                            unreachable!(
                                "Supplied index should never be greater than recipient set size"
                            );
                        } else if index + 1 == current_len {
                            // selected index is the last element: no need to swap, just decrement len
                            current_len -= 1;
                        } else {
                            let replacement = current_len - 1; // if current_len were 0, we would already have panicked.
                            let replace_with = if let Some((_prior_ix, replace_with)) =
                                remapped_entries.remove_entry(&replacement)
                            {
                                // the entry to swap in was itself swapped, so let's use the new value instead
                                replace_with
                            } else {
                                self.get_reward_set_entry(replacement)?
                            };

                            // NOTE: we have to have a hash mode for the address -- i.e. we have to be
                            // able to conver it to a clarity tuple -- since this data must be available
                            // via `get-burn-block-info?`.
                            assert!(
                                replace_with.as_clarity_tuple().is_some(),
                                "FATAL: do not know hash mode for next PoX address"
                            );

                            // swap and decrement to remove from set
                            remapped_entries.insert(index, replace_with);
                            current_len -= 1;
                        }
                    }
                    // store the changes in the new trie
                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(current_len as usize));

                    for (recipient_index, replace_with) in remapped_entries.into_iter() {
                        keys.push(db_keys::pox_reward_set_entry(recipient_index));
                        values.push(replace_with.to_db_string());
                    }

                    // reward-phase PoX payout addresses
                    payout_addrs
                } else {
                    // in prepare phase (no recipient info), so no payouts
                    vec![]
                }
            }
        } else {
            // initial snapshot
            assert_eq!(next_pox_info, None);
            keys.push(db_keys::pox_identifier().to_string());
            values.push(PoxId::initial().to_string());
            keys.push(db_keys::pox_reward_set_size().to_string());
            values.push(db_keys::reward_set_size_to_string(0));
            keys.push(db_keys::pox_last_anchor().to_string());
            values.push("".to_string());
            keys.push(db_keys::pox_last_anchor_txid().to_string());
            values.push("".to_string());
            keys.push(db_keys::pox_last_selected_anchor().to_string());
            values.push("".to_string());
            keys.push(db_keys::pox_last_selected_anchor_txid().to_string());
            values.push("".to_string());

            // no payouts
            vec![]
        };

        // store each indexed field
        let root_hash = if !self.context.dryrun {
            // commit to all newly-arrived blocks
            let (mut block_arrival_keys, mut block_arrival_values) =
                self.process_new_block_arrivals(parent_snapshot)?;
            keys.append(&mut block_arrival_keys);
            values.append(&mut block_arrival_values);

            self.put_indexed_all(
                &parent_snapshot.sortition_id,
                &snapshot.sortition_id,
                &keys,
                &values,
            )?
        } else {
            TrieHash([0x00; 32])
        };

        // pox payout addrs must include burn addresses
        let num_pox_payouts = self.get_num_pox_payouts(snapshot.block_height);
        while pox_payout_addrs.len() < num_pox_payouts {
            // NOTE: while this coerces mainnet, it's totally fine in practice because the address
            // version is not exposed to Clarity.  Clarity only sees a PoX-specific version and the
            // hash.
            pox_payout_addrs.push(PoxAddress::standard_burn_address(true));
        }

        self.context.chain_tip = snapshot.sortition_id.clone();
        Ok((root_hash, (pox_payout_addrs, pox_payout)))
    }

    /// Resolve ties between blocks at the same height.
    /// Hashes the given snapshot's sortition hash with the index block hash for each block
    /// (calculated from `new_block_arrivals`' consensus hash and block header hash), and chooses
    /// the block in `new_block_arrivals` whose resulting hash is lexographically the smallest.
    /// Returns the index into `new_block_arrivals` for the block whose hash is the smallest.
    fn break_canonical_stacks_tip_tie(
        tip: &BlockSnapshot,
        best_height: u64,
        new_block_arrivals: &[(ConsensusHash, BlockHeaderHash, u64)],
    ) -> Option<usize> {
        // if there's a tie, then randomly and deterministically pick one
        let mut tied = vec![];
        for (i, (consensus_hash, block_bhh, height)) in new_block_arrivals.iter().enumerate() {
            if best_height == *height {
                tied.push((StacksBlockId::new(consensus_hash, block_bhh), i));
            }
        }

        if tied.is_empty() {
            return None;
        }
        if tied.len() == 1 {
            return Some(tied[0].1);
        }

        // break ties by hashing the index block hash with the snapshot's sortition hash, and
        // picking the lexicographically smallest one
        let mut hash_tied = vec![];
        let mut mapping = HashMap::new();
        for (block_id, arrival_idx) in tied.into_iter() {
            let mut buff = [0u8; 64];
            buff[0..32].copy_from_slice(&block_id.0);
            buff[32..64].copy_from_slice(&tip.sortition_hash.0);

            let hashed = Sha512Trunc256Sum::from_data(&buff);
            hash_tied.push(hashed.clone());
            mapping.insert(hashed, arrival_idx);
        }

        hash_tied.sort();
        let winner = hash_tied
            .first()
            .expect("FATAL: zero-length list of tied block IDs");

        let winner_index = *mapping
            .get(&winner)
            .expect("FATAL: winning block ID not mapped");

        Some(winner_index)
    }

    /// Find the new Stacks block arrivals as of the given tip `parent_tip`, and returns
    /// the highest Stacks chain tip and maximum arrival index.
    /// Used for both discovering the new arrivals and processing them with new snapshots.
    ///
    /// Returns Ok((
    ///     stacks tip consensus hash,
    ///     stacks tip block header hash,
    ///     stacks tip height,
    ///     max arrival index,
    ///     list of all blocks that have arrived since this parent_tip
    /// ))
    fn inner_find_new_block_arrivals(
        &mut self,
        parent_tip: &BlockSnapshot,
    ) -> Result<
        (
            ConsensusHash,
            BlockHeaderHash,
            u64,
            u64,
            Vec<(BlockHeaderHash, u64)>,
        ),
        db_error,
    > {
        let mut new_block_arrivals = vec![];

        let old_max_arrival_index = self
            .get_indexed(
                &parent_tip.sortition_id,
                &db_keys::stacks_block_max_arrival_index(),
            )?
            .unwrap_or("1".into())
            .parse::<u64>()
            .expect("BUG: max arrival index is not a u64");

        let max_arrival_index = SortitionDB::get_max_arrival_index(self.tx())?;

        // find all Stacks block hashes who arrived since this parent_tip was built.
        for ari in old_max_arrival_index..(max_arrival_index + 1) {
            test_debug!("Get block with arrival index {}", ari);
            let arrival_sn = match SortitionDB::get_snapshot_by_arrival_index(self.tx(), ari)? {
                Some(sn) => sn,
                None => {
                    continue;
                }
            };
            if !arrival_sn.pox_valid {
                continue;
            }

            // must be an ancestor of this tip, or must be this tip
            if let Some(sn) =
                self.get_block_snapshot(&arrival_sn.burn_header_hash, &parent_tip.sortition_id)?
            {
                if !sn.pox_valid || sn != arrival_sn {
                    continue;
                }

                debug!(
                    "New Stacks anchored block arrived: block {}/{} ({}) ari={} tip={}",
                    &sn.consensus_hash,
                    &sn.winning_stacks_block_hash,
                    sn.stacks_block_height,
                    ari,
                    &parent_tip.burn_header_hash
                );
                new_block_arrivals.push((
                    sn.consensus_hash,
                    sn.winning_stacks_block_hash,
                    sn.stacks_block_height,
                ));
            } else {
                // this block did not arrive on an ancestor block
                continue;
            }
        }

        let mut best_tip_block_bhh = parent_tip.canonical_stacks_tip_hash.clone();
        let mut best_tip_consensus_hash = parent_tip.canonical_stacks_tip_consensus_hash.clone();
        let mut best_tip_height = parent_tip.canonical_stacks_tip_height;
        let mut ret = vec![];

        debug!(
            "Current best tip is {}/{} (height {})",
            &best_tip_consensus_hash, &best_tip_block_bhh, best_tip_height
        );

        for (consensus_hash, block_bhh, height) in new_block_arrivals.iter() {
            ret.push((block_bhh.clone(), *height));

            // genesis blocks are incomparable -- it doesn't matter which one was "first."
            // everyone else must be higher than the highest known tip to supersede it.
            if *height > best_tip_height || (*height == 0 && best_tip_height == 0) {
                debug!(
                    "At tip {}: {}/{} (height {}) is superceded by {}/{} (height {})",
                    &parent_tip.burn_header_hash,
                    &best_tip_consensus_hash,
                    &best_tip_block_bhh,
                    best_tip_height,
                    consensus_hash,
                    block_bhh,
                    *height
                );

                best_tip_block_bhh = block_bhh.clone();
                best_tip_consensus_hash = consensus_hash.clone();
                best_tip_height = *height;
            }
        }

        // if there's a tie, then randomly and deterministically pick one
        let winning_index_opt = SortitionHandleTx::break_canonical_stacks_tip_tie(
            parent_tip,
            best_tip_height,
            &new_block_arrivals,
        );
        if let Some(winning_index) = winning_index_opt {
            best_tip_consensus_hash = new_block_arrivals[winning_index].0;
            best_tip_block_bhh = new_block_arrivals[winning_index].1;
        }

        debug!(
            "Max arrival for child of {} is {} (hash {} height {})",
            &best_tip_consensus_hash, &max_arrival_index, &best_tip_block_bhh, best_tip_height
        );

        Ok((
            best_tip_consensus_hash,
            best_tip_block_bhh,
            best_tip_height,
            max_arrival_index,
            ret,
        ))
    }

    /// Find the new Stacks block arrivals as of the given tip `tip`, and return the highest chain
    /// tip discovered.
    ///
    /// Used in conjunction with update_new_block_arrivals().
    ///
    /// Returns Ok((
    ///     stacks tip consensus hash,
    ///     stacks tip block header hash,
    ///     stacks tip height,
    /// ))
    fn find_new_block_arrivals(
        &mut self,
        tip: &BlockSnapshot,
    ) -> Result<(ConsensusHash, BlockHeaderHash, u64), db_error> {
        self.inner_find_new_block_arrivals(tip)
            .map(|(ch, bhh, height, _, _)| (ch, bhh, height))
    }

    /// Update the given tip's canonical Stacks block pointer.
    /// Does so on all sortitions of the same height as tip.
    /// Only used in Stacks 2.x
    fn update_new_block_arrivals(
        &mut self,
        tip: &BlockSnapshot,
        best_chh: ConsensusHash,
        best_bhh: BlockHeaderHash,
        best_height: u64,
    ) -> Result<(), db_error> {
        let args = params![
            best_chh,
            best_bhh,
            u64_to_sql(best_height)?,
            u64_to_sql(tip.block_height)?,
        ];

        debug!(
            "Canonical Stacks tip at ({},{}) is {}/{} (height {})",
            &tip.block_height, &tip.burn_header_hash, &best_chh, &best_bhh, best_height
        );
        self.execute("UPDATE snapshots SET canonical_stacks_tip_consensus_hash = ?1, canonical_stacks_tip_hash = ?2, canonical_stacks_tip_height = ?3
                    WHERE block_height = ?4", args)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Find all stacks blocks that were processed since parent_tip had been processed, and generate MARF
    /// key/value pairs for the subset that arrived on ancestor blocks of the parent.  Update the
    /// given parent chain tip to have the correct memoized canonical chain tip present in the fork
    /// it represents.
    fn process_new_block_arrivals(
        &mut self,
        parent_tip: &mut BlockSnapshot,
    ) -> Result<(Vec<String>, Vec<String>), db_error> {
        let mut keys = vec![];
        let mut values = vec![];

        let (
            best_tip_consensus_hash,
            best_tip_block_bhh,
            best_tip_height,
            max_arrival_index,
            new_arrivals,
        ) = self.inner_find_new_block_arrivals(parent_tip)?;

        // generate MARF key/value pairs for new arrivals
        for (block_bhh, height) in new_arrivals.into_iter() {
            keys.push(db_keys::stacks_block_index(&block_bhh));
            values.push(db_keys::stacks_block_index_value(height));
        }

        // update parent tip
        parent_tip.canonical_stacks_tip_consensus_hash = best_tip_consensus_hash;
        parent_tip.canonical_stacks_tip_hash = best_tip_block_bhh;
        parent_tip.canonical_stacks_tip_height = best_tip_height;

        // generate MARF key/value pairs for highest arrival
        keys.push(db_keys::stacks_block_max_arrival_index());
        values.push(db_keys::stacks_block_max_arrival_index_value(
            max_arrival_index,
        ));

        Ok((keys, values))
    }
}

impl ChainstateDB for SortitionDB {
    fn backup(_backup_path: &str) -> Result<(), db_error> {
        return Err(db_error::NotImplemented);
    }
}

#[cfg(test)]
pub mod tests {
    use std::sync::mpsc::sync_channel;
    use std::thread;

    use stacks_common::address::AddressHashMode;
    use stacks_common::types::chainstate::{BlockHeaderHash, StacksAddress, VRFSeed};
    use stacks_common::types::sqlite::NO_PARAMS;
    use stacks_common::util::get_epoch_time_secs;
    use stacks_common::util::hash::{hex_bytes, Hash160};
    use stacks_common::util::vrf::*;

    use super::*;
    use crate::burnchains::affirmation::AffirmationMap;
    use crate::burnchains::bitcoin::address::BitcoinAddress;
    use crate::burnchains::bitcoin::keys::BitcoinPublicKey;
    use crate::burnchains::bitcoin::BitcoinNetworkType;
    use crate::burnchains::tests::affirmation::{make_reward_cycle, make_simple_key_register};
    use crate::burnchains::*;
    use crate::chainstate::burn::operations::leader_block_commit::BURN_BLOCK_MINED_AT_MODULUS;
    use crate::chainstate::burn::operations::{
        BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp,
    };
    use crate::chainstate::burn::ConsensusHash;
    use crate::chainstate::stacks::StacksPublicKey;
    use crate::core::{StacksEpochExtension, *};
    use crate::util_lib::db::Error as db_error;

    impl SortitionHandleTx<'_> {
        /// Update the canonical Stacks tip (testing only)
        pub fn test_update_canonical_stacks_tip(
            &mut self,
            sort_id: &SortitionId,
            consensus_hash: &ConsensusHash,
            stacks_block_hash: &BlockHeaderHash,
            stacks_block_height: u64,
        ) -> Result<(), db_error> {
            self.update_canonical_stacks_tip(
                sort_id,
                consensus_hash,
                stacks_block_hash,
                stacks_block_height,
            )
        }
    }

    impl SortitionDB {
        /// Open a burn database at random tmp dir (used for testing)
        pub fn connect_test(
            first_block_height: u64,
            first_burn_hash: &BurnchainHeaderHash,
        ) -> Result<SortitionDB, db_error> {
            use crate::core::StacksEpochExtension;
            SortitionDB::connect_test_with_epochs(
                first_block_height,
                first_burn_hash,
                StacksEpoch::unit_test(StacksEpochId::Epoch20, first_block_height),
            )
        }

        /// Open a burn database at random tmp dir (used for testing)
        /// But, take a particular epoch configuration
        pub fn connect_test_with_epochs(
            first_block_height: u64,
            first_burn_hash: &BurnchainHeaderHash,
            epochs: EpochList,
        ) -> Result<SortitionDB, db_error> {
            let mut rng = rand::thread_rng();
            let mut buf = [0u8; 32];
            rng.fill_bytes(&mut buf);
            let db_path_dir = format!(
                "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
                to_hex(&buf)
            );

            SortitionDB::connect(
                &db_path_dir,
                first_block_height,
                first_burn_hash,
                get_epoch_time_secs(),
                &epochs,
                PoxConstants::test_default(),
                None,
                true,
            )
        }

        pub fn connect_v1(
            path: &str,
            first_block_height: u64,
            first_burn_hash: &BurnchainHeaderHash,
            first_burn_header_timestamp: u64,
            readwrite: bool,
        ) -> Result<SortitionDB, db_error> {
            let create_flag = match fs::metadata(path) {
                Err(e) => {
                    if e.kind() == ErrorKind::NotFound {
                        // need to create
                        if readwrite {
                            true
                        } else {
                            return Err(db_error::NoDBError);
                        }
                    } else {
                        return Err(db_error::IOError(e));
                    }
                }
                Ok(_md) => false,
            };

            let index_path = db_mkdirs(path)?;
            debug!(
                "Connect/Open {} sortdb '{}' as '{}'",
                if create_flag { "(create)" } else { "" },
                index_path,
                if readwrite { "readwrite" } else { "readonly" }
            );

            let marf = SortitionDB::open_index(&index_path)?;

            let mut db = SortitionDB {
                path: path.to_string(),
                marf,
                readwrite,
                dryrun: false,
                first_block_height,
                first_burn_header_hash: first_burn_hash.clone(),
                pox_constants: PoxConstants::test_default(),
            };

            if create_flag {
                // instantiate!
                db.instantiate_v1(
                    first_block_height,
                    first_burn_hash,
                    first_burn_header_timestamp,
                )?;
            } else {
                // validate -- must contain the given first block and first block hash
                let snapshot = SortitionDB::get_first_block_snapshot(db.conn())?;
                if !snapshot.is_initial()
                    || snapshot.block_height != first_block_height
                    || snapshot.burn_header_hash != *first_burn_hash
                {
                    error!("Invalid genesis snapshot: sn.is_initial = {}, sn.block_height = {}, sn.burn_hash = {}, expect.block_height = {}, expect.burn_hash = {}",
                           snapshot.is_initial(), snapshot.block_height, &snapshot.burn_header_hash, first_block_height, first_burn_hash);
                    return Err(db_error::Corruption);
                }
            }

            Ok(db)
        }

        fn instantiate_v1(
            &mut self,
            first_block_height: u64,
            first_burn_header_hash: &BurnchainHeaderHash,
            first_burn_header_timestamp: u64,
        ) -> Result<(), db_error> {
            debug!("Instantiate SortDB");

            sql_pragma(self.conn(), "journal_mode", &"WAL")?;
            sql_pragma(self.conn(), "foreign_keys", &true)?;

            let mut db_tx = SortitionHandleTx::begin(self, &SortitionId::sentinel())?;

            // create first (sentinel) snapshot
            debug!("Make first snapshot");
            let mut first_snapshot = BlockSnapshot::initial(
                first_block_height,
                first_burn_header_hash,
                first_burn_header_timestamp,
            );

            assert!(first_snapshot.parent_burn_header_hash != first_snapshot.burn_header_hash);
            assert_eq!(
                first_snapshot.parent_burn_header_hash,
                BurnchainHeaderHash::sentinel()
            );

            for row_text in SORTITION_DB_INITIAL_SCHEMA {
                db_tx.execute_batch(row_text)?;
            }

            db_tx.execute(
                "INSERT OR REPLACE INTO db_config (version) VALUES (?1)",
                &[&"1"],
            )?;

            db_tx.instantiate_index()?;

            let mut first_sn = first_snapshot.clone();
            first_sn.sortition_id = SortitionId::sentinel();
            let (index_root, pox_payout) =
                db_tx.index_add_fork_info(&mut first_sn, &first_snapshot, &[], None, None, None)?;
            first_snapshot.index_root = index_root;

            // manually insert the first block snapshot in instantiate_v1 testing code, because
            //  SCHEMA_8 adds a new column
            let pox_payouts_json = serde_json::to_string(&pox_payout)
                .expect("FATAL: could not encode `total_pox_payouts` as JSON");

            let args = params![
                u64_to_sql(first_snapshot.block_height)?,
                first_snapshot.burn_header_hash,
                u64_to_sql(first_snapshot.burn_header_timestamp)?,
                first_snapshot.parent_burn_header_hash,
                first_snapshot.consensus_hash,
                first_snapshot.ops_hash,
                first_snapshot.total_burn.to_string(),
                first_snapshot.sortition,
                first_snapshot.sortition_hash,
                first_snapshot.winning_block_txid,
                first_snapshot.winning_stacks_block_hash,
                first_snapshot.index_root,
                u64_to_sql(first_snapshot.num_sortitions)?,
                first_snapshot.stacks_block_accepted,
                u64_to_sql(first_snapshot.stacks_block_height)?,
                u64_to_sql(first_snapshot.arrival_index)?,
                u64_to_sql(first_snapshot.canonical_stacks_tip_height)?,
                first_snapshot.canonical_stacks_tip_hash,
                first_snapshot.canonical_stacks_tip_consensus_hash,
                first_snapshot.sortition_id,
                first_snapshot.parent_sortition_id,
                first_snapshot.pox_valid,
                first_snapshot.accumulated_coinbase_ustx.to_string(),
                pox_payouts_json,
            ];

            db_tx.execute("INSERT INTO snapshots \
                          (block_height, burn_header_hash, burn_header_timestamp, parent_burn_header_hash, consensus_hash, ops_hash, total_burn, sortition, sortition_hash, winning_block_txid, winning_stacks_block_hash, index_root, num_sortitions, \
                          stacks_block_accepted, stacks_block_height, arrival_index, canonical_stacks_tip_height, canonical_stacks_tip_hash, canonical_stacks_tip_consensus_hash, sortition_id, parent_sortition_id, pox_valid, accumulated_coinbase_ustx, \
                          pox_payouts) \
                          VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, ?20, ?21, ?22, ?23, ?24)", args)?;

            db_tx.store_transition_ops(
                &first_snapshot.sortition_id,
                &BurnchainStateTransition::noop(),
            )?;

            db_tx.commit()?;
            Ok(())
        }

        pub fn test_get_next_block_recipients(
            &mut self,
            burnchain: &Burnchain,
            next_pox_info: Option<&RewardCycleInfo>,
        ) -> Result<Option<RewardSetInfo>, BurnchainError> {
            let parent_snapshot = SortitionDB::get_canonical_burn_chain_tip(self.conn())?;
            self.get_next_block_recipients(burnchain, &parent_snapshot, next_pox_info)
        }

        pub fn set_canonical_stacks_chain_tip(
            conn: &Connection,
            ch: &ConsensusHash,
            bhh: &BlockHeaderHash,
            height: u64,
        ) -> Result<(), db_error> {
            let tip = SortitionDB::get_canonical_burn_chain_tip(conn)?;
            let args = params![ch, bhh, u64_to_sql(height)?, tip.sortition_id];
            conn.execute("UPDATE snapshots SET canonical_stacks_tip_consensus_hash = ?1, canonical_stacks_tip_hash = ?2, canonical_stacks_tip_height = ?3
                        WHERE sortition_id = ?4", args)
                .map_err(db_error::SqliteError)?;
            Ok(())
        }

        /// Given the last_tenure_id (e.g. in a block-commit in Nakamoto), find its sortition in the
        /// given sortition fork.
        pub fn get_block_snapshot_for_winning_nakamoto_tenure(
            ic: &SortitionDBConn,
            tip: &SortitionId,
            last_tenure_id: &StacksBlockId,
        ) -> Result<Option<BlockSnapshot>, db_error> {
            let block_hash = BlockHeaderHash(last_tenure_id.0.clone());
            Self::get_block_snapshot_for_winning_stacks_block(ic, tip, &block_hash)
        }

        /// Get a blockstack burnchain operation by txid
        pub fn get_burnchain_transaction(
            conn: &Connection,
            txid: &Txid,
        ) -> Result<Option<BlockstackOperationType>, db_error> {
            // leader key?
            let leader_key_sql = "SELECT * FROM leader_keys WHERE txid = ?1 LIMIT 1";
            let args = [&txid];

            let leader_key_res = query_row_panic(conn, &leader_key_sql, &args, || {
                "Multiple leader keys with same txid".to_string()
            })?;
            if let Some(leader_key) = leader_key_res {
                return Ok(Some(BlockstackOperationType::LeaderKeyRegister(leader_key)));
            }

            // block commit?
            let block_commit_sql = "SELECT * FROM block_commits WHERE txid = ?1 LIMIT 1";

            let block_commit_res = query_row_panic(conn, &block_commit_sql, &args, || {
                "Multiple block commits with same txid".to_string()
            })?;
            if let Some(block_commit) = block_commit_res {
                return Ok(Some(BlockstackOperationType::LeaderBlockCommit(
                    block_commit,
                )));
            }

            Ok(None)
        }

        /// Load up all stacks chain tips, in ascending order by block height.  Great for testing!
        pub fn get_all_stacks_chain_tips(
            &self,
        ) -> Result<Vec<(SortitionId, ConsensusHash, BlockHeaderHash, u64)>, db_error> {
            let sql = "SELECT * FROM stacks_chain_tips ORDER BY block_height ASC";
            let mut stmt = self.conn().prepare(sql)?;
            let mut qry = stmt.query(NO_PARAMS)?;
            let mut ret = vec![];
            while let Some(row) = qry.next()? {
                let sort_id: SortitionId = row.get("sortition_id")?;
                let consensus_hash: ConsensusHash = row.get("consensus_hash")?;
                let block_hash: BlockHeaderHash = row.get("block_hash")?;
                let block_height_i64: i64 = row.get("block_height")?;
                let block_height =
                    u64::try_from(block_height_i64).map_err(|_| db_error::ParseError)?;
                ret.push((sort_id, consensus_hash, block_hash, block_height));
            }
            Ok(ret)
        }

        /// Get the last block-commit from a given sender
        pub fn get_last_block_commit_by_sender(
            conn: &DBConn,
            sender: &BurnchainSigner,
        ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
            let apparent_sender_str =
                serde_json::to_string(sender).map_err(db_error::SerializationError)?;
            let sql = "SELECT * FROM block_commits WHERE apparent_sender = ?1 ORDER BY block_height DESC LIMIT 1";
            let args = params![apparent_sender_str];
            query_row(conn, sql, args)
        }
    }

    #[test]
    fn test_instantiate() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let _db = SortitionDB::connect_test(123, &first_burn_hash).unwrap();
    }

    #[test]
    fn test_v1_to_v2_migration() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let first_block_height = 123;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        // create a v1 sortition DB
        let db = SortitionDB::connect_v1(
            &db_path_dir,
            first_block_height,
            &first_burn_hash,
            get_epoch_time_secs(),
            true,
        )
        .unwrap();
        let res = SortitionDB::get_stacks_epoch(db.conn(), first_block_height);
        assert!(res.is_err());
        assert!(format!("{:?}", res).contains("no such table: epochs"));

        assert!(SortitionDB::open(&db_path_dir, true, PoxConstants::test_default()).is_err());

        // create a v2 sortition DB at the same path as the v1 DB.
        // the schema migration should be successfully applied, and the epochs table should exist.
        let db = SortitionDB::connect(
            &db_path_dir,
            first_block_height,
            &first_burn_hash,
            get_epoch_time_secs(),
            &StacksEpoch::unit_test_2_05(first_block_height),
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
        // assert that an epoch is returned
        SortitionDB::get_stacks_epoch(db.conn(), first_block_height)
            .expect("Database should not error querying epochs")
            .expect("Database should have an epoch entry");

        assert!(SortitionDB::open(&db_path_dir, true, PoxConstants::test_default()).is_ok());
    }

    #[test]
    fn test_tx_begin_end() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(123, &first_burn_hash).unwrap();
        let tx = db.tx_begin().unwrap();
        tx.commit().unwrap();
    }

    pub fn test_append_snapshot_with_winner(
        db: &mut SortitionDB,
        next_hash: BurnchainHeaderHash,
        block_ops: &[BlockstackOperationType],
        parent_sn: Option<BlockSnapshot>,
        winning_block_commit: Option<LeaderBlockCommitOp>,
    ) -> BlockSnapshot {
        let mut sn = match parent_sn {
            Some(sn) => sn,
            None => SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap(),
        };

        let mut tx = SortitionHandleTx::begin(db, &sn.sortition_id).unwrap();

        let sn_parent = sn.clone();
        sn.parent_burn_header_hash = sn.burn_header_hash.clone();
        sn.parent_sortition_id = sn.sortition_id.clone();
        sn.burn_header_hash = next_hash;
        sn.block_height += 1;
        sn.num_sortitions += 1;
        sn.sortition_id = SortitionId::stubbed(&sn.burn_header_hash);
        sn.consensus_hash = ConsensusHash(Hash160::from_data(&sn.consensus_hash.0).0);

        if let Some(cmt) = winning_block_commit {
            sn.sortition = true;
            sn.winning_stacks_block_hash = cmt.block_header_hash;
            sn.winning_block_txid = cmt.txid;
        }

        let index_root = tx
            .append_chain_tip_snapshot(&sn_parent, &sn, block_ops, &[], None, None, None)
            .unwrap();
        sn.index_root = index_root;

        tx.commit().unwrap();

        sn
    }

    pub fn test_append_snapshot(
        db: &mut SortitionDB,
        next_hash: BurnchainHeaderHash,
        block_ops: &[BlockstackOperationType],
    ) -> BlockSnapshot {
        test_append_snapshot_with_winner(db, next_hash, block_ops, None, None)
    }

    #[test]
    fn test_insert_leader_key() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![1, 2, 3, 4, 5],

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &[BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        {
            let ic = db.index_conn();
            let leader_key_opt = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex,
                &snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_opt.is_some());
            assert_eq!(leader_key_opt.unwrap(), leader_key);
        }

        let new_snapshot = test_append_snapshot(&mut db, BurnchainHeaderHash([0x02; 32]), &[]);

        {
            let ic = db.index_conn();
            let leader_key_opt = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex,
                &new_snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_opt.is_some());
            assert_eq!(leader_key_opt.unwrap(), leader_key);

            let leader_key_none = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex + 1,
                &new_snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_none.is_none());
        }
    }

    #[test]
    fn test_insert_block_commit() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![1, 2, 3, 4, 5],

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let block_commit = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 0x43424140,
            parent_vtxindex: 0x5150,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],

            commit_outs: vec![],
            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 2,
            burn_parent_modulus: ((block_height + 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
            treatment: vec![],
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &[BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        // test get_consumed_leader_keys()
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }

        let snapshot_consumed = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                block_commit.clone(),
            )],
        );

        {
            let res_block_commits =
                SortitionDB::get_block_commits_by_block(db.conn(), &snapshot_consumed.sortition_id)
                    .unwrap();
            assert_eq!(res_block_commits.len(), 1);
            assert_eq!(res_block_commits[0], block_commit);
        }

        // advance and get parent
        let empty_snapshot = test_append_snapshot(&mut db, BurnchainHeaderHash([0x05; 32]), &[]);

        // test get_block_commit_parent()
        {
            let ic = db.index_conn();
            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 2,
                block_commit.vtxindex,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_some());
            assert_eq!(parent.unwrap(), block_commit);

            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 3,
                block_commit.vtxindex,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_none());

            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 2,
                block_commit.vtxindex + 1,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_none());
        }

        // test get_block_commit()
        {
            let handle = db.index_handle(&empty_snapshot.sortition_id);
            let commit = handle
                .get_block_commit_by_txid(&snapshot_consumed.sortition_id, &block_commit.txid)
                .unwrap();
            assert!(commit.is_some());
            assert_eq!(commit.unwrap(), block_commit);

            let bad_txid = Txid::from_bytes_be(
                &hex_bytes("4c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap();
            let commit = handle
                .get_block_commit_by_txid(&snapshot_consumed.sortition_id, &bad_txid)
                .unwrap();
            assert!(commit.is_none());
        }

        // sortition ID is memoized, or absent
        {
            assert_eq!(
                SortitionDB::get_block_commit_parent_sortition_id(
                    db.conn(),
                    &block_commit.txid,
                    &snapshot_consumed.sortition_id
                )
                .unwrap(),
                Some(SortitionId([0x00; 32]))
            );
        }

        // test get_consumed_leader_keys() (should be doable at any subsequent index root)
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&empty_snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }

        // make a fork between the leader key and block commit, and verify that the key is
        // unconsumed
        let fork_snapshot = {
            let mut sn = SortitionDB::get_block_snapshot(db.conn(), &snapshot.sortition_id)
                .unwrap()
                .unwrap();
            let next_hash = BurnchainHeaderHash([0x13; 32]);
            let mut tx = SortitionHandleTx::begin(&mut db, &sn.sortition_id).unwrap();

            let sn_parent = sn.clone();
            sn.parent_burn_header_hash = sn.burn_header_hash.clone();
            sn.sortition_id = SortitionId(next_hash.0.clone());
            sn.parent_sortition_id = sn_parent.sortition_id.clone();
            sn.burn_header_hash = next_hash;
            sn.block_height += 1;
            sn.num_sortitions += 1;
            sn.consensus_hash = ConsensusHash([0x23; 20]);

            let index_root = tx
                .append_chain_tip_snapshot(&sn_parent, &sn, &[], &[], None, None, None)
                .unwrap();
            sn.index_root = index_root;

            tx.commit().unwrap();

            sn
        };

        // test get_consumed_leader_keys() and is_leader_key_consumed() against this new fork
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&fork_snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }
    }

    #[test]
    fn has_VRF_public_key() {
        let public_key = VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap();
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: public_key.clone(),
            memo: vec![1, 2, 3, 4, 5],

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 2,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let no_key_snapshot = test_append_snapshot(&mut db, BurnchainHeaderHash([0x01; 32]), &[]);

        let has_key_before = {
            let mut ic = SortitionHandleTx::begin(&mut db, &no_key_snapshot.sortition_id).unwrap();
            ic.has_VRF_public_key(&public_key).unwrap()
        };

        assert!(!has_key_before);

        let key_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &[BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let has_key_after = {
            let mut ic = SortitionHandleTx::begin(&mut db, &key_snapshot.sortition_id).unwrap();
            ic.has_VRF_public_key(&public_key).unwrap()
        };

        assert!(has_key_after);
    }

    #[test]
    fn is_fresh_consensus_hash() {
        let consensus_hash_lifetime = 24;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..255 {
                let sortition_id = SortitionId([
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i,
                ]);
                let parent_sortition_id = if i == 0 {
                    last_snapshot.sortition_id.clone()
                } else {
                    SortitionId([
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        i - 1,
                    ])
                };

                let mut tx = SortitionHandleTx::begin(&mut db, &parent_sortition_id).unwrap();
                let snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: i as u64 + 1,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i,
                    ])
                    .unwrap(),
                    sortition_id,
                    parent_sortition_id,
                    parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        (if i == 0 { 0x10 } else { 0 }) as u8,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        (if i == 0 { 0xff } else { i - 1 }),
                    ])
                    .unwrap(),
                    consensus_hash: ConsensusHash::from_bytes(&[
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        i + 1,
                    ])
                    .unwrap(),
                    ops_hash: OpsHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i,
                    ])
                    .unwrap(),
                    total_burn: i as u64,
                    sortition: true,
                    sortition_hash: SortitionHash::initial(),
                    winning_block_txid: Txid::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    winning_stacks_block_hash: BlockHeaderHash::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    index_root: TrieHash::from_empty_data(),
                    num_sortitions: i as u64 + 1,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    miner_pk_hash: None,
                };
                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;
                tx.commit().unwrap();
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let ch_fresh = ConsensusHash::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255,
        ])
        .unwrap();
        let ch_oldest_fresh = ConsensusHash::from_bytes(&[
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            (255 - consensus_hash_lifetime) as u8,
        ])
        .unwrap();
        let ch_newest_stale = ConsensusHash::from_bytes(&[
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            (255 - consensus_hash_lifetime - 1) as u8,
        ])
        .unwrap();
        let ch_missing = ConsensusHash::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 255,
        ])
        .unwrap();

        let mut ic = SortitionHandleTx::begin(&mut db, &tip.sortition_id).unwrap();
        let fresh_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_fresh)
            .unwrap();

        assert!(fresh_check);

        let oldest_fresh_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_oldest_fresh)
            .unwrap();

        assert!(oldest_fresh_check);

        let newest_stale_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_newest_stale)
            .unwrap();

        assert!(!newest_stale_check);

        let missing_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_missing)
            .unwrap();

        assert!(!missing_check);
    }

    #[test]
    fn get_consensus_at() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..256u64 {
                let sortition_id = SortitionId([
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i as u8,
                ]);
                let parent_sortition_id = if i == 0 {
                    last_snapshot.sortition_id.clone()
                } else {
                    SortitionId([
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        (i - 1) as u8,
                    ])
                };

                let mut tx = SortitionHandleTx::begin(&mut db, &parent_sortition_id).unwrap();
                let snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: i + 1,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    sortition_id,
                    parent_sortition_id,
                    parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        (if i == 0 { 0x10 } else { 0 }) as u8,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        (if i == 0 { 0xff } else { i - 1 }) as u8,
                    ])
                    .unwrap(),
                    consensus_hash: ConsensusHash::from_bytes(&[
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        ((i + 1) / 256) as u8,
                        (i + 1) as u8,
                    ])
                    .unwrap(),
                    ops_hash: OpsHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    total_burn: i,
                    sortition: true,
                    sortition_hash: SortitionHash::initial(),
                    winning_block_txid: Txid::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    winning_stacks_block_hash: BlockHeaderHash::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    index_root: TrieHash::from_empty_data(),
                    num_sortitions: i + 1,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    miner_pk_hash: None,
                };
                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;
                // should succeed within the tx
                let ch = tx.get_consensus_at(i + 1).unwrap().unwrap();
                assert_eq!(ch, last_snapshot.consensus_hash);

                tx.commit().unwrap();
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        for i in 0..256 {
            // should succeed within the conn
            let ic = db.index_handle(&tip.sortition_id);
            let expected_ch = ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
            ])
            .unwrap();
            let ch = ic.get_consensus_at(i).unwrap().unwrap();
            assert_eq!(ch, expected_ch);
        }
    }

    #[test]
    fn get_block_burn_amount() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![1, 2, 3, 4, 5],

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let block_commit = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 0x43424140,
            parent_vtxindex: 0x4342,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 2,
            burn_parent_modulus: ((block_height + 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
            treatment: vec![],
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let key_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &[BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let commit_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                block_commit.clone(),
            )],
        );

        {
            let burn_amt = SortitionDB::get_block_burn_amount(db.conn(), &commit_snapshot).unwrap();
            assert_eq!(burn_amt, block_commit.burn_fee);

            let no_burn_amt = SortitionDB::get_block_burn_amount(db.conn(), &key_snapshot).unwrap();
            assert_eq!(no_burn_amt, 0);
        }
    }

    #[test]
    fn get_last_snapshot_with_sortition() {
        let block_height = 123;
        let total_burn_sortition = 100;
        let total_burn_no_sortition = 200;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let mut first_snapshot = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: block_height - 2,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: first_burn_hash.clone(),
            sortition_id: SortitionId(first_burn_hash.0.clone()),
            parent_sortition_id: SortitionId(first_burn_hash.0.clone()),
            parent_burn_header_hash: BurnchainHeaderHash([0xff; 32]),
            consensus_hash: ConsensusHash::from_hex("0000000000000000000000000000000000000000")
                .unwrap(),
            ops_hash: OpsHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            total_burn: 0,
            sortition: true,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            winning_stacks_block_hash: BlockHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            index_root: TrieHash([0u8; 32]),
            num_sortitions: 0,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
            miner_pk_hash: None,
        };

        let mut snapshot_with_sortition = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ])
            .unwrap(),
            sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ]),
            parent_sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ]),
            parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            consensus_hash: ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            ])
            .unwrap(),
            ops_hash: OpsHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            total_burn: total_burn_sortition,
            sortition: true,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000001",
            )
            .unwrap(),
            winning_stacks_block_hash: BlockHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000001",
            )
            .unwrap(),
            index_root: TrieHash([1u8; 32]),
            num_sortitions: 1,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
            miner_pk_hash: None,
        };

        let snapshot_without_sortition = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: block_height - 1,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ]),
            parent_sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ]),
            parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ])
            .unwrap(),
            consensus_hash: ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
            ])
            .unwrap(),
            ops_hash: OpsHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ])
            .unwrap(),
            total_burn: total_burn_no_sortition,
            sortition: false,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000002",
            )
            .unwrap(),
            winning_stacks_block_hash: BlockHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000002",
            )
            .unwrap(),
            index_root: TrieHash([2u8; 32]),
            num_sortitions: 0,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
            miner_pk_hash: None,
        };

        let mut db = SortitionDB::connect_test(block_height - 2, &first_burn_hash).unwrap();

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let initial_snapshot = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height - 2)
                .unwrap()
        };

        first_snapshot.index_root = initial_snapshot.index_root.clone();
        first_snapshot.burn_header_timestamp = initial_snapshot.burn_header_timestamp;
        assert_eq!(initial_snapshot, first_snapshot);

        {
            let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            let mut tx = SortitionHandleTx::begin(&mut db, &chain_tip.sortition_id).unwrap();

            tx.append_chain_tip_snapshot(
                &chain_tip,
                &snapshot_without_sortition,
                &[],
                &[],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let mut next_snapshot = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height - 1)
                .unwrap()
        };

        next_snapshot.index_root = initial_snapshot.index_root.clone();
        next_snapshot.burn_header_timestamp = initial_snapshot.burn_header_timestamp;
        assert_eq!(initial_snapshot, next_snapshot);

        {
            let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            let mut tx = SortitionHandleTx::begin(&mut db, &chain_tip.sortition_id).unwrap();

            tx.append_chain_tip_snapshot(
                &chain_tip,
                &snapshot_with_sortition,
                &[],
                &[],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let next_snapshot_2 = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height).unwrap()
        };

        snapshot_with_sortition.index_root = next_snapshot_2.index_root.clone();
        snapshot_with_sortition.burn_header_timestamp = next_snapshot_2.burn_header_timestamp;
        assert_eq!(snapshot_with_sortition, next_snapshot_2);
    }

    /// Verify that the snapshots in a fork are well-formed -- i.e. the block heights are
    /// sequential and the parent block hash of the ith block is equal to the block hash of the
    /// (i-1)th block.
    fn verify_fork_integrity(db: &mut SortitionDB, tip: &SortitionId) {
        let mut child = SortitionDB::get_block_snapshot(db.conn(), tip)
            .unwrap()
            .unwrap();

        let initial = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        test_debug!(
            "Verify from {},hash={},parent={} back to {},hash={},parent={}",
            child.block_height,
            child.burn_header_hash,
            child.parent_burn_header_hash,
            initial.block_height,
            initial.burn_header_hash,
            initial.parent_burn_header_hash
        );

        while child.block_height > initial.block_height {
            let parent = {
                let ic = db.index_conn();
                SortitionDB::get_ancestor_snapshot(&ic, child.block_height - 1, &child.sortition_id)
                    .unwrap()
                    .unwrap()
            };

            test_debug!(
                "Verify {} == {} - 1 and hash={},parent_hash={} == parent={}",
                parent.block_height,
                child.block_height,
                child.burn_header_hash,
                parent.burn_header_hash,
                child.parent_burn_header_hash
            );

            assert_eq!(parent.block_height, child.block_height - 1);
            assert_eq!(parent.burn_header_hash, child.parent_burn_header_hash);

            child = parent.clone();
        }

        assert_eq!(child, initial);
    }

    #[test]
    fn test_chain_reorg() {
        // Create a set of forks that looks like this:
        // 0-1-2-3-4-5-6-7-8-9 (fork 0)
        //  \
        //   1-2-3-4-5-6-7-8-9 (fork 1)
        //    \
        //     2-3-4-5-6-7-8-9 (fork 2)
        //      \
        //       3-4-5-6-7-8-9 (fork 3)
        //
        //    ...etc...
        //
        // Then, append a block to fork 9, and confirm that it switches places with fork 0.
        // Append 2 blocks to fork 8, and confirm that it switches places with fork 0.
        // Append 3 blocks to fork 7, and confirm that it switches places with fork 0.
        // ... etc.
        //
        let first_burn_hash = BurnchainHeaderHash([0x00; 32]);
        let first_block_height = 100;

        let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();

        // make an initial fork
        let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        for i in 0..10 {
            let mut next_snapshot = last_snapshot.clone();

            next_snapshot.block_height += 1;
            next_snapshot.num_sortitions += 1;
            next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
            next_snapshot.burn_header_hash = BurnchainHeaderHash([
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                i + 1,
            ]);
            next_snapshot.sortition_id = SortitionId([
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                i + 1,
            ]);
            next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
            next_snapshot.consensus_hash = ConsensusHash([
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                i + 1,
            ]);

            let mut tx = SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
            tx.append_chain_tip_snapshot(
                &last_snapshot,
                &next_snapshot,
                &[],
                &[],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();

            last_snapshot = next_snapshot.clone();
        }

        test_debug!("----- make forks -----");

        // make other forks
        for i in 0..9 {
            let parent_block_hash = if i == 0 {
                [0u8; 32]
            } else {
                let mut tmp = [
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    (i + 1) as u8,
                ];
                tmp[i - 1] = 1;
                tmp
            };

            let parent_block = SortitionId(parent_block_hash);
            test_debug!(
                "----- build fork off of parent {} (i = {}) -----",
                &parent_block,
                i
            );

            let mut last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &parent_block)
                .unwrap()
                .unwrap();

            let initial_block_height = last_snapshot.block_height;
            let initial_num_sortitions = last_snapshot.num_sortitions;

            let mut next_snapshot = last_snapshot.clone();

            for j in (i + 1)..10 {
                let mut block_hash = [
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    (j + 1) as u8,
                ];
                block_hash[i] = (j - i) as u8;

                next_snapshot.block_height = initial_block_height + (j - i) as u64;
                next_snapshot.num_sortitions = initial_num_sortitions + (j - i) as u64;
                next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
                next_snapshot.sortition_id = SortitionId(block_hash.clone());
                next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
                next_snapshot.burn_header_hash = BurnchainHeaderHash(block_hash);
                next_snapshot.consensus_hash = ConsensusHash([
                    1,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    j as u8,
                    (i + 1) as u8,
                ]);

                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                let next_index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &next_snapshot,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();

                next_snapshot.index_root = next_index_root;
                last_snapshot = next_snapshot.clone();
            }

            test_debug!(
                "----- made fork {} (i = {}) -----",
                &next_snapshot.burn_header_hash,
                i
            );
        }

        test_debug!("----- grow forks -----");

        let mut all_chain_tips = vec![];

        // grow each fork so it overtakes the currently-canonical fork
        for i in 0..9 {
            let mut last_block_hash = [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 10,
            ];
            last_block_hash[i] = (9 - i) as u8;
            let last_block = SortitionId(last_block_hash);

            test_debug!("----- grow fork {} (i = {}) -----", &last_block, i);

            let mut last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &last_block)
                .unwrap()
                .unwrap();

            let initial_block_height = last_snapshot.block_height;
            let mut next_snapshot = last_snapshot.clone();

            // grow the fork up to the length of the previous fork
            for j in 0..((i + 1) as u64) {
                next_snapshot = last_snapshot.clone();

                let mut next_block_hash_vec = last_snapshot.burn_header_hash.as_bytes().to_vec();
                next_block_hash_vec[0] += 1;
                let mut next_block_hash = [0u8; 32];
                next_block_hash.copy_from_slice(&next_block_hash_vec[..]);

                next_snapshot.block_height = last_snapshot.block_height + 1;
                next_snapshot.num_sortitions = last_snapshot.num_sortitions + 1;
                next_snapshot.parent_burn_header_hash = last_snapshot.burn_header_hash.clone();
                next_snapshot.sortition_id = SortitionId(next_block_hash.clone());
                next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
                next_snapshot.burn_header_hash = BurnchainHeaderHash(next_block_hash);
                next_snapshot.consensus_hash = ConsensusHash([
                    2,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                    j as u8,
                    (i + 1) as u8,
                ]);

                let next_index_root = {
                    let mut tx =
                        SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                    let next_index_root = tx
                        .append_chain_tip_snapshot(
                            &last_snapshot,
                            &next_snapshot,
                            &[],
                            &[],
                            None,
                            None,
                            None,
                        )
                        .unwrap();
                    tx.commit().unwrap();
                    next_index_root
                };

                last_snapshot =
                    SortitionDB::get_block_snapshot(db.conn(), &next_snapshot.sortition_id)
                        .unwrap()
                        .unwrap();
            }

            // make the fork exceed the canonical chain tip
            next_snapshot = last_snapshot.clone();

            let mut next_block_hash_vec = last_snapshot.burn_header_hash.as_bytes().to_vec();
            next_block_hash_vec[0] = 0xff;
            let mut next_block_hash = [0u8; 32];
            next_block_hash.copy_from_slice(&next_block_hash_vec[..]);

            next_snapshot.block_height += 1;
            next_snapshot.num_sortitions += 1;
            next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
            next_snapshot.sortition_id = SortitionId(next_block_hash.clone());
            next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
            next_snapshot.burn_header_hash = BurnchainHeaderHash(next_block_hash);
            next_snapshot.consensus_hash =
                ConsensusHash(Hash160::from_data(&next_snapshot.consensus_hash.0).0);

            let next_index_root = {
                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                let next_index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &next_snapshot,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();
                next_index_root
            };

            next_snapshot.index_root = next_index_root;

            let mut expected_tip = next_snapshot.clone();
            expected_tip.index_root = next_index_root;

            let canonical_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            assert_eq!(canonical_tip, expected_tip);

            verify_fork_integrity(&mut db, &canonical_tip.sortition_id);
            all_chain_tips.push(canonical_tip.sortition_id.clone());
        }

        for tip_header_hash in all_chain_tips.iter() {
            verify_fork_integrity(&mut db, tip_header_hash);
        }
    }

    #[test]
    fn test_get_stacks_header_hashes() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            let mut total_burn = 0;
            let mut total_sortitions = 0;
            for i in 0..256 {
                let snapshot_row = if i % 3 == 0 {
                    BlockSnapshot {
                        accumulated_coinbase_ustx: 0,
                        pox_valid: true,
                        block_height: i + 1,
                        burn_header_timestamp: get_epoch_time_secs(),
                        burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        sortition_id: SortitionId([
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ]),
                        parent_sortition_id: last_snapshot.sortition_id.clone(),
                        parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            (if i == 0 { 0x10 } else { 0 }) as u8,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            (if i == 0 { 0xff } else { i - 1 }) as u8,
                        ])
                        .unwrap(),
                        consensus_hash: ConsensusHash::from_bytes(&[
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        ops_hash: OpsHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        total_burn,
                        sortition: false,
                        sortition_hash: SortitionHash([(i as u8); 32]),
                        winning_block_txid: Txid([(i as u8); 32]),
                        winning_stacks_block_hash: BlockHeaderHash([0u8; 32]),
                        index_root: TrieHash::from_empty_data(),
                        num_sortitions: total_sortitions,
                        stacks_block_accepted: false,
                        stacks_block_height: 0,
                        arrival_index: 0,
                        canonical_stacks_tip_height: 0,
                        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                        miner_pk_hash: None,
                    }
                } else {
                    total_burn += 1;
                    total_sortitions += 1;
                    BlockSnapshot {
                        accumulated_coinbase_ustx: 0,
                        pox_valid: true,
                        block_height: i + 1,
                        burn_header_timestamp: get_epoch_time_secs(),
                        burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        sortition_id: SortitionId([
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ]),
                        parent_sortition_id: last_snapshot.sortition_id.clone(),
                        parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            (if i == 0 { 0x10 } else { 0 }) as u8,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            0,
                            (if i == 0 { 0xff } else { i - 1 }) as u8,
                        ])
                        .unwrap(),
                        consensus_hash: ConsensusHash::from_bytes(&[
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        ops_hash: OpsHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        total_burn,
                        sortition: true,
                        sortition_hash: SortitionHash([(i as u8); 32]),
                        winning_block_txid: Txid([(i as u8); 32]),
                        winning_stacks_block_hash: BlockHeaderHash([(i as u8); 32]),
                        index_root: TrieHash::from_empty_data(),
                        num_sortitions: total_sortitions,
                        stacks_block_accepted: false,
                        stacks_block_height: 0,
                        arrival_index: 0,
                        canonical_stacks_tip_height: 0,
                        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                        miner_pk_hash: None,
                    }
                };

                // NOTE: we don't care about VRF keys or block commits here

                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();

                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;

                // should succeed within the tx
                let ch = tx
                    .get_consensus_at(i + 1)
                    .unwrap()
                    .unwrap_or(ConsensusHash::empty());
                assert_eq!(ch, last_snapshot.consensus_hash);

                tx.commit().unwrap();
            }
        }

        let canonical_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        let mut cache = BlockHeaderCache::new();

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(256, &canonical_tip.consensus_hash, &cache)
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            assert_eq!(hashes.len(), 256);
            for i in 0..256 {
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    256,
                    &canonical_tip.consensus_hash,
                    &BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(256, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 256);
            assert_eq!(cached_hashes.len(), 256);
            for i in 0..256 {
                assert_eq!(cached_hashes[i], hashes[i]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    192,
                    &canonical_tip.consensus_hash,
                    &BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(192, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 192);
            assert_eq!(cached_hashes.len(), 192);
            for i in 64..256 {
                assert_eq!(cached_hashes[i - 64], hashes[i - 64]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i - 64];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                assert!(cache.contains_key(consensus_hash));
                assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    257,
                    &canonical_tip.consensus_hash,
                    &BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(257, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 256);
            assert_eq!(cached_hashes.len(), 256);
            for i in 0..256 {
                assert_eq!(cached_hashes[i], hashes[i]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let err = ic
                .get_stacks_header_hashes(256, &ConsensusHash([0x03; 20]), &BlockHeaderCache::new())
                .unwrap_err();
            match err {
                db_error::NotFoundError => {}
                _ => {
                    eprintln!("Got wrong error: {:?}", &err);
                    assert!(false);
                    unreachable!();
                }
            }

            let err = ic
                .get_stacks_header_hashes(256, &ConsensusHash([0x03; 20]), &cache)
                .unwrap_err();
            match err {
                db_error::NotFoundError => {}
                _ => {
                    eprintln!("Got wrong error: {:?}", &err);
                    assert!(false);
                    unreachable!();
                }
            }
        }
    }

    pub fn make_fork_run(
        db: &mut SortitionDB,
        start_snapshot: &BlockSnapshot,
        length: u64,
        bit_pattern: u8,
    ) -> Vec<BlockSnapshot> {
        let mut last_snapshot = start_snapshot.clone();
        let mut new_snapshots = vec![];
        for i in last_snapshot.block_height..(last_snapshot.block_height + length) {
            let snapshot = BlockSnapshot {
                accumulated_coinbase_ustx: 0,
                pox_valid: true,
                block_height: last_snapshot.block_height + 1,
                burn_header_timestamp: get_epoch_time_secs(),
                burn_header_hash: BurnchainHeaderHash([(i as u8) | bit_pattern; 32]),
                sortition_id: SortitionId([(i as u8) | bit_pattern; 32]),
                parent_sortition_id: last_snapshot.sortition_id.clone(),
                parent_burn_header_hash: last_snapshot.burn_header_hash.clone(),
                consensus_hash: ConsensusHash([((i + 1) as u8) | bit_pattern; 20]),
                ops_hash: OpsHash([(i as u8) | bit_pattern; 32]),
                total_burn: 0,
                sortition: true,
                sortition_hash: SortitionHash([(i as u8) | bit_pattern; 32]),
                winning_block_txid: Txid([(i as u8) | bit_pattern; 32]),
                winning_stacks_block_hash: BlockHeaderHash([(i as u8) | bit_pattern; 32]),
                index_root: TrieHash([0u8; 32]),
                num_sortitions: last_snapshot.num_sortitions + 1,
                stacks_block_accepted: false,
                stacks_block_height: 0,
                arrival_index: 0,
                canonical_stacks_tip_height: last_snapshot.canonical_stacks_tip_height,
                canonical_stacks_tip_hash: last_snapshot.canonical_stacks_tip_hash,
                canonical_stacks_tip_consensus_hash: last_snapshot
                    .canonical_stacks_tip_consensus_hash,
                miner_pk_hash: None,
            };
            new_snapshots.push(snapshot.clone());
            {
                let mut tx = SortitionHandleTx::begin(db, &last_snapshot.sortition_id).unwrap();
                let _index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot,
                        &[],
                        &[],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();
            }
            last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &snapshot.sortition_id)
                .unwrap()
                .unwrap();
        }
        new_snapshots
    }

    #[test]
    fn test_set_stacks_block_accepted() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();

        let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        // seed a single fork
        make_fork_run(&mut db, &last_snapshot, 5, 0);

        // set some blocks as processed
        for i in 0..5 {
            let consensus_hash = ConsensusHash([(i + 1) as u8; 20]);

            let stacks_block_hash = BlockHeaderHash([i as u8; 32]);
            let height = i;

            {
                let mut tx = db.tx_begin_at_tip();

                debug!(
                    "test: set_stacks_block_accepted {}/{} height {}",
                    &consensus_hash, &stacks_block_hash, height
                );
                tx.set_stacks_block_accepted(&consensus_hash, &stacks_block_hash, height)
                    .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);
        }

        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x04; 32]))
            .unwrap()
            .unwrap();

        // before materializing new arrivals to the MARF, we should still have the canonical tip
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );

        // materialize all block arrivals in the MARF
        make_fork_run(&mut db, &last_snapshot, 1, 0);

        // verify that all Stacks block in this fork can be looked up from this chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        {
            let ic = db.index_conn();
            for i in 0..5 {
                let parent_stacks_block_hash = BlockHeaderHash([i as u8; 32]);
                let parent_key = db_keys::stacks_block_index(&parent_stacks_block_hash);

                test_debug!(
                    "Look up '{}' off of {}",
                    &parent_key,
                    &last_snapshot.burn_header_hash
                );
                let value_opt = ic
                    .get_indexed(&last_snapshot.sortition_id, &parent_key)
                    .unwrap();
                assert!(value_opt.is_some());
                assert_eq!(value_opt.unwrap(), format!("{}", i));
            }
        }

        // make a burn fork off of the 5th block
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        make_fork_run(&mut db, &last_snapshot, 5, 0x80);

        // chain tip is _still_ memoized to the last materialized chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );

        // accept blocks 5 and 7 in one fork, and 6, 8, 9 in another.
        // Stacks fork 1,2,3,4,5,7 will be the longest fork.
        // Stacks fork 1,2,3,4 will overtake it when blocks 6,8,9 are processed.
        for (i, height) in [7].iter().zip([6].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(&consensus_hash, &stacks_block_hash, *height)
                    .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip, since it's the longest stacks fork
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);
        }

        // chain tip is _still_ memoized to the last materialized chain tip (i.e. stacks block 7)
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x88; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x87; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // when the blocks for burn blocks 6 and 8 arrive, the canonical fork is still at stacks
        // block 7.  The two stacks forks will be:
        // * 1,2,3,4,5,7
        // * 1,2,3,4,6,8
        for (i, height) in [6, 8].iter().zip([5, 6].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(&consensus_hash, &stacks_block_hash, *height)
                    .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip, since it's the longest stacks fork.
            // BUT! the tie-breaking logic will cause the canonical fork to *flip*
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();

            if *i != 8 {
                assert_eq!(
                    block_consensus_hash,
                    last_snapshot.canonical_stacks_tip_consensus_hash
                );
                assert_eq!(block_bhh, last_snapshot.canonical_stacks_tip_hash);
            } else {
                // flip!
                let new_last_snapshot =
                    SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
                assert_eq!(
                    block_consensus_hash,
                    new_last_snapshot.canonical_stacks_tip_consensus_hash
                );
                assert_eq!(block_bhh, new_last_snapshot.canonical_stacks_tip_hash);
                assert_ne!(
                    new_last_snapshot.canonical_stacks_tip_consensus_hash,
                    last_snapshot.canonical_stacks_tip_consensus_hash
                );
                assert_ne!(
                    new_last_snapshot.canonical_stacks_tip_hash,
                    last_snapshot.canonical_stacks_tip_hash
                );
            }
        }

        // when the block for burn block 9 arrives, the canonical stacks fork will be
        // 1,2,3,4,6,8,9.  It overtakes 1,2,3,4,5,7
        for (i, height) in [9].iter().zip([7].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(&consensus_hash, &stacks_block_hash, *height)
                    .unwrap();
                tx.commit().unwrap();
            }

            // we've overtaken the longest fork with a different longest fork on this burn chain fork
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);
        }

        // canonical stacks chain tip is now stacks block 9
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x8a; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x89; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 7);

        // fork the burn chain at 0x4, producing a longer burnchain fork.  There are now two
        // burnchain forks, where the first one has two stacks forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x04; 32]))
            .unwrap()
            .unwrap();
        make_fork_run(&mut db, &last_snapshot, 7, 0x40);

        // canonical stacks chain tip is now stacks block 4, since the burn chain fork ending on
        // 0x4b has overtaken the burn chain fork ending on 0x8a
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);

        // set the stacks block at 0x4b as accepted as the 5th block
        {
            let mut tx = db.tx_begin_at_tip();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x4c; 20]),
                &BlockHeaderHash([0x4b; 32]),
                5,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // fork the burn chain at 0x48, producing a shorter burnchain fork.  There are now three
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x48; 32]))
            .unwrap()
            .unwrap();
        make_fork_run(&mut db, &last_snapshot, 2, 0x20);

        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);

        // doesn't affect canonical chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // set the stacks block at 0x29 and 0x2a as accepted as the 5th and 6th blocks
        {
            let mut tx = db.tx_handle_begin(&SortitionId([0x2a; 32])).unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x2a; 20]),
                &BlockHeaderHash([0x29; 32]),
                5,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x2b; 20]),
                &BlockHeaderHash([0x2a; 32]),
                6,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a

        // canonical stacks chain off of non-canonical burn chain fork 0x2a should have been updated
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x2b; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x2a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // insertion on the non-canonical tip doesn't affect canonical chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // insert stacks blocks #6, #7, #8, #9 off of the burn chain tip starting at 0x4b (i.e. the
        // canonical burn chain tip), on blocks 0x45, 0x46, and 0x47
        {
            let mut tx = db.tx_begin_at_tip();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x46; 20]),
                &BlockHeaderHash([0x45; 32]),
                5,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x47; 20]),
                &BlockHeaderHash([0x46; 32]),
                6,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x48; 20]),
                &BlockHeaderHash([0x47; 32]),
                7,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x49; 20]),
                &BlockHeaderHash([0x48; 32]),
                8,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,    6,    7,    8,   9
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a

        // new stacks tip is the 9th block added on burn chain tipped by 0x4b
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x49; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x48; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 8);

        // LIMITATION: the burn chain tipped at 0x2a will _not_ be updated, since it is not the
        // canonical burn chain tip.
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x2b; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x2a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // BUT, when the burn chain tipped by 0x2a overtakes the one tipped by 0x4b, then all blocks
        // will show up.
        make_fork_run(&mut db, &last_snapshot, 2, 0x20);

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,    6,    7,    8,    9
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,    7,    8,    9,   10
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a, 0x2b, 0x2c

        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2c; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x49; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x48; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 8);
    }

    /// Verify that the highest Stacks pointer written remains so, even if blocks from lower
    /// heights arrive. Verify that the pointer changes even if no new sortitions are added.
    #[test]
    fn test_stacks_block_accepted_out_of_order() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();

        let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        // seed a single fork
        make_fork_run(&mut db, &last_snapshot, 5, 0);

        // set some blocks as processed
        for i in (0..5).rev() {
            let consensus_hash = ConsensusHash([(i + 1) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([i as u8; 32]);
            let height = i;

            {
                let mut tx = db.tx_begin_at_tip();

                debug!(
                    "test: set_stacks_block_accepted {}/{} height {}",
                    &consensus_hash, &stacks_block_hash, height
                );
                tx.set_stacks_block_accepted(&consensus_hash, &stacks_block_hash, height)
                    .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, ConsensusHash([0x05; 20]));
            assert_eq!(block_bhh, BlockHeaderHash([0x04; 32]));
        }

        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x04; 32]))
            .unwrap()
            .unwrap();

        // before materializing new arrivals to the MARF, we should still have the canonical tip
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
    }

    #[test]
    fn test_stacks_tip_tiebreaker() {
        let snapshot = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: 123,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
            sortition_id: SortitionId([0x02; 32]),
            parent_sortition_id: SortitionId([0x01; 32]),
            parent_burn_header_hash: BurnchainHeaderHash([0xff; 32]),
            consensus_hash: ConsensusHash([0x03; 20]),
            ops_hash: OpsHash([0x04; 32]),
            total_burn: 0,
            sortition: true,
            sortition_hash: SortitionHash([0x05; 32]),
            winning_block_txid: Txid([0x06; 32]),
            winning_stacks_block_hash: BlockHeaderHash([0x07; 32]),
            index_root: TrieHash([0x08; 32]),
            num_sortitions: 3,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0x09; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0x0a; 20]),
            miner_pk_hash: None,
        };

        let best_height = 123;
        let new_block_arrivals = vec![
            (ConsensusHash([0x01; 20]), BlockHeaderHash([0x02; 32]), 123),
            (ConsensusHash([0x03; 20]), BlockHeaderHash([0x04; 32]), 123),
            (ConsensusHash([0x07; 20]), BlockHeaderHash([0x08; 32]), 122),
            (ConsensusHash([0x05; 20]), BlockHeaderHash([0x06; 32]), 123),
        ];

        assert_eq!(
            SortitionHandleTx::break_canonical_stacks_tip_tie(&snapshot, 121, &new_block_arrivals),
            None
        );
        assert_eq!(
            SortitionHandleTx::break_canonical_stacks_tip_tie(&snapshot, 122, &new_block_arrivals),
            Some(2)
        );
        assert_eq!(
            SortitionHandleTx::break_canonical_stacks_tip_tie(&snapshot, 123, &new_block_arrivals),
            Some(0)
        );
    }

    #[test]
    fn test_epoch_switch_205() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let mut db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 8,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();

        let mut cur_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        // In this loop, we will advance the height, and check if the stacks epoch id is advancing as expected.
        for i in 0..20 {
            debug!("Get epoch for block height {}", cur_snapshot.block_height);
            let cur_epoch = SortitionDB::get_stacks_epoch(db.conn(), cur_snapshot.block_height)
                .unwrap()
                .unwrap();

            if cur_snapshot.block_height < 8 {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch10);
            } else if cur_snapshot.block_height < 12 {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch20);
            } else {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch2_05);
            }

            cur_snapshot =
                test_append_snapshot(&mut db, BurnchainHeaderHash([((i + 1) as u8); 32]), &[]);
        }
    }

    #[test]
    fn test_epoch_switch_21() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!("/tmp/test-blockstack-sortdb-{}", to_hex(&buf));

        let mut db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 8,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: 14,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch21,
                    start_height: 14,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();

        let mut cur_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        for i in 0..20 {
            debug!("Get epoch for block height {}", cur_snapshot.block_height);
            let cur_epoch = SortitionDB::get_stacks_epoch(db.conn(), cur_snapshot.block_height)
                .unwrap()
                .unwrap();

            if cur_snapshot.block_height < 8 {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch10);
            } else if cur_snapshot.block_height < 12 {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch20);
            } else if cur_snapshot.block_height < 14 {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch2_05);
            } else {
                assert_eq!(cur_epoch.epoch_id, StacksEpochId::Epoch21);
            }

            cur_snapshot =
                test_append_snapshot(&mut db, BurnchainHeaderHash([((i + 1) as u8); 32]), &[]);
        }
    }

    #[test]
    #[should_panic]
    fn test_bad_epochs_discontinuous() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 9,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                }, // discontinuity
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_bad_epochs_overlapping() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 7,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                }, // overlap
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_bad_epochs_missing_past() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 1,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                }, // should start at 0
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 8,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_bad_epochs_missing_future() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 8,
                    end_height: 12,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 12,
                    end_height: 20,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                }, // missing future
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
    }

    #[test]
    #[should_panic]
    fn test_bad_epochs_invalid() {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!(
            "/tmp/stacks-node-tests/unit-tests-sortdb/db-{}",
            to_hex(&buf)
        );

        let db = SortitionDB::connect(
            &db_path_dir,
            3,
            &BurnchainHeaderHash([0u8; 32]),
            0,
            &[
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch10,
                    start_height: 0,
                    end_height: 8,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_1_0,
                },
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch20,
                    start_height: 8,
                    end_height: 7,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_0,
                }, // invalid range
                StacksEpoch {
                    epoch_id: StacksEpochId::Epoch2_05,
                    start_height: 8,
                    end_height: STACKS_EPOCH_MAX,
                    block_limit: ExecutionCost::max_value(),
                    network_epoch: PEER_VERSION_EPOCH_2_05,
                },
            ],
            PoxConstants::test_default(),
            None,
            true,
        )
        .unwrap();
    }

    #[test]
    fn test_descended_from() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![1, 2, 3, 4, 5],

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let genesis_block_commit = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222221")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            // genesis
            parent_block_ptr: 0,
            parent_vtxindex: 0,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("dec0489b200c05e3611c174a203da75bea86eb16d254afdec9d93a7d50623426")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 1,
            block_height: block_height + 2,
            burn_parent_modulus: ((block_height + 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
            treatment: vec![],
        };

        // descends from genesis
        let block_commit_1 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: genesis_block_commit.block_height as u32,
            parent_vtxindex: genesis_block_commit.vtxindex as u16,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("c25b21f8c8d55f52cf67e1e7604ca243438df7753a06bea085e10a9957ce0f8e")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 1,
            block_height: block_height + 3,
            burn_parent_modulus: ((block_height + 2) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x04; 32]),
            treatment: vec![],
        };

        // descends from block_commit_1
        let block_commit_1_1 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222224")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: block_commit_1.block_height as u32,
            parent_vtxindex: block_commit_1.vtxindex as u16,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("a55f4f6afff0ba597a22a5d90bea2cd61b078518dbdf67f77588e3c0effb5c0f")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 1,
            block_height: block_height + 4,
            burn_parent_modulus: ((block_height + 3) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x05; 32]),
            treatment: vec![],
        };

        // descends from genesis_block_commit
        let block_commit_2 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222223")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: genesis_block_commit.block_height as u32,
            parent_vtxindex: genesis_block_commit.vtxindex as u16,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 1,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner::mock_parts(
                AddressHashMode::SerializeP2PKH,
                1,
                vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("53bfa82f97ef65f0239ded2b4ed93cab1f9d72f9454ac5eb4d7d0f79ad9e0127")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 2,
            block_height: block_height + 5,
            burn_parent_modulus: ((block_height + 4) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x06; 32]),
            treatment: vec![],
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let key_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &[BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let genesis_commit_snapshot = test_append_snapshot_with_winner(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                genesis_block_commit.clone(),
            )],
            None,
            Some(genesis_block_commit.clone()),
        );

        let first_block_commit_snapshot = test_append_snapshot_with_winner(
            &mut db,
            BurnchainHeaderHash([0x04; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                block_commit_1.clone(),
            )],
            None,
            Some(block_commit_1.clone()),
        );

        let second_block_commit_snapshot = test_append_snapshot_with_winner(
            &mut db,
            BurnchainHeaderHash([0x05; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                block_commit_1_1.clone(),
            )],
            None,
            Some(block_commit_1_1.clone()),
        );

        let third_block_commit_snapshot = test_append_snapshot_with_winner(
            &mut db,
            BurnchainHeaderHash([0x06; 32]),
            &[BlockstackOperationType::LeaderBlockCommit(
                block_commit_2.clone(),
            )],
            None,
            Some(block_commit_2.clone()),
        );

        assert_eq!(
            genesis_commit_snapshot.winning_stacks_block_hash,
            genesis_block_commit.block_header_hash
        );
        assert_eq!(
            first_block_commit_snapshot.winning_stacks_block_hash,
            block_commit_1.block_header_hash
        );
        assert_eq!(
            second_block_commit_snapshot.winning_stacks_block_hash,
            block_commit_1_1.block_header_hash
        );
        assert_eq!(
            third_block_commit_snapshot.winning_stacks_block_hash,
            block_commit_2.block_header_hash
        );

        assert_eq!(
            SortitionDB::get_block_commit_parent_sortition_id(
                db.conn(),
                &block_commit_1.txid,
                &first_block_commit_snapshot.sortition_id
            )
            .unwrap(),
            Some(genesis_commit_snapshot.sortition_id.clone())
        );
        assert_eq!(
            SortitionDB::get_block_commit_parent_sortition_id(
                db.conn(),
                &block_commit_1_1.txid,
                &second_block_commit_snapshot.sortition_id
            )
            .unwrap(),
            Some(first_block_commit_snapshot.sortition_id.clone())
        );
        assert_eq!(
            SortitionDB::get_block_commit_parent_sortition_id(
                db.conn(),
                &block_commit_2.txid,
                &third_block_commit_snapshot.sortition_id
            )
            .unwrap(),
            Some(genesis_commit_snapshot.sortition_id.clone())
        );

        assert_eq!(
            SortitionDB::get_block_commit_parent_sortition_id(
                db.conn(),
                &block_commit_2.txid,
                &first_block_commit_snapshot.sortition_id
            )
            .unwrap(),
            None
        );

        for i in 0..2 {
            // do this battery of tests twice -- once with the block commit parent descendancy
            // information, and once without.
            if i == 0 {
                debug!("Test descended_from with block_commit_parents");
            } else {
                debug!("Test descended_from without block_commit_parents");
            }
            {
                let mut db_tx =
                    SortitionHandleTx::begin(&mut db, &third_block_commit_snapshot.sortition_id)
                        .unwrap();
                assert!(db_tx
                    .descended_from(
                        block_commit_1.block_height,
                        &block_commit_1.block_header_hash
                    )
                    .unwrap());
                assert!(db_tx
                    .descended_from(
                        block_commit_1.block_height,
                        &genesis_block_commit.block_header_hash
                    )
                    .unwrap());
                assert!(db_tx
                    .descended_from(
                        block_commit_2.block_height,
                        &genesis_block_commit.block_header_hash
                    )
                    .unwrap());

                assert!(!db_tx
                    .descended_from(
                        block_commit_2.block_height,
                        &block_commit_1.block_header_hash
                    )
                    .unwrap());

                // not possible, since block_commit_1 predates block_commit_2
                assert!(!db_tx
                    .descended_from(
                        block_commit_1.block_height,
                        &block_commit_2.block_header_hash
                    )
                    .unwrap());
            }
            {
                let mut db_tx =
                    SortitionHandleTx::begin(&mut db, &third_block_commit_snapshot.sortition_id)
                        .unwrap();
                assert!(db_tx
                    .descended_from(
                        block_commit_1_1.block_height,
                        &block_commit_1.block_header_hash
                    )
                    .unwrap());
                assert!(db_tx
                    .descended_from(
                        block_commit_1.block_height,
                        &genesis_block_commit.block_header_hash
                    )
                    .unwrap());

                // transitively...
                assert!(db_tx
                    .descended_from(
                        block_commit_1_1.block_height,
                        &genesis_block_commit.block_header_hash
                    )
                    .unwrap());
            }

            // drop descendancy information
            {
                let db_tx = db.tx_begin().unwrap();
                db_tx
                    .execute("DELETE FROM block_commit_parents", NO_PARAMS)
                    .unwrap();
                db_tx.commit().unwrap();
            }
        }
    }

    #[test]
    fn test_get_ancestor_burnchain_header_hashes() {
        let block_height = 100;
        let first_burn_hash = BurnchainHeaderHash([0x00; 32]);
        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();
        for i in 1..11 {
            test_append_snapshot(&mut db, BurnchainHeaderHash([i as u8; 32]), &[]);
        }

        // typical
        let ancestors = SortitionDB::get_ancestor_burnchain_header_hashes(
            db.conn(),
            &BurnchainHeaderHash([0x09; 32]),
            6,
        )
        .unwrap();
        assert_eq!(
            ancestors,
            vec![
                BurnchainHeaderHash([0x09; 32]),
                BurnchainHeaderHash([0x08; 32]),
                BurnchainHeaderHash([0x07; 32]),
                BurnchainHeaderHash([0x06; 32]),
                BurnchainHeaderHash([0x05; 32]),
                BurnchainHeaderHash([0x04; 32]),
                BurnchainHeaderHash([0x03; 32])
            ]
        );

        // edge case -- get too many
        let ancestors = SortitionDB::get_ancestor_burnchain_header_hashes(
            db.conn(),
            &BurnchainHeaderHash([0x09; 32]),
            20,
        )
        .unwrap();
        assert_eq!(
            ancestors,
            vec![
                BurnchainHeaderHash([0x09; 32]),
                BurnchainHeaderHash([0x08; 32]),
                BurnchainHeaderHash([0x07; 32]),
                BurnchainHeaderHash([0x06; 32]),
                BurnchainHeaderHash([0x05; 32]),
                BurnchainHeaderHash([0x04; 32]),
                BurnchainHeaderHash([0x03; 32]),
                BurnchainHeaderHash([0x02; 32]),
                BurnchainHeaderHash([0x01; 32]),
                BurnchainHeaderHash([0x00; 32]),
                BurnchainHeaderHash([0xff; 32]),
            ]
        );

        // edge case -- get none
        let ancestors = SortitionDB::get_ancestor_burnchain_header_hashes(
            db.conn(),
            &BurnchainHeaderHash([0x09; 32]),
            0,
        )
        .unwrap();
        assert_eq!(ancestors, vec![BurnchainHeaderHash([0x09; 32])]);

        // edge case -- get one that doesn't exist
        let ancestors = SortitionDB::get_ancestor_burnchain_header_hashes(
            db.conn(),
            &BurnchainHeaderHash([0xfe; 32]),
            0,
        )
        .unwrap();
        assert_eq!(ancestors, vec![BurnchainHeaderHash([0xfe; 32])]);
    }

    #[test]
    fn test_get_set_ast_rules() {
        let block_height = 123;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), 0).unwrap(),
            ASTRules::Typical
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), 1).unwrap(),
            ASTRules::Typical
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), AST_RULES_PRECHECK_SIZE - 1).unwrap(),
            ASTRules::Typical
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), AST_RULES_PRECHECK_SIZE).unwrap(),
            ASTRules::PrecheckSize
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), AST_RULES_PRECHECK_SIZE + 1).unwrap(),
            ASTRules::PrecheckSize
        );

        {
            let mut tx = db.tx_begin().unwrap();
            SortitionDB::override_ast_rule_height(&mut tx, ASTRules::PrecheckSize, 1).unwrap();
            tx.commit().unwrap();
        }

        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), 0).unwrap(),
            ASTRules::Typical
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), 1).unwrap(),
            ASTRules::PrecheckSize
        );
        assert_eq!(
            SortitionDB::get_ast_rules(db.conn(), 2).unwrap(),
            ASTRules::PrecheckSize
        );
    }

    #[test]
    fn test_get_chosen_pox_anchor() {
        let path_root = "/tmp/test_get_chosen_pox_anchor";
        if fs::metadata(path_root).is_ok() {
            fs::remove_dir_all(path_root).unwrap();
        }

        fs::create_dir_all(path_root).unwrap();

        let pox_consts = PoxConstants::new(
            10,
            3,
            3,
            25,
            5,
            u64::MAX,
            u64::MAX,
            u32::MAX,
            u32::MAX,
            u32::MAX,
            u32::MAX,
        );

        let mut burnchain = Burnchain::regtest(path_root);
        burnchain.pox_constants = pox_consts.clone();

        let mut burnchain_db =
            BurnchainDB::connect(&burnchain.get_burnchaindb_path(), &burnchain, true).unwrap();
        let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();
        let first_block_height = first_block_header.block_height;

        let mut headers = vec![first_block_header.clone()];
        let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

        let (next_headers, commits) = make_reward_cycle(
            &mut burnchain_db,
            &burnchain,
            &key_register,
            &mut headers,
            vec![None, None],
        );

        assert!(headers.len() > commits.len());

        let mut db = SortitionDB::connect_test_with_epochs(
            first_block_height,
            &first_block_header.block_hash,
            StacksEpoch::all(0, 0, 0),
        )
        .unwrap();

        // make snapshot for each block-commit.
        // make the first run of commits always win.
        for (i, commit_set) in commits.iter().enumerate() {
            let commit_ops: Vec<BlockstackOperationType> = commit_set
                .iter()
                .filter_map(|op| {
                    op.as_ref()
                        .map(|op| BlockstackOperationType::LeaderBlockCommit(op.clone()))
                })
                .collect();
            let winner = if commit_set.is_empty() {
                None
            } else {
                commit_set[0].clone()
            };
            let burn_header_hash = headers[i + 1].block_hash.clone();
            let burn_block_height = headers[i + 1].block_height;

            Burnchain::process_affirmation_maps(
                &burnchain,
                &mut burnchain_db,
                &headers,
                burn_block_height,
            )
            .unwrap();
            test_append_snapshot_with_winner(&mut db, burn_header_hash, &commit_ops, None, winner);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        {
            let ic = db.index_handle(&tip.sortition_id);
            let anchor_2_05 = ic
                .get_chosen_pox_anchor(None, &tip.burn_header_hash, &pox_consts)
                .unwrap()
                .unwrap();
            let anchor_2_1 = ic
                .get_chosen_pox_anchor(
                    Some(burnchain_db.conn()),
                    &tip.burn_header_hash,
                    &pox_consts,
                )
                .unwrap()
                .unwrap();

            let ic = db.index_conn();
            let expected_anchor_ch = SortitionDB::get_ancestor_snapshot(&ic, 7, &tip.sortition_id)
                .unwrap()
                .unwrap()
                .consensus_hash;
            assert_eq!(
                anchor_2_05,
                (
                    expected_anchor_ch.clone(),
                    commits[6][0].as_ref().unwrap().block_header_hash.clone(),
                    commits[6][0].as_ref().unwrap().txid.clone(),
                )
            );
            assert_eq!(
                anchor_2_1,
                (
                    expected_anchor_ch,
                    commits[6][1].as_ref().unwrap().block_header_hash.clone(),
                    commits[6][1].as_ref().unwrap().txid.clone(),
                )
            );
        }
    }

    #[test]
    fn test_load_store_burnchain_ops() {
        let block_height = 123;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let fork_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000001",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();
        let vote_pubkey = StacksPublicKey::from_hex(
            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
        )
        .unwrap();
        let vote_key: StacksPublicKeyBuffer = vote_pubkey.to_bytes_compressed().as_slice().into();

        let good_ops = vec![
            BlockstackOperationType::TransferStx(TransferStxOp {
                sender: StacksAddress::new(1, Hash160([1u8; 20])),
                recipient: StacksAddress::new(2, Hash160([2u8; 20])),
                transfered_ustx: 123,
                memo: vec![0x00, 0x01, 0x02, 0x03, 0x04],

                txid: Txid([0x01; 32]),
                vtxindex: 1,
                block_height,
                burn_header_hash: first_burn_hash.clone(),
            }),
            BlockstackOperationType::StackStx(StackStxOp {
                sender: StacksAddress::new(3, Hash160([3u8; 20])),
                reward_addr: PoxAddress::Standard(StacksAddress::new(4, Hash160([4u8; 20])), None),
                stacked_ustx: 456,
                num_cycles: 6,
                signer_key: Some(StacksPublicKeyBuffer([0x02; 33])),
                max_amount: Some(u128::MAX),
                auth_id: Some(0u32),

                txid: Txid([0x02; 32]),
                vtxindex: 2,
                block_height,
                burn_header_hash: first_burn_hash.clone(),
            }),
            BlockstackOperationType::DelegateStx(DelegateStxOp {
                sender: StacksAddress::new(6, Hash160([6u8; 20])),
                delegate_to: StacksAddress::new(7, Hash160([7u8; 20])),
                reward_addr: Some((
                    123,
                    PoxAddress::Standard(
                        StacksAddress::new(8, Hash160([8u8; 20])),
                        Some(AddressHashMode::SerializeP2PKH),
                    ),
                )),
                delegated_ustx: 789,
                until_burn_height: Some(1000),

                txid: Txid([0x04; 32]),
                vtxindex: 3,
                block_height,
                burn_header_hash: first_burn_hash.clone(),
            }),
            BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
                sender: StacksAddress::new(6, Hash160([6u8; 20])),
                aggregate_key: vote_key,
                signer_key: vote_key,
                round: 1,
                reward_cycle: 2,
                signer_index: 3,

                txid: Txid([0x05; 32]),
                vtxindex: 4,
                block_height,
                burn_header_hash: first_burn_hash.clone(),
            }),
        ];

        let mut tx = db.tx_begin_at_tip();
        for op in good_ops.iter() {
            tx.store_burnchain_transaction(op, &SortitionId::stubbed(&first_burn_hash))
                .unwrap();
        }
        tx.commit().unwrap();

        let ops = SortitionDB::get_transfer_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::TransferStx(ops[0].clone()),
            good_ops[0]
        );

        let ops = SortitionDB::get_stack_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::StackStx(ops[0].clone()),
            good_ops[1]
        );

        let ops = SortitionDB::get_delegate_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::DelegateStx(ops[0].clone()),
            good_ops[2]
        );

        let ops = SortitionDB::get_vote_for_aggregate_key_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::VoteForAggregateKey(ops[0].clone()),
            good_ops[3]
        );

        // if the same ops get mined in a different burnchain block, they will still be available
        let good_ops_2 = vec![
            BlockstackOperationType::TransferStx(TransferStxOp {
                sender: StacksAddress::new(1, Hash160([1u8; 20])),
                recipient: StacksAddress::new(2, Hash160([2u8; 20])),
                transfered_ustx: 123,
                memo: vec![0x00, 0x01, 0x02, 0x03, 0x04],

                txid: Txid([0x01; 32]),
                vtxindex: 1,
                block_height,
                burn_header_hash: fork_burn_hash.clone(),
            }),
            BlockstackOperationType::StackStx(StackStxOp {
                sender: StacksAddress::new(3, Hash160([3u8; 20])),
                reward_addr: PoxAddress::Standard(StacksAddress::new(4, Hash160([4u8; 20])), None),
                stacked_ustx: 456,
                num_cycles: 6,
                signer_key: None,
                max_amount: None,
                auth_id: None,

                txid: Txid([0x02; 32]),
                vtxindex: 2,
                block_height,
                burn_header_hash: fork_burn_hash.clone(),
            }),
            BlockstackOperationType::DelegateStx(DelegateStxOp {
                sender: StacksAddress::new(6, Hash160([6u8; 20])),
                delegate_to: StacksAddress::new(7, Hash160([7u8; 20])),
                reward_addr: Some((
                    123,
                    PoxAddress::Standard(StacksAddress::new(8, Hash160([8u8; 20])), None),
                )),
                delegated_ustx: 789,
                until_burn_height: Some(1000),

                txid: Txid([0x04; 32]),
                vtxindex: 3,
                block_height,
                burn_header_hash: fork_burn_hash.clone(),
            }),
            BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
                sender: StacksAddress::new(6, Hash160([6u8; 20])),
                aggregate_key: StacksPublicKeyBuffer([0x01; 33]),
                signer_key: StacksPublicKeyBuffer([0x02; 33]),
                round: 1,
                reward_cycle: 2,
                signer_index: 3,

                txid: Txid([0x05; 32]),
                vtxindex: 4,
                block_height,
                burn_header_hash: fork_burn_hash.clone(),
            }),
        ];

        let mut tx = db.tx_begin_at_tip();
        for op in good_ops_2.iter() {
            tx.store_burnchain_transaction(op, &SortitionId::stubbed(&fork_burn_hash))
                .unwrap();
        }
        tx.commit().unwrap();

        // old ones are still there
        let ops = SortitionDB::get_transfer_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::TransferStx(ops[0].clone()),
            good_ops[0]
        );

        let ops = SortitionDB::get_stack_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::StackStx(ops[0].clone()),
            good_ops[1]
        );

        let ops = SortitionDB::get_delegate_stx_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::DelegateStx(ops[0].clone()),
            good_ops[2]
        );

        let ops = SortitionDB::get_vote_for_aggregate_key_ops(db.conn(), &first_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::VoteForAggregateKey(ops[0].clone()),
            good_ops[3]
        );

        // and so are the new ones
        let ops = SortitionDB::get_transfer_stx_ops(db.conn(), &fork_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::TransferStx(ops[0].clone()),
            good_ops_2[0]
        );

        let ops = SortitionDB::get_stack_stx_ops(db.conn(), &fork_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::StackStx(ops[0].clone()),
            good_ops_2[1]
        );

        let ops = SortitionDB::get_delegate_stx_ops(db.conn(), &fork_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::DelegateStx(ops[0].clone()),
            good_ops_2[2]
        );

        let ops = SortitionDB::get_vote_for_aggregate_key_ops(db.conn(), &fork_burn_hash).unwrap();
        assert_eq!(ops.len(), 1);
        assert_eq!(
            BlockstackOperationType::VoteForAggregateKey(ops[0].clone()),
            good_ops_2[3]
        );
    }

    #[test]
    fn test_validate_and_replace_epochs() {
        use crate::core::STACKS_EPOCHS_MAINNET;

        let path_root = "/tmp/test_validate_and_replace_epochs";
        if fs::metadata(path_root).is_ok() {
            fs::remove_dir_all(path_root).unwrap();
        }

        fs::create_dir_all(path_root).unwrap();

        let mut bad_epochs = (*STACKS_EPOCHS_MAINNET).clone();
        bad_epochs[StacksEpochId::Epoch25].end_height += 1;
        bad_epochs[StacksEpochId::Epoch30].start_height += 1;

        let sortdb = SortitionDB::connect(
            &format!("{}/sortdb.sqlite", &path_root),
            0,
            &BurnchainHeaderHash([0x00; 32]),
            0,
            &bad_epochs,
            PoxConstants::mainnet_default(),
            None,
            true,
        )
        .unwrap();

        let db_epochs = SortitionDB::get_stacks_epochs(sortdb.conn()).unwrap();
        assert_eq!(db_epochs, bad_epochs.to_vec());

        let fixed_sortdb = SortitionDB::connect(
            &format!("{}/sortdb.sqlite", &path_root),
            0,
            &BurnchainHeaderHash([0x00; 32]),
            0,
            &STACKS_EPOCHS_MAINNET,
            PoxConstants::mainnet_default(),
            None,
            true,
        )
        .unwrap();

        let db_epochs = SortitionDB::get_stacks_epochs(sortdb.conn()).unwrap();
        assert_eq!(db_epochs, STACKS_EPOCHS_MAINNET.to_vec());
    }

    #[test]
    fn latest_db_version_supports_latest_epoch() {
        assert!(SortitionDB::is_db_version_supported_in_epoch(
            StacksEpochId::latest(),
            SORTITION_DB_VERSION
        ));
    }

    #[test]
    fn test_has_consensus_hash() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();

        let last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        // fork 1: 0 <-- 1 <-- 2 <-- 3 <-- 4
        //                              \
        // fork 2:                       *---- 5 <-- 6

        let all_snapshots = make_fork_run(&mut db, &last_snapshot, 5, 0);
        let fork_snapshots = make_fork_run(&mut db, &all_snapshots[3], 2, 0x80);

        let tip = &all_snapshots[4];
        let tip_2 = &fork_snapshots[1];
        assert_ne!(tip, tip_2);

        let ih = db.index_handle(&tip.sortition_id);
        for sn in all_snapshots.iter() {
            assert!(ih.has_consensus_hash(&sn.consensus_hash).unwrap());
        }
        for sn in fork_snapshots.iter() {
            assert!(!ih.has_consensus_hash(&sn.consensus_hash).unwrap());
        }

        let ih = db.index_handle(&tip_2.sortition_id);
        for sn in fork_snapshots.iter() {
            assert!(ih.has_consensus_hash(&sn.consensus_hash).unwrap());
        }
        for sn in all_snapshots[0..4].iter() {
            assert!(ih.has_consensus_hash(&sn.consensus_hash).unwrap());
        }
        assert!(!ih
            .has_consensus_hash(&all_snapshots[4].consensus_hash)
            .unwrap());
    }
}
