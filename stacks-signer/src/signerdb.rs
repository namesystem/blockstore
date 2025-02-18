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

use std::fmt::Display;
use std::path::Path;
use std::time::{Duration, SystemTime};

use blockstack_lib::chainstate::nakamoto::NakamotoBlock;
use blockstack_lib::chainstate::stacks::TransactionPayload;
use blockstack_lib::util_lib::db::{
    query_row, query_rows, sqlite_open, table_exists, tx_begin_immediate, u64_to_sql,
    Error as DBError,
};
#[cfg(any(test, feature = "testing"))]
use blockstack_lib::util_lib::db::{FromColumn, FromRow};
use clarity::types::chainstate::{BurnchainHeaderHash, StacksAddress};
use clarity::types::Address;
use libsigner::v0::messages::{RejectReason, RejectReasonPrefix};
use libsigner::BlockProposal;
use rusqlite::functions::FunctionFlags;
use rusqlite::{
    params, Connection, Error as SqliteError, OpenFlags, OptionalExtension, Transaction,
};
use serde::{Deserialize, Serialize};
use slog::{slog_debug, slog_error};
use stacks_common::codec::{read_next, write_next, Error as CodecError, StacksMessageCodec};
use stacks_common::types::chainstate::ConsensusHash;
use stacks_common::util::get_epoch_time_secs;
use stacks_common::util::hash::Sha512Trunc256Sum;
use stacks_common::util::secp256k1::MessageSignature;
use stacks_common::{debug, define_u8_enum, error};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
/// A vote across the signer set for a block
pub struct NakamotoBlockVote {
    /// Signer signature hash (i.e. block hash) of the Nakamoto block
    pub signer_signature_hash: Sha512Trunc256Sum,
    /// Whether or not the block was rejected
    pub rejected: bool,
}

impl StacksMessageCodec for NakamotoBlockVote {
    fn consensus_serialize<W: std::io::Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        write_next(fd, &self.signer_signature_hash)?;
        if self.rejected {
            write_next(fd, &1u8)?;
        }
        Ok(())
    }

    fn consensus_deserialize<R: std::io::Read>(fd: &mut R) -> Result<Self, CodecError> {
        let signer_signature_hash = read_next(fd)?;
        let rejected_byte: Option<u8> = read_next(fd).ok();
        let rejected = rejected_byte.is_some();
        Ok(Self {
            signer_signature_hash,
            rejected,
        })
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Default)]
/// Store extra version-specific info in `BlockInfo`
pub enum ExtraBlockInfo {
    #[default]
    /// Don't know what version
    None,
    /// Extra data for Signer V0
    V0,
}

define_u8_enum!(
/// Block state relative to the signer's view of the stacks blockchain
BlockState {
    /// The block has not yet been processed by the signer
    Unprocessed = 0,
    /// The block is accepted by the signer but a threshold of signers has not yet signed it
    LocallyAccepted = 1,
    /// The block is rejected by the signer but a threshold of signers has not accepted/rejected it yet
    LocallyRejected = 2,
    /// A threshold number of signers have signed the block
    GloballyAccepted = 3,
    /// A threshold number of signers have rejected the block
    GloballyRejected = 4
});

impl TryFrom<u8> for BlockState {
    type Error = String;
    fn try_from(value: u8) -> Result<BlockState, String> {
        let state = match value {
            0 => BlockState::Unprocessed,
            1 => BlockState::LocallyAccepted,
            2 => BlockState::LocallyRejected,
            3 => BlockState::GloballyAccepted,
            4 => BlockState::GloballyRejected,
            _ => return Err("Invalid block state".into()),
        };
        Ok(state)
    }
}

impl Display for BlockState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = match self {
            BlockState::Unprocessed => "Unprocessed",
            BlockState::LocallyAccepted => "LocallyAccepted",
            BlockState::LocallyRejected => "LocallyRejected",
            BlockState::GloballyAccepted => "GloballyAccepted",
            BlockState::GloballyRejected => "GloballyRejected",
        };
        write!(f, "{}", state)
    }
}

impl TryFrom<&str> for BlockState {
    type Error = String;
    fn try_from(value: &str) -> Result<BlockState, String> {
        let state = match value {
            "Unprocessed" => BlockState::Unprocessed,
            "LocallyAccepted" => BlockState::LocallyAccepted,
            "LocallyRejected" => BlockState::LocallyRejected,
            "GloballyAccepted" => BlockState::GloballyAccepted,
            "GloballyRejected" => BlockState::GloballyRejected,
            _ => return Err("Unparsable block state".into()),
        };
        Ok(state)
    }
}

/// Additional Info about a proposed block
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct BlockInfo {
    /// The block we are considering
    pub block: NakamotoBlock,
    /// The burn block height at which the block was proposed
    pub burn_block_height: u64,
    /// The reward cycle the block belongs to
    pub reward_cycle: u64,
    /// Our vote on the block if we have one yet
    pub vote: Option<NakamotoBlockVote>,
    /// Whether the block contents are valid
    pub valid: Option<bool>,
    /// Whether this block is already being signed over
    pub signed_over: bool,
    /// Time at which the proposal was received by this signer (epoch time in seconds)
    pub proposed_time: u64,
    /// Time at which the proposal was signed by this signer (epoch time in seconds)
    pub signed_self: Option<u64>,
    /// Time at which the proposal was signed by a threshold in the signer set (epoch time in seconds)
    pub signed_group: Option<u64>,
    /// The block state relative to the signer's view of the stacks blockchain
    pub state: BlockState,
    /// Consumed processing time in milliseconds to validate this block
    pub validation_time_ms: Option<u64>,
    /// Extra data specific to v0, v1, etc.
    pub ext: ExtraBlockInfo,
}

impl From<BlockProposal> for BlockInfo {
    fn from(value: BlockProposal) -> Self {
        Self {
            block: value.block,
            burn_block_height: value.burn_height,
            reward_cycle: value.reward_cycle,
            vote: None,
            valid: None,
            signed_over: false,
            proposed_time: get_epoch_time_secs(),
            signed_self: None,
            signed_group: None,
            ext: ExtraBlockInfo::default(),
            state: BlockState::Unprocessed,
            validation_time_ms: None,
        }
    }
}
impl BlockInfo {
    /// Whether the block is a tenure change block or not
    pub fn is_tenure_change(&self) -> bool {
        self.block
            .txs
            .first()
            .map(|tx| matches!(tx.payload, TransactionPayload::TenureChange(_)))
            .unwrap_or(false)
    }

    /// Mark this block as locally accepted, valid, signed over, and records either the self or group signed timestamp in the block info if it wasn't
    ///  already set.
    pub fn mark_locally_accepted(&mut self, group_signed: bool) -> Result<(), String> {
        self.move_to(BlockState::LocallyAccepted)?;
        self.valid = Some(true);
        self.signed_over = true;
        if group_signed {
            self.signed_group.get_or_insert(get_epoch_time_secs());
        } else {
            self.signed_self.get_or_insert(get_epoch_time_secs());
        }
        Ok(())
    }

    /// Mark this block as valid, signed over, and records a group timestamp in the block info if it wasn't
    ///  already set.
    fn mark_globally_accepted(&mut self) -> Result<(), String> {
        self.move_to(BlockState::GloballyAccepted)?;
        self.valid = Some(true);
        self.signed_over = true;
        self.signed_group.get_or_insert(get_epoch_time_secs());
        Ok(())
    }

    /// Mark the block as locally rejected and invalid
    pub fn mark_locally_rejected(&mut self) -> Result<(), String> {
        self.move_to(BlockState::LocallyRejected)?;
        self.valid = Some(false);
        Ok(())
    }

    /// Mark the block as globally rejected and invalid
    fn mark_globally_rejected(&mut self) -> Result<(), String> {
        self.move_to(BlockState::GloballyRejected)?;
        self.valid = Some(false);
        Ok(())
    }

    /// Return the block's signer signature hash
    pub fn signer_signature_hash(&self) -> Sha512Trunc256Sum {
        self.block.header.signer_signature_hash()
    }

    /// Check if the block state transition is valid
    fn check_state(&self, state: BlockState) -> bool {
        let prev_state = &self.state;
        if *prev_state == state {
            return true;
        }
        match state {
            BlockState::Unprocessed => false,
            BlockState::LocallyAccepted | BlockState::LocallyRejected => !matches!(
                prev_state,
                BlockState::GloballyRejected | BlockState::GloballyAccepted
            ),
            BlockState::GloballyAccepted => !matches!(prev_state, BlockState::GloballyRejected),
            BlockState::GloballyRejected => !matches!(prev_state, BlockState::GloballyAccepted),
        }
    }

    /// Attempt to transition the block state
    pub fn move_to(&mut self, state: BlockState) -> Result<(), String> {
        if !self.check_state(state) {
            return Err(format!(
                "Invalid state transition from {} to {state}",
                self.state
            ));
        }
        self.state = state;
        Ok(())
    }

    /// Check if the block is globally accepted or rejected
    pub fn has_reached_consensus(&self) -> bool {
        matches!(
            self.state,
            BlockState::GloballyAccepted | BlockState::GloballyRejected
        )
    }

    /// Check if the block is locally accepted or rejected
    pub fn is_locally_finalized(&self) -> bool {
        matches!(
            self.state,
            BlockState::LocallyAccepted | BlockState::LocallyRejected
        )
    }
}

/// This struct manages a SQLite database connection
/// for the signer.
#[derive(Debug)]
pub struct SignerDb {
    /// Connection to the SQLite database
    db: Connection,
}

static CREATE_BLOCKS_TABLE_1: &str = "
CREATE TABLE IF NOT EXISTS blocks (
    reward_cycle INTEGER NOT NULL,
    signer_signature_hash TEXT NOT NULL,
    block_info TEXT NOT NULL,
    consensus_hash TEXT NOT NULL,
    signed_over INTEGER NOT NULL,
    stacks_height INTEGER NOT NULL,
    burn_block_height INTEGER NOT NULL,
    PRIMARY KEY (reward_cycle, signer_signature_hash)
) STRICT";

static CREATE_BLOCKS_TABLE_2: &str = "
CREATE TABLE IF NOT EXISTS blocks (
    reward_cycle INTEGER NOT NULL,
    signer_signature_hash TEXT NOT NULL,
    block_info TEXT NOT NULL,
    consensus_hash TEXT NOT NULL,
    signed_over INTEGER NOT NULL,
    broadcasted INTEGER,
    stacks_height INTEGER NOT NULL,
    burn_block_height INTEGER NOT NULL,
    PRIMARY KEY (reward_cycle, signer_signature_hash)
) STRICT";

static CREATE_INDEXES_1: &str = "
CREATE INDEX IF NOT EXISTS blocks_signed_over ON blocks (signed_over);
CREATE INDEX IF NOT EXISTS blocks_consensus_hash ON blocks (consensus_hash);
CREATE INDEX IF NOT EXISTS blocks_valid ON blocks ((json_extract(block_info, '$.valid')));
CREATE INDEX IF NOT EXISTS burn_blocks_height ON burn_blocks (block_height);
";

static CREATE_INDEXES_2: &str = r#"
CREATE INDEX IF NOT EXISTS block_signatures_on_signer_signature_hash ON block_signatures(signer_signature_hash);
"#;

static CREATE_INDEXES_3: &str = r#"
CREATE INDEX IF NOT EXISTS block_rejection_signer_addrs_on_block_signature_hash ON block_rejection_signer_addrs(signer_signature_hash);
"#;

static CREATE_INDEXES_4: &str = r#"
CREATE INDEX IF NOT EXISTS blocks_state ON blocks ((json_extract(block_info, '$.state')));
CREATE INDEX IF NOT EXISTS blocks_signed_group ON blocks ((json_extract(block_info, '$.signed_group')));
"#;

static CREATE_INDEXES_5: &str = r#"
CREATE INDEX IF NOT EXISTS blocks_signed_over ON blocks (consensus_hash, signed_over);
CREATE INDEX IF NOT EXISTS blocks_consensus_hash_state ON blocks (consensus_hash, state);
CREATE INDEX IF NOT EXISTS blocks_state ON blocks (state);
CREATE INDEX IF NOT EXISTS blocks_signed_group ON blocks (signed_group);
"#;

static CREATE_INDEXES_6: &str = r#"
CREATE INDEX IF NOT EXISTS block_validations_pending_on_added_time ON block_validations_pending(added_time ASC);
"#;

static CREATE_INDEXES_8: &str = r#"
-- Add new index for get_last_globally_accepted_block query
CREATE INDEX IF NOT EXISTS blocks_consensus_hash_state_height ON blocks (consensus_hash, state, stacks_height DESC);

-- Add new index for get_canonical_tip query
CREATE INDEX IF NOT EXISTS blocks_state_height_signed_group ON blocks (state, stacks_height DESC, signed_group DESC);

-- Index for get_first_signed_block_in_tenure
CREATE INDEX IF NOT EXISTS blocks_consensus_hash_status_height ON blocks (consensus_hash, signed_over, stacks_height ASC);

-- Index for has_unprocessed_blocks
CREATE INDEX IF NOT EXISTS blocks_reward_cycle_state on blocks (reward_cycle, state);
"#;

static CREATE_SIGNER_STATE_TABLE: &str = "
CREATE TABLE IF NOT EXISTS signer_states (
    reward_cycle INTEGER PRIMARY KEY,
    encrypted_state BLOB NOT NULL
) STRICT";

static CREATE_BURN_STATE_TABLE: &str = "
CREATE TABLE IF NOT EXISTS burn_blocks (
    block_hash TEXT PRIMARY KEY,
    block_height INTEGER NOT NULL,
    received_time INTEGER NOT NULL
) STRICT";

static CREATE_DB_CONFIG: &str = "
    CREATE TABLE db_config(
        version INTEGER NOT NULL
    ) STRICT
";

static DROP_SCHEMA_0: &str = "
   DROP TABLE IF EXISTS burn_blocks;
   DROP TABLE IF EXISTS signer_states;
   DROP TABLE IF EXISTS blocks;
   DROP TABLE IF EXISTS db_config;";

static DROP_SCHEMA_1: &str = "
   DROP TABLE IF EXISTS burn_blocks;
   DROP TABLE IF EXISTS signer_states;
   DROP TABLE IF EXISTS blocks;
   DROP TABLE IF EXISTS db_config;";

static DROP_SCHEMA_2: &str = "
    DROP TABLE IF EXISTS burn_blocks;
    DROP TABLE IF EXISTS signer_states;
    DROP TABLE IF EXISTS blocks;
    DROP TABLE IF EXISTS db_config;";

static CREATE_BLOCK_SIGNATURES_TABLE: &str = r#"
CREATE TABLE IF NOT EXISTS block_signatures (
    -- The block sighash commits to all of the stacks and burnchain state as of its parent,
    -- as well as the tenure itself so there's no need to include the reward cycle.  Just
    -- the sighash is sufficient to uniquely identify the block across all burnchain, PoX,
    -- and stacks forks.
    signer_signature_hash TEXT NOT NULL,
    -- signature itself
    signature TEXT NOT NULL,
    PRIMARY KEY (signature)
) STRICT;"#;

static CREATE_BLOCK_REJECTION_SIGNER_ADDRS_TABLE: &str = r#"
CREATE TABLE IF NOT EXISTS block_rejection_signer_addrs (
    -- The block sighash commits to all of the stacks and burnchain state as of its parent,
    -- as well as the tenure itself so there's no need to include the reward cycle.  Just
    -- the sighash is sufficient to uniquely identify the block across all burnchain, PoX,
    -- and stacks forks.
    signer_signature_hash TEXT NOT NULL,
    -- the signer address that rejected the block
    signer_addr TEXT NOT NULL,
    PRIMARY KEY (signer_addr)
) STRICT;"#;

// Migration logic necessary to move blocks from the old blocks table to the new blocks table
static MIGRATE_BLOCKS_TABLE_2_BLOCKS_TABLE_3: &str = r#"
CREATE TABLE IF NOT EXISTS temp_blocks (
    -- The block sighash commits to all of the stacks and burnchain state as of its parent,
    -- as well as the tenure itself so there's no need to include the reward cycle.  Just
    -- the sighash is sufficient to uniquely identify the block across all burnchain, PoX,
    -- and stacks forks.
    signer_signature_hash TEXT NOT NULL PRIMARY KEY,
    reward_cycle INTEGER NOT NULL,
    block_info TEXT NOT NULL,
    consensus_hash TEXT NOT NULL,
    signed_over INTEGER NOT NULL,
    broadcasted INTEGER,
    stacks_height INTEGER NOT NULL,
    burn_block_height INTEGER NOT NULL,
    valid INTEGER,
    state TEXT NOT NULL,
    signed_group INTEGER,
    signed_self INTEGER,
    proposed_time INTEGER NOT NULL,
    validation_time_ms INTEGER,
    tenure_change INTEGER NOT NULL
) STRICT;

INSERT INTO temp_blocks (
    signer_signature_hash,
    reward_cycle,
    block_info,
    consensus_hash,
    signed_over,
    broadcasted,
    stacks_height,
    burn_block_height,
    valid,
    state,
    signed_group,
    signed_self,
    proposed_time,
    validation_time_ms,
    tenure_change
)
SELECT
    signer_signature_hash,
    reward_cycle,
    block_info,
    consensus_hash,
    signed_over,
    broadcasted,
    stacks_height,
    burn_block_height,
    json_extract(block_info, '$.valid') AS valid,
    json_extract(block_info, '$.state') AS state,
    json_extract(block_info, '$.signed_group') AS signed_group,
    json_extract(block_info, '$.signed_self') AS signed_self,
    json_extract(block_info, '$.proposed_time') AS proposed_time,
    json_extract(block_info, '$.validation_time_ms') AS validation_time_ms,
    is_tenure_change(block_info) AS tenure_change
FROM blocks;

DROP TABLE blocks;

ALTER TABLE temp_blocks RENAME TO blocks;"#;

static CREATE_BLOCK_VALIDATION_PENDING_TABLE: &str = r#"
CREATE TABLE IF NOT EXISTS block_validations_pending (
    signer_signature_hash TEXT NOT NULL,
    -- the time at which the block was added to the pending table
    added_time INTEGER NOT NULL,
    PRIMARY KEY (signer_signature_hash)
) STRICT;"#;

static CREATE_TENURE_ACTIVTY_TABLE: &str = r#"
CREATE TABLE IF NOT EXISTS tenure_activity (
    consensus_hash TEXT NOT NULL PRIMARY KEY,
    last_activity_time INTEGER NOT NULL
) STRICT;"#;

static ADD_REJECT_CODE: &str = r#"
ALTER TABLE block_rejection_signer_addrs
    ADD COLUMN reject_code INTEGER;
"#;

static SCHEMA_1: &[&str] = &[
    DROP_SCHEMA_0,
    CREATE_DB_CONFIG,
    CREATE_BURN_STATE_TABLE,
    CREATE_BLOCKS_TABLE_1,
    CREATE_SIGNER_STATE_TABLE,
    CREATE_INDEXES_1,
    "INSERT INTO db_config (version) VALUES (1);",
];

static SCHEMA_2: &[&str] = &[
    DROP_SCHEMA_1,
    CREATE_DB_CONFIG,
    CREATE_BURN_STATE_TABLE,
    CREATE_BLOCKS_TABLE_2,
    CREATE_SIGNER_STATE_TABLE,
    CREATE_BLOCK_SIGNATURES_TABLE,
    CREATE_INDEXES_1,
    CREATE_INDEXES_2,
    "INSERT INTO db_config (version) VALUES (2);",
];

static SCHEMA_3: &[&str] = &[
    DROP_SCHEMA_2,
    CREATE_DB_CONFIG,
    CREATE_BURN_STATE_TABLE,
    CREATE_BLOCKS_TABLE_2,
    CREATE_SIGNER_STATE_TABLE,
    CREATE_BLOCK_SIGNATURES_TABLE,
    CREATE_BLOCK_REJECTION_SIGNER_ADDRS_TABLE,
    CREATE_INDEXES_1,
    CREATE_INDEXES_2,
    CREATE_INDEXES_3,
    "INSERT INTO db_config (version) VALUES (3);",
];

static SCHEMA_4: &[&str] = &[
    CREATE_INDEXES_4,
    "INSERT OR REPLACE INTO db_config (version) VALUES (4);",
];

static SCHEMA_5: &[&str] = &[
    MIGRATE_BLOCKS_TABLE_2_BLOCKS_TABLE_3,
    CREATE_INDEXES_5,
    "DELETE FROM db_config;", // Be extra careful. Make sure there is only ever one row in the table.
    "INSERT INTO db_config (version) VALUES (5);",
];

static SCHEMA_6: &[&str] = &[
    CREATE_BLOCK_VALIDATION_PENDING_TABLE,
    CREATE_INDEXES_6,
    "INSERT OR REPLACE INTO db_config (version) VALUES (6);",
];

static SCHEMA_7: &[&str] = &[
    CREATE_TENURE_ACTIVTY_TABLE,
    "INSERT OR REPLACE INTO db_config (version) VALUES (7);",
];

static SCHEMA_8: &[&str] = &[
    CREATE_INDEXES_8,
    "INSERT INTO db_config (version) VALUES (8);",
];

static SCHEMA_9: &[&str] = &[
    ADD_REJECT_CODE,
    "INSERT INTO db_config (version) VALUES (9);",
];

impl SignerDb {
    /// The current schema version used in this build of the signer binary.
    pub const SCHEMA_VERSION: u32 = 9;

    /// Create a new `SignerState` instance.
    /// This will create a new SQLite database at the given path
    /// or an in-memory database if the path is ":memory:"
    pub fn new(db_path: impl AsRef<Path>) -> Result<Self, DBError> {
        let connection = Self::connect(db_path)?;

        let mut signer_db = Self { db: connection };
        signer_db.create_or_migrate()?;

        Ok(signer_db)
    }

    /// Returns the schema version of the database
    fn get_schema_version(conn: &Connection) -> Result<u32, DBError> {
        if !table_exists(conn, "db_config")? {
            return Ok(0);
        }
        let result = conn
            .query_row("SELECT MAX(version) FROM db_config LIMIT 1", [], |row| {
                row.get(0)
            })
            .optional();
        match result {
            Ok(x) => Ok(x.unwrap_or(0)),
            Err(e) => Err(DBError::from(e)),
        }
    }

    /// Migrate from schema 0 to schema 1
    fn schema_1_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 1 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_1.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 1 to schema 2
    fn schema_2_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 2 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_2.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 2 to schema 3
    fn schema_3_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 3 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_3.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 3 to schema 4
    fn schema_4_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 4 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_4.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 4 to schema 5
    fn schema_5_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 5 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_5.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 5 to schema 6
    fn schema_6_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 6 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_6.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 6 to schema 7
    fn schema_7_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 7 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_7.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 7 to schema 8
    fn schema_8_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 8 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_8.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Migrate from schema 9 to schema 9
    fn schema_9_migration(tx: &Transaction) -> Result<(), DBError> {
        if Self::get_schema_version(tx)? >= 9 {
            // no migration necessary
            return Ok(());
        }

        for statement in SCHEMA_9.iter() {
            tx.execute_batch(statement)?;
        }

        Ok(())
    }

    /// Register custom scalar functions used by the database
    fn register_scalar_functions(&self) -> Result<(), DBError> {
        // Register helper function for determining if a block is a tenure change transaction
        // Required only for data migration from Schema 4 to Schema 5
        self.db.create_scalar_function(
            "is_tenure_change",
            1,
            FunctionFlags::SQLITE_UTF8 | FunctionFlags::SQLITE_DETERMINISTIC,
            |ctx| {
                let value = ctx.get::<String>(0)?;
                let block_info = serde_json::from_str::<BlockInfo>(&value)
                    .map_err(|e| SqliteError::UserFunctionError(e.into()))?;
                Ok(block_info.is_tenure_change())
            },
        )?;
        Ok(())
    }

    /// Drop registered scalar functions used only for data migrations
    fn remove_scalar_functions(&self) -> Result<(), DBError> {
        self.db.remove_function("is_tenure_change", 1)?;
        Ok(())
    }

    /// Either instantiate a new database, or migrate an existing one
    /// If the detected version of the existing database is 0 (i.e., a pre-migration
    /// logic DB, the DB will be dropped).
    fn create_or_migrate(&mut self) -> Result<(), DBError> {
        self.register_scalar_functions()?;
        let sql_tx = tx_begin_immediate(&mut self.db)?;
        loop {
            let version = Self::get_schema_version(&sql_tx)?;
            match version {
                0 => Self::schema_1_migration(&sql_tx)?,
                1 => Self::schema_2_migration(&sql_tx)?,
                2 => Self::schema_3_migration(&sql_tx)?,
                3 => Self::schema_4_migration(&sql_tx)?,
                4 => Self::schema_5_migration(&sql_tx)?,
                5 => Self::schema_6_migration(&sql_tx)?,
                6 => Self::schema_7_migration(&sql_tx)?,
                7 => Self::schema_8_migration(&sql_tx)?,
                8 => Self::schema_9_migration(&sql_tx)?,
                9 => break,
                x => return Err(DBError::Other(format!(
                    "Database schema is newer than supported by this binary. Expected version = {}, Database version = {x}",
                    Self::SCHEMA_VERSION,
                ))),
            }
        }
        sql_tx.commit()?;
        self.remove_scalar_functions()?;
        Ok(())
    }

    fn connect(db_path: impl AsRef<Path>) -> Result<Connection, SqliteError> {
        sqlite_open(
            db_path,
            OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE,
            false,
        )
    }

    /// Get the signer state for the provided reward cycle if it exists in the database
    pub fn get_encrypted_signer_state(
        &self,
        reward_cycle: u64,
    ) -> Result<Option<Vec<u8>>, DBError> {
        query_row(
            &self.db,
            "SELECT encrypted_state FROM signer_states WHERE reward_cycle = ?",
            [u64_to_sql(reward_cycle)?],
        )
    }

    /// Insert the given state in the `signer_states` table for the given reward cycle
    pub fn insert_encrypted_signer_state(
        &self,
        reward_cycle: u64,
        encrypted_signer_state: &[u8],
    ) -> Result<(), DBError> {
        self.db.execute(
            "INSERT OR REPLACE INTO signer_states (reward_cycle, encrypted_state) VALUES (?1, ?2)",
            params![u64_to_sql(reward_cycle)?, encrypted_signer_state],
        )?;
        Ok(())
    }

    /// Fetch a block from the database using the block's
    /// `signer_signature_hash`
    pub fn block_lookup(&self, hash: &Sha512Trunc256Sum) -> Result<Option<BlockInfo>, DBError> {
        let result: Option<String> = query_row(
            &self.db,
            "SELECT block_info FROM blocks WHERE signer_signature_hash = ?",
            params![hash.to_string()],
        )?;

        try_deserialize(result)
    }

    /// Return whether there was signed block in a tenure (identified by its consensus hash)
    pub fn has_signed_block_in_tenure(&self, tenure: &ConsensusHash) -> Result<bool, DBError> {
        let query =
            "SELECT block_info FROM blocks WHERE consensus_hash = ? AND signed_over = 1 LIMIT 1";
        let result: Option<String> = query_row(&self.db, query, [tenure])?;

        Ok(result.is_some())
    }

    /// Return the first signed block in a tenure (identified by its consensus hash)
    pub fn get_first_signed_block_in_tenure(
        &self,
        tenure: &ConsensusHash,
    ) -> Result<Option<BlockInfo>, DBError> {
        let query = "SELECT block_info FROM blocks WHERE consensus_hash = ? AND signed_over = 1 ORDER BY stacks_height ASC LIMIT 1";
        let result: Option<String> = query_row(&self.db, query, [tenure])?;

        try_deserialize(result)
    }

    /// Return the last accepted block in a tenure (identified by its consensus hash).
    pub fn get_last_accepted_block(
        &self,
        tenure: &ConsensusHash,
    ) -> Result<Option<BlockInfo>, DBError> {
        let query = "SELECT block_info FROM blocks WHERE consensus_hash = ?1 AND state IN (?2, ?3) ORDER BY stacks_height DESC LIMIT 1";
        let args = params![
            tenure,
            &BlockState::GloballyAccepted.to_string(),
            &BlockState::LocallyAccepted.to_string()
        ];
        let result: Option<String> = query_row(&self.db, query, args)?;

        try_deserialize(result)
    }

    /// Return the last globally accepted block in a tenure (identified by its consensus hash).
    pub fn get_last_globally_accepted_block(
        &self,
        tenure: &ConsensusHash,
    ) -> Result<Option<BlockInfo>, DBError> {
        let query = "SELECT block_info FROM blocks WHERE consensus_hash = ?1 AND state = ?2 ORDER BY stacks_height DESC LIMIT 1";
        let args = params![tenure, &BlockState::GloballyAccepted.to_string()];
        let result: Option<String> = query_row(&self.db, query, args)?;

        try_deserialize(result)
    }

    /// Return the canonical tip -- the last globally accepted block.
    pub fn get_canonical_tip(&self) -> Result<Option<BlockInfo>, DBError> {
        let query = "SELECT block_info FROM blocks WHERE state = ?1 ORDER BY stacks_height DESC, signed_group DESC LIMIT 1";
        let args = params![&BlockState::GloballyAccepted.to_string()];
        let result: Option<String> = query_row(&self.db, query, args)?;

        try_deserialize(result)
    }

    /// Insert or replace a burn block into the database
    pub fn insert_burn_block(
        &mut self,
        burn_hash: &BurnchainHeaderHash,
        burn_height: u64,
        received_time: &SystemTime,
    ) -> Result<(), DBError> {
        let received_ts = received_time
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| DBError::Other(format!("Bad system time: {e}")))?
            .as_secs();
        debug!("Inserting burn block info"; "burn_block_height" => burn_height, "burn_hash" => %burn_hash, "received" => received_ts);
        self.db.execute(
            "INSERT OR REPLACE INTO burn_blocks (block_hash, block_height, received_time) VALUES (?1, ?2, ?3)",
            params![
                burn_hash,
                u64_to_sql(burn_height)?,
                u64_to_sql(received_ts)?,
            ],
        )?;
        Ok(())
    }

    /// Get timestamp (epoch seconds) at which a burn block was received over the event dispatcheer by this signer
    /// if that burn block has been received.
    pub fn get_burn_block_receive_time(
        &self,
        burn_hash: &BurnchainHeaderHash,
    ) -> Result<Option<u64>, DBError> {
        let query = "SELECT received_time FROM burn_blocks WHERE block_hash = ? LIMIT 1";
        let Some(receive_time_i64) = query_row::<i64, _>(&self.db, query, &[burn_hash])? else {
            return Ok(None);
        };
        let receive_time = u64::try_from(receive_time_i64).map_err(|e| {
            error!("Failed to parse db received_time as u64: {e}");
            DBError::Corruption
        })?;
        Ok(Some(receive_time))
    }

    /// Insert or replace a block into the database.
    /// Preserves the `broadcast` column if replacing an existing block.
    pub fn insert_block(&mut self, block_info: &BlockInfo) -> Result<(), DBError> {
        let block_json =
            serde_json::to_string(&block_info).expect("Unable to serialize block info");
        let hash = &block_info.signer_signature_hash();
        let block_id = &block_info.block.block_id();
        let signed_over = block_info.signed_over;
        let vote = block_info
            .vote
            .as_ref()
            .map(|v| if v.rejected { "REJECT" } else { "ACCEPT" });
        let broadcasted = self.get_block_broadcasted(hash)?;
        debug!("Inserting block_info.";
            "reward_cycle" => %block_info.reward_cycle,
            "burn_block_height" => %block_info.burn_block_height,
            "sighash" => %hash,
            "block_id" => %block_id,
            "signed" => %signed_over,
            "broadcasted" => ?broadcasted,
            "vote" => vote
        );
        self.db.execute("INSERT OR REPLACE INTO blocks (reward_cycle, burn_block_height, signer_signature_hash, block_info, signed_over, broadcasted, stacks_height, consensus_hash, valid, state, signed_group, signed_self, proposed_time, validation_time_ms, tenure_change) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15)", params![
            u64_to_sql(block_info.reward_cycle)?,
            u64_to_sql(block_info.burn_block_height)?,
            hash.to_string(),
            block_json,
            &block_info.signed_over,
            &broadcasted,
            u64_to_sql(block_info.block.header.chain_length)?,
            block_info.block.header.consensus_hash.to_hex(),
            &block_info.valid, &block_info.state.to_string(),
            &block_info.signed_group,
            &block_info.signed_self,
            &block_info.proposed_time,
            &block_info.validation_time_ms,
            &block_info.is_tenure_change()
        ])?;
        Ok(())
    }

    /// Determine if there are any unprocessed blocks
    pub fn has_unprocessed_blocks(&self, reward_cycle: u64) -> Result<bool, DBError> {
        let query = "SELECT block_info FROM blocks WHERE reward_cycle = ?1 AND state = ?2 LIMIT 1";
        let result: Option<String> = query_row(
            &self.db,
            query,
            params!(
                &u64_to_sql(reward_cycle)?,
                &BlockState::Unprocessed.to_string()
            ),
        )?;

        Ok(result.is_some())
    }

    /// Record an observed block signature
    pub fn add_block_signature(
        &self,
        block_sighash: &Sha512Trunc256Sum,
        signature: &MessageSignature,
    ) -> Result<(), DBError> {
        let qry = "INSERT OR REPLACE INTO block_signatures (signer_signature_hash, signature) VALUES (?1, ?2);";
        let args = params![
            block_sighash,
            serde_json::to_string(signature).map_err(DBError::SerializationError)?
        ];

        debug!("Inserting block signature.";
            "sighash" => %block_sighash,
            "signature" => %signature);

        self.db.execute(qry, args)?;
        Ok(())
    }

    /// Get all signatures for a block
    pub fn get_block_signatures(
        &self,
        block_sighash: &Sha512Trunc256Sum,
    ) -> Result<Vec<MessageSignature>, DBError> {
        let qry = "SELECT signature FROM block_signatures WHERE signer_signature_hash = ?1";
        let args = params![block_sighash];
        let sigs_txt: Vec<String> = query_rows(&self.db, qry, args)?;
        sigs_txt
            .into_iter()
            .map(|sig_txt| serde_json::from_str(&sig_txt).map_err(|_| DBError::ParseError))
            .collect()
    }

    /// Record an observed block rejection_signature
    pub fn add_block_rejection_signer_addr(
        &self,
        block_sighash: &Sha512Trunc256Sum,
        addr: &StacksAddress,
        reject_reason: &RejectReason,
    ) -> Result<(), DBError> {
        let qry = "INSERT OR REPLACE INTO block_rejection_signer_addrs (signer_signature_hash, signer_addr, reject_code) VALUES (?1, ?2, ?3);";
        let args = params![
            block_sighash,
            addr.to_string(),
            RejectReasonPrefix::from(reject_reason) as i64
        ];

        debug!("Inserting block rejection.";
            "block_sighash" => %block_sighash,
            "signer_address" => %addr,
            "reject_reason" => %reject_reason
        );

        self.db.execute(qry, args)?;
        Ok(())
    }

    /// Get all signer addresses that rejected the block (and their reject codes)
    pub fn get_block_rejection_signer_addrs(
        &self,
        block_sighash: &Sha512Trunc256Sum,
    ) -> Result<Vec<(StacksAddress, RejectReasonPrefix)>, DBError> {
        let qry =
            "SELECT signer_addr, reject_code FROM block_rejection_signer_addrs WHERE signer_signature_hash = ?1";
        let args = params![block_sighash];
        let mut stmt = self.db.prepare(qry)?;

        let rows = stmt.query_map(args, |row| {
            let addr: String = row.get(0)?;
            let addr = StacksAddress::from_string(&addr).ok_or(SqliteError::InvalidColumnType(
                0,
                "signer_addr".into(),
                rusqlite::types::Type::Text,
            ))?;
            let reject_code: i64 = row.get(1)?;

            let reject_code = u8::try_from(reject_code)
                .map_err(|_| {
                    SqliteError::InvalidColumnType(
                        1,
                        "reject_code".into(),
                        rusqlite::types::Type::Integer,
                    )
                })
                .map(RejectReasonPrefix::from)?;

            Ok((addr, reject_code))
        })?;

        rows.collect::<Result<Vec<_>, _>>().map_err(|e| e.into())
    }

    /// Mark a block as having been broadcasted and therefore GloballyAccepted
    pub fn set_block_broadcasted(
        &self,
        block_sighash: &Sha512Trunc256Sum,
        ts: u64,
    ) -> Result<(), DBError> {
        let qry = "UPDATE blocks SET broadcasted = ?1 WHERE signer_signature_hash = ?2";
        let args = params![u64_to_sql(ts)?, block_sighash];

        debug!("Marking block {} as broadcasted at {}", block_sighash, ts);
        self.db.execute(qry, args)?;
        Ok(())
    }

    /// Get the timestamp at which the block was broadcasted.
    pub fn get_block_broadcasted(
        &self,
        block_sighash: &Sha512Trunc256Sum,
    ) -> Result<Option<u64>, DBError> {
        let qry =
            "SELECT IFNULL(broadcasted,0) AS broadcasted FROM blocks WHERE signer_signature_hash = ?";
        let args = params![block_sighash];

        let Some(broadcasted): Option<u64> = query_row(&self.db, qry, args)? else {
            return Ok(None);
        };
        if broadcasted == 0 {
            return Ok(None);
        }
        Ok(Some(broadcasted))
    }

    /// Get a pending block validation, sorted by the time at which it was added to the pending table.
    /// If found, remove it from the pending table.
    pub fn get_and_remove_pending_block_validation(
        &self,
    ) -> Result<Option<Sha512Trunc256Sum>, DBError> {
        let qry = "DELETE FROM block_validations_pending WHERE signer_signature_hash = (SELECT signer_signature_hash FROM block_validations_pending ORDER BY added_time ASC LIMIT 1) RETURNING signer_signature_hash";
        let args = params![];
        let mut stmt = self.db.prepare(qry)?;
        let sighash: Option<String> = stmt.query_row(args, |row| row.get(0)).optional()?;
        Ok(sighash.and_then(|sighash| Sha512Trunc256Sum::from_hex(&sighash).ok()))
    }

    /// Remove a pending block validation
    pub fn remove_pending_block_validation(
        &self,
        sighash: &Sha512Trunc256Sum,
    ) -> Result<(), DBError> {
        self.db.execute(
            "DELETE FROM block_validations_pending WHERE signer_signature_hash = ?1",
            params![sighash.to_string()],
        )?;
        Ok(())
    }

    /// Insert a pending block validation
    pub fn insert_pending_block_validation(
        &self,
        sighash: &Sha512Trunc256Sum,
        ts: u64,
    ) -> Result<(), DBError> {
        self.db.execute(
            "INSERT INTO block_validations_pending (signer_signature_hash, added_time) VALUES (?1, ?2)",
            params![sighash.to_string(), u64_to_sql(ts)?],
        )?;
        Ok(())
    }

    /// Return the start time (epoch time in seconds) and the processing time in milliseconds of the tenure (idenfitied by consensus_hash).
    fn get_tenure_times(&self, tenure: &ConsensusHash) -> Result<(u64, u64), DBError> {
        let query = "SELECT tenure_change, proposed_time, validation_time_ms FROM blocks WHERE consensus_hash = ?1 AND state = ?2 ORDER BY stacks_height DESC";
        let args = params![tenure, BlockState::GloballyAccepted.to_string()];
        let mut stmt = self.db.prepare(query)?;
        let rows = stmt.query_map(args, |row| {
            let tenure_change_block: bool = row.get(0)?;
            let proposed_time: u64 = row.get(1)?;
            let validation_time_ms: Option<u64> = row.get(2)?;
            Ok((tenure_change_block, proposed_time, validation_time_ms))
        })?;
        let mut tenure_processing_time_ms = 0_u64;
        let mut tenure_start_time = None;
        let mut nmb_rows = 0;
        for (i, row) in rows.enumerate() {
            nmb_rows += 1;
            let (tenure_change_block, proposed_time, validation_time_ms) = row?;
            tenure_processing_time_ms =
                tenure_processing_time_ms.saturating_add(validation_time_ms.unwrap_or(0));
            tenure_start_time = Some(proposed_time);
            if tenure_change_block {
                debug!("Found tenure change block {i} blocks ago in tenure {tenure}");
                break;
            }
        }
        debug!("Calculated tenure extend timestamp from {nmb_rows} blocks in tenure {tenure}");
        Ok((
            tenure_start_time.unwrap_or(get_epoch_time_secs()),
            tenure_processing_time_ms,
        ))
    }

    /// Calculate the tenure extend timestamp. If determine the timestamp for a block rejection, check_tenure_extend should be set to false to avoid recalculating
    /// the tenure extend timestamp for a tenure extend block.
    pub fn calculate_tenure_extend_timestamp(
        &self,
        tenure_idle_timeout: Duration,
        block: &NakamotoBlock,
        check_tenure_extend: bool,
    ) -> u64 {
        if check_tenure_extend && block.get_tenure_tx_payload().is_some() {
            let tenure_extend_timestamp =
                get_epoch_time_secs().wrapping_add(tenure_idle_timeout.as_secs());
            debug!("Calculated tenure extend timestamp for a tenure extend block. Rolling over timestamp: {tenure_extend_timestamp}");
            return tenure_extend_timestamp;
        }
        let tenure_idle_timeout_secs = tenure_idle_timeout.as_secs();
        let (tenure_start_time, tenure_process_time_ms) = self.get_tenure_times(&block.header.consensus_hash).inspect_err(|e| error!("Error occurred calculating tenure extend timestamp: {e:?}. Defaulting to {tenure_idle_timeout_secs} from now.")).unwrap_or((get_epoch_time_secs(), 0));
        // Plus (ms + 999)/1000 to round up to the nearest second
        let tenure_extend_timestamp = tenure_start_time
            .saturating_add(tenure_idle_timeout_secs)
            .saturating_add(tenure_process_time_ms.saturating_add(999) / 1000);
        debug!("Calculated tenure extend timestamp";
            "tenure_extend_timestamp" => tenure_extend_timestamp,
            "tenure_start_time" => tenure_start_time,
            "tenure_process_time_ms" => tenure_process_time_ms,
            "tenure_idle_timeout_secs" => tenure_idle_timeout_secs,
            "tenure_extend_in" => tenure_extend_timestamp.saturating_sub(get_epoch_time_secs()),
            "consensus_hash" => %block.header.consensus_hash,
        );
        tenure_extend_timestamp
    }

    /// Mark a block as globally accepted. This removes the block from the pending
    /// validations table. This does **not** update the block's state in SignerDb.
    pub fn mark_block_globally_accepted(&self, block_info: &mut BlockInfo) -> Result<(), DBError> {
        block_info
            .mark_globally_accepted()
            .map_err(DBError::Other)?;
        self.remove_pending_block_validation(&block_info.signer_signature_hash())?;
        Ok(())
    }

    /// Mark a block as globally rejected. This removes the block from the pending
    /// validations table. This does **not** update the block's state in SignerDb.
    pub fn mark_block_globally_rejected(&self, block_info: &mut BlockInfo) -> Result<(), DBError> {
        block_info
            .mark_globally_rejected()
            .map_err(DBError::Other)?;
        self.remove_pending_block_validation(&block_info.signer_signature_hash())?;
        Ok(())
    }
    /// Update the tenure (identified by consensus_hash) last activity timestamp
    pub fn update_last_activity_time(
        &mut self,
        tenure: &ConsensusHash,
        last_activity_time: u64,
    ) -> Result<(), DBError> {
        debug!("Updating last activity for tenure"; "consensus_hash" => %tenure, "last_activity_time" => last_activity_time);
        self.db.execute("INSERT OR REPLACE INTO tenure_activity (consensus_hash, last_activity_time) VALUES (?1, ?2)", params![tenure, u64_to_sql(last_activity_time)?])?;
        Ok(())
    }

    /// Get the last activity timestamp for a tenure (identified by consensus_hash)
    pub fn get_last_activity_time(&self, tenure: &ConsensusHash) -> Result<Option<u64>, DBError> {
        let query =
            "SELECT last_activity_time FROM tenure_activity WHERE consensus_hash = ? LIMIT 1";
        let Some(last_activity_time_i64) = query_row::<i64, _>(&self.db, query, &[tenure])? else {
            return Ok(None);
        };
        let last_activity_time = u64::try_from(last_activity_time_i64).map_err(|e| {
            error!("Failed to parse db last_activity_time as u64: {e}");
            DBError::Corruption
        })?;
        Ok(Some(last_activity_time))
    }
}

fn try_deserialize<T>(s: Option<String>) -> Result<Option<T>, DBError>
where
    T: serde::de::DeserializeOwned,
{
    s.as_deref()
        .map(serde_json::from_str)
        .transpose()
        .map_err(DBError::SerializationError)
}

/// For tests, a struct to represent a pending block validation
#[cfg(any(test, feature = "testing"))]
pub struct PendingBlockValidation {
    /// The signer signature hash of the block
    pub signer_signature_hash: Sha512Trunc256Sum,
    /// The time at which the block was added to the pending table
    pub added_time: u64,
}

#[cfg(any(test, feature = "testing"))]
impl FromRow<PendingBlockValidation> for PendingBlockValidation {
    fn from_row(row: &rusqlite::Row) -> Result<Self, DBError> {
        let signer_signature_hash = Sha512Trunc256Sum::from_column(row, "signer_signature_hash")?;
        let added_time = row.get_unwrap(1);
        Ok(PendingBlockValidation {
            signer_signature_hash,
            added_time,
        })
    }
}

#[cfg(any(test, feature = "testing"))]
impl SignerDb {
    /// For tests, fetch all pending block validations
    pub fn get_all_pending_block_validations(
        &self,
    ) -> Result<Vec<PendingBlockValidation>, DBError> {
        let qry = "SELECT signer_signature_hash, added_time FROM block_validations_pending ORDER BY added_time ASC";
        query_rows(&self.db, qry, params![])
    }

    /// For tests, check if a pending block validation exists
    pub fn has_pending_block_validation(
        &self,
        sighash: &Sha512Trunc256Sum,
    ) -> Result<bool, DBError> {
        let qry = "SELECT signer_signature_hash FROM block_validations_pending WHERE signer_signature_hash = ?1";
        let args = params![sighash.to_string()];
        let sighash_opt: Option<String> = query_row(&self.db, qry, args)?;
        Ok(sighash_opt.is_some())
    }
}

/// Tests for SignerDb
#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;

    use blockstack_lib::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader};
    use blockstack_lib::chainstate::stacks::{
        StacksTransaction, TenureChangeCause, TenureChangePayload, TransactionAuth,
        TransactionVersion,
    };
    use clarity::types::chainstate::{StacksBlockId, StacksPrivateKey, StacksPublicKey};
    use clarity::util::hash::Hash160;
    use clarity::util::secp256k1::MessageSignature;
    use libsigner::{BlockProposal, BlockProposalData};

    use super::*;
    use crate::signerdb::NakamotoBlockVote;

    fn _wipe_db(db_path: &PathBuf) {
        if fs::metadata(db_path).is_ok() {
            fs::remove_file(db_path).unwrap();
        }
    }

    fn create_block_override(
        overrides: impl FnOnce(&mut BlockProposal),
    ) -> (BlockInfo, BlockProposal) {
        let header = NakamotoBlockHeader::empty();
        let block = NakamotoBlock {
            header,
            txs: vec![],
        };
        let mut block_proposal = BlockProposal {
            block,
            burn_height: 7,
            reward_cycle: 42,
            block_proposal_data: BlockProposalData::empty(),
        };
        overrides(&mut block_proposal);
        (BlockInfo::from(block_proposal.clone()), block_proposal)
    }

    fn create_block() -> (BlockInfo, BlockProposal) {
        create_block_override(|_| {})
    }

    fn tmp_db_path() -> PathBuf {
        std::env::temp_dir().join(format!(
            "stacks-signer-test-{}.sqlite",
            rand::random::<u64>()
        ))
    }

    fn test_basic_signer_db_with_path(db_path: impl AsRef<Path>) {
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let (block_info_1, block_proposal_1) = create_block_override(|b| {
            b.block.header.consensus_hash = ConsensusHash([0x01; 20]);
        });
        let (block_info_2, block_proposal_2) = create_block_override(|b| {
            b.block.header.consensus_hash = ConsensusHash([0x02; 20]);
        });
        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db");
        let block_info = db
            .block_lookup(&block_proposal_1.block.header.signer_signature_hash())
            .unwrap()
            .expect("Unable to get block from db");

        assert_eq!(BlockInfo::from(block_proposal_1), block_info);

        // Test looking up a block with an unknown hash
        let block_info = db
            .block_lookup(&block_proposal_2.block.header.signer_signature_hash())
            .unwrap();
        assert!(block_info.is_none());

        db.insert_block(&block_info_2)
            .expect("Unable to insert block into db");
        let block_info = db
            .block_lookup(&block_proposal_2.block.header.signer_signature_hash())
            .unwrap()
            .expect("Unable to get block from db");

        assert_eq!(BlockInfo::from(block_proposal_2), block_info);
    }

    #[test]
    fn test_basic_signer_db() {
        let db_path = tmp_db_path();
        eprintln!("db path is {}", &db_path.display());
        test_basic_signer_db_with_path(db_path)
    }

    #[test]
    fn test_basic_signer_db_in_memory() {
        test_basic_signer_db_with_path(":memory:")
    }

    #[test]
    fn test_update_block() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let (block_info, block_proposal) = create_block();
        db.insert_block(&block_info)
            .expect("Unable to insert block into db");

        let block_info = db
            .block_lookup(&block_proposal.block.header.signer_signature_hash())
            .unwrap()
            .expect("Unable to get block from db");

        assert_eq!(BlockInfo::from(block_proposal.clone()), block_info);

        let old_block_info = block_info;
        let old_block_proposal = block_proposal;

        let (mut block_info, block_proposal) = create_block_override(|b| {
            b.block.header.signer_signature =
                old_block_proposal.block.header.signer_signature.clone();
        });
        assert_eq!(
            block_info.signer_signature_hash(),
            old_block_info.signer_signature_hash()
        );
        let vote = NakamotoBlockVote {
            signer_signature_hash: Sha512Trunc256Sum([0x01; 32]),
            rejected: false,
        };
        block_info.vote = Some(vote.clone());
        db.insert_block(&block_info)
            .expect("Unable to insert block into db");

        let block_info = db
            .block_lookup(&block_proposal.block.header.signer_signature_hash())
            .unwrap()
            .expect("Unable to get block from db");

        assert_ne!(old_block_info, block_info);
        assert_eq!(block_info.vote, Some(vote));
    }

    #[test]
    fn get_first_signed_block() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let (mut block_info, block_proposal) = create_block();
        db.insert_block(&block_info).unwrap();

        assert!(db
            .get_first_signed_block_in_tenure(&block_proposal.block.header.consensus_hash)
            .unwrap()
            .is_none());

        block_info
            .mark_locally_accepted(false)
            .expect("Failed to mark block as locally accepted");
        db.insert_block(&block_info).unwrap();

        let fetched_info = db
            .get_first_signed_block_in_tenure(&block_proposal.block.header.consensus_hash)
            .unwrap()
            .unwrap();
        assert_eq!(fetched_info, block_info);
    }

    #[test]
    fn insert_burn_block_get_time() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let test_burn_hash = BurnchainHeaderHash([10; 32]);
        let stime = SystemTime::now();
        let time_to_epoch = stime
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        db.insert_burn_block(&test_burn_hash, 10, &stime).unwrap();

        let stored_time = db
            .get_burn_block_receive_time(&test_burn_hash)
            .unwrap()
            .unwrap();
        assert_eq!(stored_time, time_to_epoch);
    }

    #[test]
    fn test_write_signer_state() {
        let db_path = tmp_db_path();
        let db = SignerDb::new(db_path).expect("Failed to create signer db");
        let state_0 = vec![0];
        let state_1 = vec![1; 1024];

        db.insert_encrypted_signer_state(10, &state_0)
            .expect("Failed to insert signer state");

        db.insert_encrypted_signer_state(11, &state_1)
            .expect("Failed to insert signer state");

        assert_eq!(
            db.get_encrypted_signer_state(10)
                .expect("Failed to get signer state")
                .unwrap(),
            state_0
        );
        assert_eq!(
            db.get_encrypted_signer_state(11)
                .expect("Failed to get signer state")
                .unwrap(),
            state_1
        );
        assert!(db
            .get_encrypted_signer_state(12)
            .expect("Failed to get signer state")
            .is_none());
        assert!(db
            .get_encrypted_signer_state(9)
            .expect("Failed to get signer state")
            .is_none());
    }

    #[test]
    fn test_has_unprocessed_blocks() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let (mut block_info_1, _block_proposal) = create_block_override(|b| {
            b.block.header.miner_signature = MessageSignature([0x01; 65]);
            b.burn_height = 1;
        });
        let (mut block_info_2, _block_proposal) = create_block_override(|b| {
            b.block.header.miner_signature = MessageSignature([0x02; 65]);
            b.burn_height = 2;
        });

        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db");
        db.insert_block(&block_info_2)
            .expect("Unable to insert block into db");

        assert!(db
            .has_unprocessed_blocks(block_info_1.reward_cycle)
            .unwrap());

        block_info_1.state = BlockState::LocallyRejected;

        db.insert_block(&block_info_1)
            .expect("Unable to update block in db");

        assert!(db
            .has_unprocessed_blocks(block_info_1.reward_cycle)
            .unwrap());

        block_info_2.state = BlockState::LocallyAccepted;

        db.insert_block(&block_info_2)
            .expect("Unable to update block in db");

        assert!(!db
            .has_unprocessed_blocks(block_info_1.reward_cycle)
            .unwrap());
    }

    #[test]
    fn test_sqlite_version() {
        let db_path = tmp_db_path();
        let db = SignerDb::new(db_path).expect("Failed to create signer db");
        assert_eq!(
            query_row(&db.db, "SELECT sqlite_version()", []).unwrap(),
            Some("3.45.0".to_string())
        );
    }

    #[test]
    fn add_and_get_block_signatures() {
        let db_path = tmp_db_path();
        let db = SignerDb::new(db_path).expect("Failed to create signer db");

        let block_id = Sha512Trunc256Sum::from_data("foo".as_bytes());
        let sig1 = MessageSignature([0x11; 65]);
        let sig2 = MessageSignature([0x22; 65]);

        assert_eq!(db.get_block_signatures(&block_id).unwrap(), vec![]);

        db.add_block_signature(&block_id, &sig1).unwrap();
        assert_eq!(db.get_block_signatures(&block_id).unwrap(), vec![sig1]);

        db.add_block_signature(&block_id, &sig2).unwrap();
        assert_eq!(
            db.get_block_signatures(&block_id).unwrap(),
            vec![sig1, sig2]
        );
    }

    #[test]
    fn test_and_set_block_broadcasted() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");

        let (block_info_1, _block_proposal) = create_block_override(|b| {
            b.block.header.miner_signature = MessageSignature([0x01; 65]);
            b.burn_height = 1;
        });

        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db");

        assert!(db
            .get_block_broadcasted(&block_info_1.signer_signature_hash())
            .unwrap()
            .is_none());
        assert_eq!(
            db.block_lookup(&block_info_1.signer_signature_hash())
                .expect("Unable to get block from db")
                .expect("Unable to get block from db")
                .state,
            BlockState::Unprocessed
        );
        assert!(db
            .get_last_globally_accepted_block(&block_info_1.block.header.consensus_hash)
            .unwrap()
            .is_none());
        db.set_block_broadcasted(&block_info_1.signer_signature_hash(), 12345)
            .unwrap();
        assert_eq!(
            db.block_lookup(&block_info_1.signer_signature_hash())
                .expect("Unable to get block from db")
                .expect("Unable to get block from db")
                .state,
            BlockState::Unprocessed
        );
        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db a second time");

        assert_eq!(
            db.get_block_broadcasted(&block_info_1.signer_signature_hash())
                .unwrap()
                .unwrap(),
            12345
        );
    }

    #[test]
    fn state_machine() {
        let (mut block, _) = create_block();
        assert_eq!(block.state, BlockState::Unprocessed);
        assert!(block.check_state(BlockState::Unprocessed));
        assert!(block.check_state(BlockState::LocallyAccepted));
        assert!(block.check_state(BlockState::LocallyRejected));
        assert!(block.check_state(BlockState::GloballyAccepted));
        assert!(block.check_state(BlockState::GloballyRejected));

        block.move_to(BlockState::LocallyAccepted).unwrap();
        assert_eq!(block.state, BlockState::LocallyAccepted);
        assert!(!block.check_state(BlockState::Unprocessed));
        assert!(block.check_state(BlockState::LocallyAccepted));
        assert!(block.check_state(BlockState::LocallyRejected));
        assert!(block.check_state(BlockState::GloballyAccepted));
        assert!(block.check_state(BlockState::GloballyRejected));

        block.move_to(BlockState::LocallyRejected).unwrap();
        assert!(!block.check_state(BlockState::Unprocessed));
        assert!(block.check_state(BlockState::LocallyAccepted));
        assert!(block.check_state(BlockState::LocallyRejected));
        assert!(block.check_state(BlockState::GloballyAccepted));
        assert!(block.check_state(BlockState::GloballyRejected));

        block.move_to(BlockState::GloballyAccepted).unwrap();
        assert_eq!(block.state, BlockState::GloballyAccepted);
        assert!(!block.check_state(BlockState::Unprocessed));
        assert!(!block.check_state(BlockState::LocallyAccepted));
        assert!(!block.check_state(BlockState::LocallyRejected));
        assert!(block.check_state(BlockState::GloballyAccepted));
        assert!(!block.check_state(BlockState::GloballyRejected));

        // Must manually override as will not be able to move from GloballyAccepted to GloballyRejected
        block.state = BlockState::GloballyRejected;
        assert!(!block.check_state(BlockState::Unprocessed));
        assert!(!block.check_state(BlockState::LocallyAccepted));
        assert!(!block.check_state(BlockState::LocallyRejected));
        assert!(!block.check_state(BlockState::GloballyAccepted));
        assert!(block.check_state(BlockState::GloballyRejected));
    }

    #[test]
    fn test_get_canonical_tip() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");

        let (mut block_info_1, _block_proposal_1) = create_block_override(|b| {
            b.block.header.miner_signature = MessageSignature([0x01; 65]);
            b.block.header.chain_length = 1;
            b.burn_height = 1;
        });

        let (mut block_info_2, _block_proposal_2) = create_block_override(|b| {
            b.block.header.miner_signature = MessageSignature([0x02; 65]);
            b.block.header.chain_length = 2;
            b.burn_height = 2;
        });

        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db");
        db.insert_block(&block_info_2)
            .expect("Unable to insert block into db");

        assert!(db.get_canonical_tip().unwrap().is_none());

        block_info_1
            .mark_globally_accepted()
            .expect("Failed to mark block as globally accepted");
        db.insert_block(&block_info_1)
            .expect("Unable to insert block into db");

        assert_eq!(db.get_canonical_tip().unwrap().unwrap(), block_info_1);

        block_info_2
            .mark_globally_accepted()
            .expect("Failed to mark block as globally accepted");
        db.insert_block(&block_info_2)
            .expect("Unable to insert block into db");

        assert_eq!(db.get_canonical_tip().unwrap().unwrap(), block_info_2);
    }

    #[test]
    fn get_accepted_blocks() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let consensus_hash_1 = ConsensusHash([0x01; 20]);
        let consensus_hash_2 = ConsensusHash([0x02; 20]);
        let consensus_hash_3 = ConsensusHash([0x03; 20]);
        let (mut block_info_1, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x01; 65]);
            b.block.header.chain_length = 1;
            b.burn_height = 1;
        });
        let (mut block_info_2, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x02; 65]);
            b.block.header.chain_length = 2;
            b.burn_height = 2;
        });
        let (mut block_info_3, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x03; 65]);
            b.block.header.chain_length = 3;
            b.burn_height = 3;
        });
        let (mut block_info_4, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_2;
            b.block.header.miner_signature = MessageSignature([0x03; 65]);
            b.block.header.chain_length = 3;
            b.burn_height = 4;
        });
        block_info_1.mark_globally_accepted().unwrap();
        block_info_2.mark_locally_accepted(false).unwrap();
        block_info_3.mark_locally_accepted(false).unwrap();
        block_info_4.mark_globally_accepted().unwrap();

        db.insert_block(&block_info_1).unwrap();
        db.insert_block(&block_info_2).unwrap();
        db.insert_block(&block_info_3).unwrap();
        db.insert_block(&block_info_4).unwrap();

        // Verify tenure consensus_hash_1
        let block_info = db
            .get_last_accepted_block(&consensus_hash_1)
            .unwrap()
            .unwrap();
        assert_eq!(block_info, block_info_3);
        let block_info = db
            .get_last_globally_accepted_block(&consensus_hash_1)
            .unwrap()
            .unwrap();
        assert_eq!(block_info, block_info_1);

        // Verify tenure consensus_hash_2
        let block_info = db
            .get_last_accepted_block(&consensus_hash_2)
            .unwrap()
            .unwrap();
        assert_eq!(block_info, block_info_4);
        let block_info = db
            .get_last_globally_accepted_block(&consensus_hash_2)
            .unwrap()
            .unwrap();
        assert_eq!(block_info, block_info_4);

        // Verify tenure consensus_hash_3
        assert!(db
            .get_last_accepted_block(&consensus_hash_3)
            .unwrap()
            .is_none());
        assert!(db
            .get_last_globally_accepted_block(&consensus_hash_3)
            .unwrap()
            .is_none());
    }

    fn generate_tenure_blocks() -> Vec<BlockInfo> {
        let tenure_change_payload = TenureChangePayload {
            tenure_consensus_hash: ConsensusHash([0x04; 20]), // same as in nakamoto header
            prev_tenure_consensus_hash: ConsensusHash([0x01; 20]),
            burn_view_consensus_hash: ConsensusHash([0x04; 20]),
            previous_tenure_end: StacksBlockId([0x03; 32]),
            previous_tenure_blocks: 1,
            cause: TenureChangeCause::BlockFound,
            pubkey_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(
                &StacksPrivateKey::random(),
            )),
        };
        let tenure_change_tx_payload = TransactionPayload::TenureChange(tenure_change_payload);
        let tenure_change_tx = StacksTransaction::new(
            TransactionVersion::Testnet,
            TransactionAuth::from_p2pkh(&StacksPrivateKey::random()).unwrap(),
            tenure_change_tx_payload,
        );

        let consensus_hash_1 = ConsensusHash([0x01; 20]);
        let consensus_hash_2 = ConsensusHash([0x02; 20]);
        let (mut block_info_1, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x01; 65]);
            b.block.header.chain_length = 1;
            b.burn_height = 1;
        });
        block_info_1.state = BlockState::GloballyAccepted;
        block_info_1.block.txs.push(tenure_change_tx.clone());
        block_info_1.validation_time_ms = Some(1000);
        block_info_1.proposed_time = get_epoch_time_secs() + 500;

        let (mut block_info_2, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x02; 65]);
            b.block.header.chain_length = 2;
            b.burn_height = 2;
        });
        block_info_2.state = BlockState::GloballyAccepted;
        block_info_2.validation_time_ms = Some(2000);
        block_info_2.proposed_time = block_info_1.proposed_time + 5;

        let (mut block_info_3, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x03; 65]);
            b.block.header.chain_length = 3;
            b.burn_height = 2;
        });
        block_info_3.state = BlockState::GloballyAccepted;
        block_info_3.block.txs.push(tenure_change_tx);
        block_info_3.validation_time_ms = Some(5000);
        block_info_3.proposed_time = block_info_1.proposed_time + 10;

        // This should have no effect on the time calculations as its not a globally accepted block
        let (mut block_info_4, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.miner_signature = MessageSignature([0x04; 65]);
            b.block.header.chain_length = 3;
            b.burn_height = 2;
        });
        block_info_4.state = BlockState::LocallyAccepted;
        block_info_4.validation_time_ms = Some(9000);
        block_info_4.proposed_time = block_info_1.proposed_time + 15;

        let (mut block_info_5, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_2;
            b.block.header.miner_signature = MessageSignature([0x05; 65]);
            b.block.header.chain_length = 4;
            b.burn_height = 3;
        });
        block_info_5.state = BlockState::GloballyAccepted;
        block_info_5.validation_time_ms = Some(20000);
        block_info_5.proposed_time = block_info_1.proposed_time + 20;

        // This should have no effect on the time calculations as its not a globally accepted block
        let (mut block_info_6, _block_proposal) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_2;
            b.block.header.miner_signature = MessageSignature([0x06; 65]);
            b.block.header.chain_length = 5;
            b.burn_height = 3;
        });
        block_info_6.state = BlockState::LocallyAccepted;
        block_info_6.validation_time_ms = Some(40000);
        block_info_6.proposed_time = block_info_1.proposed_time + 25;

        vec![
            block_info_1,
            block_info_2,
            block_info_3,
            block_info_4,
            block_info_5,
            block_info_6,
        ]
    }

    #[test]
    fn tenure_times() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let block_infos = generate_tenure_blocks();
        let consensus_hash_1 = block_infos[0].block.header.consensus_hash;
        let consensus_hash_2 = block_infos.last().unwrap().block.header.consensus_hash;
        let consensus_hash_3 = ConsensusHash([0x03; 20]);

        db.insert_block(&block_infos[0]).unwrap();
        db.insert_block(&block_infos[1]).unwrap();

        // Verify tenure consensus_hash_1
        let (start_time, processing_time) = db.get_tenure_times(&consensus_hash_1).unwrap();
        assert_eq!(start_time, block_infos[0].proposed_time);
        assert_eq!(processing_time, 3000);

        db.insert_block(&block_infos[2]).unwrap();
        db.insert_block(&block_infos[3]).unwrap();

        let (start_time, processing_time) = db.get_tenure_times(&consensus_hash_1).unwrap();
        assert_eq!(start_time, block_infos[2].proposed_time);
        assert_eq!(processing_time, 5000);

        db.insert_block(&block_infos[4]).unwrap();
        db.insert_block(&block_infos[5]).unwrap();

        // Verify tenure consensus_hash_2
        let (start_time, processing_time) = db.get_tenure_times(&consensus_hash_2).unwrap();
        assert_eq!(start_time, block_infos[4].proposed_time);
        assert_eq!(processing_time, 20000);

        // Verify tenure consensus_hash_3 (unknown hash)
        let (start_time, validation_time) = db.get_tenure_times(&consensus_hash_3).unwrap();
        assert!(start_time < block_infos[0].proposed_time, "Should have been generated from get_epoch_time_secs() making it much older than our artificially late proposal times");
        assert_eq!(validation_time, 0);
    }

    #[test]
    fn tenure_extend_timestamp() {
        let db_path = tmp_db_path();
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");

        let block_infos = generate_tenure_blocks();
        let mut unknown_block = block_infos[0].block.clone();
        unknown_block.header.consensus_hash = ConsensusHash([0x03; 20]);

        db.insert_block(&block_infos[0]).unwrap();
        db.insert_block(&block_infos[1]).unwrap();

        let tenure_idle_timeout = Duration::from_secs(10);
        // Verify tenure consensus_hash_1
        let timestamp_hash_1_before =
            db.calculate_tenure_extend_timestamp(tenure_idle_timeout, &block_infos[0].block, true);
        assert_eq!(
            timestamp_hash_1_before,
            block_infos[0]
                .proposed_time
                .saturating_add(tenure_idle_timeout.as_secs())
                .saturating_add(3)
        );

        db.insert_block(&block_infos[2]).unwrap();
        db.insert_block(&block_infos[3]).unwrap();

        let timestamp_hash_1_after =
            db.calculate_tenure_extend_timestamp(tenure_idle_timeout, &block_infos[0].block, true);

        assert_eq!(
            timestamp_hash_1_after,
            block_infos[2]
                .proposed_time
                .saturating_add(tenure_idle_timeout.as_secs())
                .saturating_add(5)
        );

        db.insert_block(&block_infos[4]).unwrap();
        db.insert_block(&block_infos[5]).unwrap();

        // Verify tenure consensus_hash_2
        let timestamp_hash_2 = db.calculate_tenure_extend_timestamp(
            tenure_idle_timeout,
            &block_infos.last().unwrap().block,
            true,
        );
        assert_eq!(
            timestamp_hash_2,
            block_infos[4]
                .proposed_time
                .saturating_add(tenure_idle_timeout.as_secs())
                .saturating_add(20)
        );

        let now = get_epoch_time_secs().saturating_add(tenure_idle_timeout.as_secs());
        let timestamp_hash_2_no_tenure_extend =
            db.calculate_tenure_extend_timestamp(tenure_idle_timeout, &block_infos[0].block, false);
        assert_ne!(timestamp_hash_2, timestamp_hash_2_no_tenure_extend);
        assert!(now < timestamp_hash_2_no_tenure_extend);

        // Verify tenure consensus_hash_3 (unknown hash)
        let timestamp_hash_3 =
            db.calculate_tenure_extend_timestamp(tenure_idle_timeout, &unknown_block, true);
        assert!(
            timestamp_hash_3.saturating_add(tenure_idle_timeout.as_secs())
                < block_infos[0].proposed_time
        );
    }

    #[test]
    fn test_get_and_remove_pending_block_validation() {
        let db_path = tmp_db_path();
        let db = SignerDb::new(db_path).expect("Failed to create signer db");

        let pending_hash = db.get_and_remove_pending_block_validation().unwrap();
        assert!(pending_hash.is_none());

        db.insert_pending_block_validation(&Sha512Trunc256Sum([0x01; 32]), 1000)
            .unwrap();
        db.insert_pending_block_validation(&Sha512Trunc256Sum([0x02; 32]), 2000)
            .unwrap();
        db.insert_pending_block_validation(&Sha512Trunc256Sum([0x03; 32]), 3000)
            .unwrap();

        let pending_hash = db.get_and_remove_pending_block_validation().unwrap();
        assert_eq!(pending_hash, Some(Sha512Trunc256Sum([0x01; 32])));

        let pendings = db.get_all_pending_block_validations().unwrap();
        assert_eq!(pendings.len(), 2);

        let pending_hash = db.get_and_remove_pending_block_validation().unwrap();
        assert_eq!(pending_hash, Some(Sha512Trunc256Sum([0x02; 32])));

        let pendings = db.get_all_pending_block_validations().unwrap();
        assert_eq!(pendings.len(), 1);

        let pending_hash = db.get_and_remove_pending_block_validation().unwrap();
        assert_eq!(pending_hash, Some(Sha512Trunc256Sum([0x03; 32])));

        let pendings = db.get_all_pending_block_validations().unwrap();
        assert!(pendings.is_empty());
    }

    #[test]
    fn has_signed_block() {
        let db_path = tmp_db_path();
        let consensus_hash_1 = ConsensusHash([0x01; 20]);
        let consensus_hash_2 = ConsensusHash([0x02; 20]);
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");
        let (mut block_info, _) = create_block_override(|b| {
            b.block.header.consensus_hash = consensus_hash_1;
            b.block.header.chain_length = 1;
        });

        assert!(!db.has_signed_block_in_tenure(&consensus_hash_1).unwrap());
        assert!(!db.has_signed_block_in_tenure(&consensus_hash_2).unwrap());

        block_info.signed_over = true;
        db.insert_block(&block_info).unwrap();

        assert!(db.has_signed_block_in_tenure(&consensus_hash_1).unwrap());
        assert!(!db.has_signed_block_in_tenure(&consensus_hash_2).unwrap());

        block_info.block.header.consensus_hash = consensus_hash_2;
        block_info.block.header.chain_length = 2;
        block_info.signed_over = false;

        db.insert_block(&block_info).unwrap();

        assert!(db.has_signed_block_in_tenure(&consensus_hash_1).unwrap());
        assert!(!db.has_signed_block_in_tenure(&consensus_hash_2).unwrap());

        block_info.signed_over = true;

        db.insert_block(&block_info).unwrap();

        assert!(db.has_signed_block_in_tenure(&consensus_hash_1).unwrap());
        assert!(db.has_signed_block_in_tenure(&consensus_hash_2).unwrap());
    }

    #[test]
    fn update_last_activity() {
        let db_path = tmp_db_path();
        let consensus_hash_1 = ConsensusHash([0x01; 20]);
        let consensus_hash_2 = ConsensusHash([0x02; 20]);
        let mut db = SignerDb::new(db_path).expect("Failed to create signer db");

        assert!(db
            .get_last_activity_time(&consensus_hash_1)
            .unwrap()
            .is_none());
        assert!(db
            .get_last_activity_time(&consensus_hash_2)
            .unwrap()
            .is_none());

        let time = get_epoch_time_secs();
        db.update_last_activity_time(&consensus_hash_1, time)
            .unwrap();
        let retrieved_time = db
            .get_last_activity_time(&consensus_hash_1)
            .unwrap()
            .unwrap();
        assert_eq!(time, retrieved_time);
        assert!(db
            .get_last_activity_time(&consensus_hash_2)
            .unwrap()
            .is_none());
    }
}
