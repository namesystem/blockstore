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

//! Subcommands used by `stacks-inspect` binary

use std::cell::LazyCell;
use std::path::PathBuf;
use std::time::Instant;
use std::{env, fs, io, process, thread};

use clarity::types::chainstate::SortitionId;
use db::ChainstateTx;
use regex::Regex;
use rusqlite::{Connection, OpenFlags};
use stacks_common::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, StacksBlockId};
use stacks_common::types::sqlite::NO_PARAMS;

use crate::burnchains::db::BurnchainDB;
use crate::burnchains::PoxConstants;
use crate::chainstate::burn::db::sortdb::{SortitionDB, SortitionHandle, SortitionHandleContext};
use crate::chainstate::burn::{BlockSnapshot, ConsensusHash};
use crate::chainstate::stacks::db::blocks::StagingBlock;
use crate::chainstate::stacks::db::{StacksBlockHeaderTypes, StacksChainState, StacksHeaderInfo};
use crate::chainstate::stacks::miner::*;
use crate::chainstate::stacks::*;
use crate::clarity_vm::clarity::ClarityInstance;
use crate::core::*;
use crate::util_lib::db::IndexDBTx;

/// Can be used with CLI commands to support non-mainnet chainstate
/// Allows integration testing of these functions
pub struct StacksChainConfig {
    pub chain_id: u32,
    pub first_block_height: u64,
    pub first_burn_header_hash: BurnchainHeaderHash,
    pub first_burn_header_timestamp: u64,
    pub pox_constants: PoxConstants,
    pub epochs: Vec<StacksEpoch>,
}

impl StacksChainConfig {
    pub fn default_mainnet() -> Self {
        Self {
            chain_id: CHAIN_ID_MAINNET,
            first_block_height: BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT,
            first_burn_header_hash: BurnchainHeaderHash::from_hex(BITCOIN_MAINNET_FIRST_BLOCK_HASH)
                .unwrap(),
            first_burn_header_timestamp: BITCOIN_MAINNET_FIRST_BLOCK_TIMESTAMP.into(),
            pox_constants: PoxConstants::mainnet_default(),
            epochs: STACKS_EPOCHS_MAINNET.to_vec(),
        }
    }
}

const STACKS_CHAIN_CONFIG_DEFAULT_MAINNET: LazyCell<StacksChainConfig> =
    LazyCell::new(StacksChainConfig::default_mainnet);

/// Replay blocks from chainstate database
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
pub fn command_replay_block(argv: &[String], conf: Option<&StacksChainConfig>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <database-path>");
        eprintln!("  {n} <database-path> prefix <index-block-hash-prefix>");
        eprintln!("  {n} <database-path> index-range <start-block> <end-block>");
        eprintln!("  {n} <database-path> range <start-block> <end-block>");
        eprintln!("  {n} <database-path> <first|last> <block-count>");
        process::exit(1);
    };
    let start = Instant::now();
    let db_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());
    let mode = argv.get(2).map(String::as_str);
    let staging_blocks_db_path = format!("{db_path}/chainstate/vm/index.sqlite");
    let conn =
        Connection::open_with_flags(&staging_blocks_db_path, OpenFlags::SQLITE_OPEN_READ_ONLY)
            .unwrap();

    let query = match mode {
        Some("prefix") => format!(
			"SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 AND index_block_hash LIKE \"{}%\"",
			argv[3]
		),
        Some("first") => format!(
			"SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {}",
			argv[3]
		),
        Some("range") => {
            let arg4 = argv[3]
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let arg5 = argv[4].parse::<u64>().expect("<end-block> not a valid u64");
            let start = arg4.saturating_sub(1);
            let blocks = arg5.saturating_sub(arg4);
            format!("SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height ASC LIMIT {start}, {blocks}")
        }
        Some("index-range") => {
            let start = argv[3]
                .parse::<u64>()
                .expect("<start_block> not a valid u64");
            let end = argv[4].parse::<u64>().expect("<end-block> not a valid u64");
            let blocks = end.saturating_sub(start);
            format!("SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY index_block_hash ASC LIMIT {start}, {blocks}")
        }
        Some("last") => format!(
			"SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0 ORDER BY height DESC LIMIT {}",
			argv[3]
		),
        Some(_) => print_help_and_exit(),
        // Default to ALL blocks
        None => "SELECT index_block_hash FROM staging_blocks WHERE orphaned = 0".into(),
    };

    let mut stmt = conn.prepare(&query).unwrap();
    let mut hashes_set = stmt.query(NO_PARAMS).unwrap();

    let mut index_block_hashes: Vec<String> = vec![];
    while let Ok(Some(row)) = hashes_set.next() {
        index_block_hashes.push(row.get(0).unwrap());
    }

    let total = index_block_hashes.len();
    println!("Will check {total} blocks");
    for (i, index_block_hash) in index_block_hashes.iter().enumerate() {
        if i % 100 == 0 {
            println!("Checked {i}...");
        }
        replay_staging_block(db_path, index_block_hash, conf);
    }
    println!("Finished. run_time_seconds = {}", start.elapsed().as_secs());
}

/// Replay mock mined blocks from JSON files
/// Terminates on error using `process::exit()`
///
/// Arguments:
///  - `argv`: Args in CLI format: `<command-name> [args...]`
///  - `conf`: Optional config for running on non-mainnet chainstate
pub fn command_replay_mock_mining(argv: &[String], conf: Option<&StacksChainConfig>) {
    let print_help_and_exit = || -> ! {
        let n = &argv[0];
        eprintln!("Usage:");
        eprintln!("  {n} <database-path> <mock-mined-blocks-path>");
        process::exit(1);
    };

    // Process CLI args
    let db_path = argv.get(1).unwrap_or_else(|| print_help_and_exit());

    let blocks_path = argv
        .get(2)
        .map(PathBuf::from)
        .map(fs::canonicalize)
        .transpose()
        .unwrap_or_else(|e| panic!("Not a valid path: {e}"))
        .unwrap_or_else(|| print_help_and_exit());

    // Validate directory path
    if !blocks_path.is_dir() {
        panic!("{blocks_path:?} is not a valid directory");
    }

    // Read entries in directory
    let dir_entries = blocks_path
        .read_dir()
        .unwrap_or_else(|e| panic!("Failed to read {blocks_path:?}: {e}"))
        .filter_map(|e| e.ok());

    // Get filenames, filtering out anything that isn't a regular file
    let filenames = dir_entries.filter_map(|e| match e.file_type() {
        Ok(t) if t.is_file() => e.file_name().into_string().ok(),
        _ => None,
    });

    // Get vec of (block_height, filename), to prepare for sorting
    //
    // NOTE: Trusting the filename is not ideal. We could sort on data read from the file,
    // but that requires reading all files
    let re = Regex::new(r"^([0-9]+)\.json$").unwrap();
    let mut indexed_files = filenames
        .filter_map(|filename| {
            // Use regex to extract block number from filename
            let Some(cap) = re.captures(&filename) else {
                debug!("Regex capture failed on {filename}");
                return None;
            };
            // cap.get(0) return entire filename
            // cap.get(1) return block number
            let i = 1;
            let Some(m) = cap.get(i) else {
                debug!("cap.get({i}) failed on {filename} match");
                return None;
            };
            let Ok(bh) = m.as_str().parse::<u64>() else {
                debug!("parse::<u64>() failed on '{}'", m.as_str());
                return None;
            };
            Some((bh, filename))
        })
        .collect::<Vec<_>>();

    // Sort by block height
    indexed_files.sort_by_key(|(bh, _)| *bh);

    if indexed_files.is_empty() {
        panic!("No block files found in {blocks_path:?}");
    }

    info!(
        "Replaying {} blocks starting at {}",
        indexed_files.len(),
        indexed_files[0].0
    );

    for (bh, filename) in indexed_files {
        let filepath = blocks_path.join(filename);
        let block = AssembledAnchorBlock::deserialize_from_file(&filepath)
            .unwrap_or_else(|e| panic!("Error reading block {bh} from file: {e}"));
        info!("Replaying block from {filepath:?}";
            "block_height" => bh,
            "block" => ?block
        );
        replay_mock_mined_block(&db_path, block, conf);
    }
}

/// Fetch and process a `StagingBlock` from database and call `replay_block()` to validate
fn replay_staging_block(
    db_path: &str,
    index_block_hash_hex: &str,
    conf: Option<&StacksChainConfig>,
) {
    let block_id = StacksBlockId::from_hex(index_block_hash_hex).unwrap();
    let chain_state_path = format!("{db_path}/chainstate/");
    let sort_db_path = format!("{db_path}/burnchain/sortition");
    let burn_db_path = format!("{db_path}/burnchain/burnchain.sqlite");
    let burnchain_blocks_db = BurnchainDB::open(&burn_db_path, false).unwrap();

    let default_conf = STACKS_CHAIN_CONFIG_DEFAULT_MAINNET;
    let conf = conf.unwrap_or(&default_conf);

    let mainnet = conf.chain_id == CHAIN_ID_MAINNET;
    let (mut chainstate, _) =
        StacksChainState::open(mainnet, conf.chain_id, &chain_state_path, None).unwrap();

    let mut sortdb = SortitionDB::connect(
        &sort_db_path,
        conf.first_block_height,
        &conf.first_burn_header_hash,
        conf.first_burn_header_timestamp,
        &conf.epochs,
        conf.pox_constants.clone(),
        None,
        true,
    )
    .unwrap();
    let sort_tx = sortdb.tx_begin_at_tip();

    let blocks_path = chainstate.blocks_path.clone();
    let (mut chainstate_tx, clarity_instance) = chainstate
        .chainstate_tx_begin()
        .expect("Failed to start chainstate tx");
    let mut next_staging_block =
        StacksChainState::load_staging_block_info(&chainstate_tx.tx, &block_id)
            .expect("Failed to load staging block data")
            .expect("No such index block hash in block database");

    next_staging_block.block_data = StacksChainState::load_block_bytes(
        &blocks_path,
        &next_staging_block.consensus_hash,
        &next_staging_block.anchored_block_hash,
    )
    .unwrap()
    .unwrap_or_default();

    let Some(parent_header_info) =
        StacksChainState::get_parent_header_info(&mut chainstate_tx, &next_staging_block).unwrap()
    else {
        println!("Failed to load parent head info for block: {index_block_hash_hex}");
        return;
    };

    let block =
        StacksChainState::extract_stacks_block(&next_staging_block).expect("Failed to get block");
    let block_size = next_staging_block.block_data.len() as u64;

    replay_block(
        sort_tx,
        chainstate_tx,
        clarity_instance,
        &burnchain_blocks_db,
        &parent_header_info,
        &next_staging_block.parent_microblock_hash,
        next_staging_block.parent_microblock_seq,
        &block_id,
        &block,
        block_size,
        &next_staging_block.consensus_hash,
        &next_staging_block.anchored_block_hash,
        next_staging_block.commit_burn,
        next_staging_block.sortition_burn,
    );
}

/// Process a mock mined block and call `replay_block()` to validate
fn replay_mock_mined_block(
    db_path: &str,
    block: AssembledAnchorBlock,
    conf: Option<&StacksChainConfig>,
) {
    let chain_state_path = format!("{db_path}/chainstate/");
    let sort_db_path = format!("{db_path}/burnchain/sortition");
    let burn_db_path = format!("{db_path}/burnchain/burnchain.sqlite");
    let burnchain_blocks_db = BurnchainDB::open(&burn_db_path, false).unwrap();

    let default_conf = STACKS_CHAIN_CONFIG_DEFAULT_MAINNET;
    let conf = conf.unwrap_or(&default_conf);

    let mainnet = conf.chain_id == CHAIN_ID_MAINNET;
    let (mut chainstate, _) =
        StacksChainState::open(mainnet, conf.chain_id, &chain_state_path, None).unwrap();

    let mut sortdb = SortitionDB::connect(
        &sort_db_path,
        conf.first_block_height,
        &conf.first_burn_header_hash,
        conf.first_burn_header_timestamp,
        &conf.epochs,
        conf.pox_constants.clone(),
        None,
        true,
    )
    .unwrap();
    let sort_tx = sortdb.tx_begin_at_tip();

    let (mut chainstate_tx, clarity_instance) = chainstate
        .chainstate_tx_begin()
        .expect("Failed to start chainstate tx");

    let block_consensus_hash = &block.consensus_hash;
    let block_hash = block.anchored_block.block_hash();
    let block_id = StacksBlockId::new(block_consensus_hash, &block_hash);
    let block_size = block
        .anchored_block
        .block_size()
        .map(u64::try_from)
        .unwrap_or_else(|e| panic!("Error serializing block {block_hash}: {e}"))
        .expect("u64 overflow");

    let Some(parent_header_info) = StacksChainState::get_anchored_block_header_info(
        &mut chainstate_tx,
        &block.parent_consensus_hash,
        &block.anchored_block.header.parent_block,
    )
    .unwrap() else {
        println!("Failed to load parent head info for block: {block_hash}");
        return;
    };

    replay_block(
        sort_tx,
        chainstate_tx,
        clarity_instance,
        &burnchain_blocks_db,
        &parent_header_info,
        &block.anchored_block.header.parent_microblock,
        block.anchored_block.header.parent_microblock_sequence,
        &block_id,
        &block.anchored_block,
        block_size,
        block_consensus_hash,
        &block_hash,
        // I think the burn is used for miner rewards but not necessary for validation
        0,
        0,
    );
}

/// Validate a block against chainstate
fn replay_block(
    mut sort_tx: IndexDBTx<SortitionHandleContext, SortitionId>,
    mut chainstate_tx: ChainstateTx,
    clarity_instance: &mut ClarityInstance,
    burnchain_blocks_db: &BurnchainDB,
    parent_header_info: &StacksHeaderInfo,
    parent_microblock_hash: &BlockHeaderHash,
    parent_microblock_seq: u16,
    block_id: &StacksBlockId,
    block: &StacksBlock,
    block_size: u64,
    block_consensus_hash: &ConsensusHash,
    block_hash: &BlockHeaderHash,
    block_commit_burn: u64,
    block_sortition_burn: u64,
) {
    let parent_block_header = match &parent_header_info.anchored_header {
        StacksBlockHeaderTypes::Epoch2(bh) => bh,
        StacksBlockHeaderTypes::Nakamoto(_) => panic!("Nakamoto blocks not supported yet"),
    };
    let parent_block_hash = parent_block_header.block_hash();

    let Some(next_microblocks) = StacksChainState::inner_find_parent_microblock_stream(
        &chainstate_tx.tx,
        &block_hash,
        &parent_block_hash,
        &parent_header_info.consensus_hash,
        parent_microblock_hash,
        parent_microblock_seq,
    )
    .unwrap() else {
        println!("No microblock stream found for {block_id}");
        return;
    };

    let (burn_header_hash, burn_header_height, burn_header_timestamp, _winning_block_txid) =
        match SortitionDB::get_block_snapshot_consensus(&sort_tx, &block_consensus_hash).unwrap() {
            Some(sn) => (
                sn.burn_header_hash,
                sn.block_height as u32,
                sn.burn_header_timestamp,
                sn.winning_block_txid,
            ),
            None => {
                // shouldn't happen
                panic!("CORRUPTION: staging block {block_consensus_hash}/{block_hash} does not correspond to a burn block");
            }
        };

    info!(
        "Process block {}/{} = {} in burn block {}, parent microblock {}",
        block_consensus_hash, block_hash, &block_id, &burn_header_hash, parent_microblock_hash,
    );

    if !StacksChainState::check_block_attachment(&parent_block_header, &block.header) {
        let msg = format!(
            "Invalid stacks block {}/{} -- does not attach to parent {}/{}",
            &block_consensus_hash,
            block.block_hash(),
            parent_block_header.block_hash(),
            &parent_header_info.consensus_hash
        );
        println!("{msg}");
        return;
    }

    // validation check -- validate parent microblocks and find the ones that connect the
    // block's parent to this block.
    let next_microblocks = StacksChainState::extract_connecting_microblocks(
        &parent_header_info,
        &block_consensus_hash,
        &block_hash,
        block,
        next_microblocks,
    )
    .unwrap();
    let (last_microblock_hash, last_microblock_seq) = match next_microblocks.len() {
        0 => (EMPTY_MICROBLOCK_PARENT_HASH.clone(), 0),
        _ => {
            let l = next_microblocks.len();
            (
                next_microblocks[l - 1].block_hash(),
                next_microblocks[l - 1].header.sequence,
            )
        }
    };
    assert_eq!(*parent_microblock_hash, last_microblock_hash);
    assert_eq!(parent_microblock_seq, last_microblock_seq);

    let block_am = StacksChainState::find_stacks_tip_affirmation_map(
        burnchain_blocks_db,
        sort_tx.tx(),
        block_consensus_hash,
        block_hash,
    )
    .unwrap();

    let pox_constants = sort_tx.context.pox_constants.clone();

    match StacksChainState::append_block(
        &mut chainstate_tx,
        clarity_instance,
        &mut sort_tx,
        &pox_constants,
        &parent_header_info,
        block_consensus_hash,
        &burn_header_hash,
        burn_header_height,
        burn_header_timestamp,
        &block,
        block_size,
        &next_microblocks,
        block_commit_burn,
        block_sortition_burn,
        block_am.weight(),
        true,
    ) {
        Ok((_receipt, _, _)) => {
            info!("Block processed successfully! block = {block_id}");
        }
        Err(e) => {
            println!("Failed processing block! block = {block_id}, error = {e:?}");
            process::exit(1);
        }
    };
}
