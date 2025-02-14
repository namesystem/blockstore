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
use core::fmt;
use std::io::Read;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError};
use std::sync::Arc;
#[cfg(test)]
use std::sync::LazyLock;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};
use std::{fs, thread};

use rand::{thread_rng, Rng};
use stacks::burnchains::{Burnchain, Txid};
use stacks::chainstate::burn::db::sortdb::{FindIter, SortitionDB};
use stacks::chainstate::burn::operations::leader_block_commit::{
    RewardSetInfo, BURN_BLOCK_MINED_AT_MODULUS,
};
use stacks::chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp,
};
use stacks::chainstate::burn::{BlockSnapshot, ConsensusHash};
use stacks::chainstate::nakamoto::coordinator::get_nakamoto_next_recipients;
use stacks::chainstate::nakamoto::{NakamotoBlockHeader, NakamotoChainState};
use stacks::chainstate::stacks::address::PoxAddress;
use stacks::chainstate::stacks::db::StacksChainState;
use stacks::chainstate::stacks::miner::{
    get_mining_spend_amount, signal_mining_blocked, signal_mining_ready,
};
use stacks::chainstate::stacks::Error as ChainstateError;
use stacks::core::mempool::MemPoolDB;
use stacks::core::STACKS_EPOCH_3_1_MARKER;
use stacks::monitoring::increment_stx_blocks_mined_counter;
use stacks::net::db::LocalPeer;
use stacks::net::p2p::NetworkHandle;
use stacks::net::relay::Relayer;
use stacks::net::NetworkResult;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksBlockId, StacksPublicKey, VRFSeed,
};
use stacks_common::types::StacksEpochId;
use stacks_common::util::get_epoch_time_ms;
use stacks_common::util::hash::Hash160;
#[cfg(test)]
use stacks_common::util::tests::TestFlag;
use stacks_common::util::vrf::VRFPublicKey;

use super::miner::MinerReason;
use super::{
    Config, Error as NakamotoNodeError, EventDispatcher, Keychain, BLOCK_PROCESSOR_STACK_SIZE,
};
use crate::burnchains::BurnchainController;
use crate::nakamoto_node::miner::{BlockMinerThread, MinerDirective};
use crate::neon_node::{
    fault_injection_skip_mining, open_chainstate_with_faults, LeaderKeyRegistrationState,
};
use crate::run_loop::nakamoto::{Globals, RunLoop};
use crate::run_loop::RegisteredKey;
use crate::BitcoinRegtestController;

#[cfg(test)]
/// Mutex to stall the relayer thread right before it creates a miner thread.
pub static TEST_MINER_THREAD_STALL: LazyLock<TestFlag<bool>> = LazyLock::new(TestFlag::default);

#[cfg(test)]
/// Mutex to stall the miner thread right after it starts up (does not block the relayer thread)
pub static TEST_MINER_THREAD_START_STALL: LazyLock<TestFlag<bool>> =
    LazyLock::new(TestFlag::default);

/// Command types for the Nakamoto relayer thread, issued to it by other threads
#[allow(clippy::large_enum_variant)]
pub enum RelayerDirective {
    /// Handle some new data that arrived on the network (such as blocks, transactions, and
    HandleNetResult(NetworkResult),
    /// A new burn block has been processed by the SortitionDB, check if this miner won sortition,
    ///  and if so, start the miner thread
    ProcessedBurnBlock(ConsensusHash, BurnchainHeaderHash, BlockHeaderHash),
    /// Either a new burn block has been processed (without a miner active yet) or a
    ///  nakamoto tenure's first block has been processed, so the relayer should issue
    ///  a block commit
    IssueBlockCommit(ConsensusHash, BlockHeaderHash),
    /// Try to register a VRF public key
    RegisterKey(BlockSnapshot),
    /// Stop the relayer thread
    Exit,
}

impl fmt::Display for RelayerDirective {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RelayerDirective::HandleNetResult(_) => write!(f, "HandleNetResult"),
            RelayerDirective::ProcessedBurnBlock(_, _, _) => write!(f, "ProcessedBurnBlock"),
            RelayerDirective::IssueBlockCommit(_, _) => write!(f, "IssueBlockCommit"),
            RelayerDirective::RegisterKey(_) => write!(f, "RegisterKey"),
            RelayerDirective::Exit => write!(f, "Exit"),
        }
    }
}

/// Last commitment data
/// This represents the tenure that the last-sent block-commit committed to.
pub struct LastCommit {
    /// block-commit sent
    block_commit: LeaderBlockCommitOp,
    /// the sortition tip at the time the block-commit was sent
    burn_tip: BlockSnapshot,
    /// the stacks tip at the time the block-commit was sent
    stacks_tip: StacksBlockId,
    /// the tenure consensus hash for the tip's tenure
    tenure_consensus_hash: ConsensusHash,
    /// the start-block hash of the tip's tenure
    #[allow(dead_code)]
    start_block_hash: BlockHeaderHash,
    /// What is the epoch in which this was sent?
    epoch_id: StacksEpochId,
    /// commit txid (to be filled in on submission)
    txid: Option<Txid>,
}

/// Timer used to check whether or not a burnchain view change has
///  waited long enough to issue a burn commit without a tenure change
enum BurnBlockCommitTimer {
    /// The timer hasn't been set: we aren't currently waiting to submit a commit
    NotSet,
    /// The timer is set, and has been set for a particular burn view
    Set {
        start_time: Instant,
        /// This is the canonical sortition at the time that the
        ///  timer began. This is used to make sure we aren't reusing
        ///  the timeout between sortitions
        burn_tip: ConsensusHash,
    },
}

impl BurnBlockCommitTimer {
    /// Check if the timer has expired (and was set).
    /// If the timer was not set, then set it.
    ///
    /// Returns true if the timer expired
    fn is_ready(&mut self, current_burn_tip: &ConsensusHash, timeout: &Duration) -> bool {
        let needs_reset = match self {
            BurnBlockCommitTimer::NotSet => true,
            BurnBlockCommitTimer::Set {
                start_time,
                burn_tip,
            } => {
                if burn_tip != current_burn_tip {
                    true
                } else {
                    if start_time.elapsed() > *timeout {
                        // timer expired and was pointed at the correct burn tip
                        // so we can just return is_ready here
                        return true;
                    }
                    // timer didn't expire, but the burn tip was correct, so
                    //  we don't need to reset the timer
                    false
                }
            }
        };
        if needs_reset {
            info!(
                "Starting new tenure timeout";
                "timeout_secs" => timeout.as_secs(),
                "burn_tip_ch" => %current_burn_tip
            );
            *self = Self::Set {
                burn_tip: current_burn_tip.clone(),
                start_time: Instant::now(),
            };
        }

        debug!(
            "Waiting for tenure timeout before issuing commit";
            "elapsed_secs" => self.elapsed_secs(),
            "burn_tip_ch" => %current_burn_tip
        );

        false
    }

    /// At what time, if set, would this timer be ready?
    fn deadline(&self, timeout: &Duration) -> Option<Instant> {
        match self {
            BurnBlockCommitTimer::NotSet => None,
            BurnBlockCommitTimer::Set { start_time, .. } => Some(*start_time + *timeout),
        }
    }

    /// How much time has elapsed on the current timer?
    fn elapsed_secs(&self) -> u64 {
        match self {
            BurnBlockCommitTimer::NotSet => 0,
            BurnBlockCommitTimer::Set { start_time, .. } => start_time.elapsed().as_secs(),
        }
    }
}

impl LastCommit {
    pub fn new(
        commit: LeaderBlockCommitOp,
        burn_tip: BlockSnapshot,
        stacks_tip: StacksBlockId,
        tenure_consensus_hash: ConsensusHash,
        start_block_hash: BlockHeaderHash,
        epoch_id: StacksEpochId,
    ) -> Self {
        Self {
            block_commit: commit,
            burn_tip,
            stacks_tip,
            tenure_consensus_hash,
            start_block_hash,
            epoch_id,
            txid: None,
        }
    }

    /// Get the commit
    pub fn get_block_commit(&self) -> &LeaderBlockCommitOp {
        &self.block_commit
    }

    /// What's the parent tenure's tenure-start block hash?
    pub fn parent_tenure_id(&self) -> StacksBlockId {
        StacksBlockId(self.block_commit.block_header_hash.0)
    }

    /// What's the stacks tip at the time of commit?
    pub fn get_stacks_tip(&self) -> &StacksBlockId {
        &self.stacks_tip
    }

    /// What's the burn tip at the time of commit?
    pub fn get_burn_tip(&self) -> &BlockSnapshot {
        &self.burn_tip
    }

    /// What's the epoch in which this was sent?
    pub fn get_epoch_id(&self) -> &StacksEpochId {
        &self.epoch_id
    }

    /// Get the tenure ID of the tenure this commit builds on
    pub fn get_tenure_id(&self) -> &ConsensusHash {
        &self.tenure_consensus_hash
    }

    /// Set our txid
    pub fn set_txid(&mut self, txid: &Txid) {
        self.txid = Some(*txid);
    }
}

pub type MinerThreadJoinHandle = JoinHandle<Result<(), NakamotoNodeError>>;

/// Miner thread join handle, as well as an "abort" flag to force the miner thread to exit when it
/// is blocked.
pub struct MinerStopHandle {
    /// The join handle itself
    join_handle: MinerThreadJoinHandle,
    /// The relayer-set abort flag
    abort_flag: Arc<AtomicBool>,
}

impl MinerStopHandle {
    pub fn new(join_handle: MinerThreadJoinHandle, abort_flag: Arc<AtomicBool>) -> Self {
        Self {
            join_handle,
            abort_flag,
        }
    }

    /// Get a ref to the inner thread object
    pub fn inner_thread(&self) -> &std::thread::Thread {
        self.join_handle.thread()
    }

    /// Destroy this stop handle to get the thread join handle
    pub fn into_inner(self) -> MinerThreadJoinHandle {
        self.join_handle
    }

    /// Stop the inner miner thread.
    /// Blocks the miner, and sets the abort flag so that a blocked miner will error out.
    pub fn stop(self, globals: &Globals) -> Result<(), NakamotoNodeError> {
        let my_id = thread::current().id();
        let prior_thread_id = self.inner_thread().id();
        debug!(
            "[Thread {:?}]: Stopping prior miner thread ID {:?}",
            &my_id, &prior_thread_id
        );

        self.abort_flag.store(true, Ordering::SeqCst);
        globals.block_miner();

        let prior_miner = self.into_inner();
        let prior_miner_result = prior_miner.join().map_err(|_| {
            error!("Miner: failed to join prior miner");
            ChainstateError::MinerAborted
        })?;
        debug!("Stopped prior miner thread ID {:?}", &prior_thread_id);
        if let Err(e) = prior_miner_result {
            // it's okay if the prior miner thread exited with an error.
            // in many cases this is expected (i.e., a burnchain block occurred)
            // if some error condition should be handled though, this is the place
            //  to do that handling.
            debug!("Prior mining thread exited with: {e:?}");
        }

        globals.unblock_miner();
        Ok(())
    }
}

/// The reason for issuing a tenure extend
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TenureExtendReason {
    /// There was an empty sortition
    EmptySortition,
    /// There was a bad sortition winner
    BadSortitionWinner,
    /// We are waiting for the current winner to produce a block.
    UnresponsiveWinner,
}

/// Information necessary to determine when to extend a tenure
#[derive(Clone)]
pub struct TenureExtendTime {
    /// The time at which we determined that we should tenure-extend
    time: Instant,
    /// The amount of time we should wait before tenure-extending
    timeout: Duration,
    /// The reason for tenure-extending
    reason: TenureExtendReason,
}

impl TenureExtendTime {
    /// Create a new `TenureExtendTime` for an UnresponsiveWinner with the specified `timeout`
    pub fn unresponsive_winner(timeout: Duration) -> Self {
        Self {
            time: Instant::now(),
            timeout,
            reason: TenureExtendReason::UnresponsiveWinner,
        }
    }

    /// Create a new `TenureExtendTime` with the provided `reason` and no `timeout`
    pub fn immediate(reason: TenureExtendReason) -> Self {
        Self {
            time: Instant::now(),
            timeout: Duration::from_millis(0),
            reason,
        }
    }

    /// Should we attempt to tenure-extend?
    pub fn should_extend(&self) -> bool {
        // We set the time, but have we waited long enough?
        self.time.elapsed() > self.timeout
    }

    // Amount of time elapsed since we decided to tenure-extend
    pub fn elapsed(&self) -> Duration {
        self.time.elapsed()
    }

    // The timeout specified when we decided to tenure-extend
    pub fn timeout(&self) -> Duration {
        self.timeout
    }

    /// The reason for tenure-extending
    pub fn reason(&self) -> &TenureExtendReason {
        &self.reason
    }

    /// Update the timeout for this `TenureExtendTime` and reset the time
    pub fn refresh(&mut self, timeout: Duration) {
        self.timeout = timeout;
        self.time = Instant::now();
    }
}

/// Relayer thread
/// * accepts network results and stores blocks and microblocks
/// * forwards new blocks, microblocks, and transactions to the p2p thread
/// * issues (and re-issues) block commits to participate as a miner
/// * processes burnchain state to determine if selected as a miner
/// * if mining, runs the miner and broadcasts blocks (via a subordinate MinerThread)
pub struct RelayerThread {
    /// Node config
    pub(crate) config: Config,
    /// Handle to the sortition DB
    sortdb: SortitionDB,
    /// Handle to the chainstate DB
    chainstate: StacksChainState,
    /// Handle to the mempool DB
    mempool: MemPoolDB,
    /// Handle to global state and inter-thread communication channels
    pub(crate) globals: Globals,
    /// Authoritative copy of the keychain state
    pub(crate) keychain: Keychain,
    /// Burnchian configuration
    pub(crate) burnchain: Burnchain,
    /// height of last VRF key registration request
    last_vrf_key_burn_height: Option<u64>,
    /// client to the burnchain (used only for sending block-commits)
    pub(crate) bitcoin_controller: BitcoinRegtestController,
    /// client to the event dispatcher
    pub(crate) event_dispatcher: EventDispatcher,
    /// copy of the local peer state
    local_peer: LocalPeer,
    /// last observed burnchain block height from the p2p thread (obtained from network results)
    last_network_block_height: u64,
    /// time at which we observed a change in the network block height (epoch time in millis)
    last_network_block_height_ts: u128,
    /// last observed number of downloader state-machine passes from the p2p thread (obtained from
    /// network results)
    last_network_download_passes: u64,
    /// last observed number of inventory state-machine passes from the p2p thread (obtained from
    /// network results)
    last_network_inv_passes: u64,
    /// minimum number of downloader state-machine passes that must take place before mining (this
    /// is used to ensure that the p2p thread attempts to download new Stacks block data before
    /// this thread tries to mine a block)
    min_network_download_passes: u64,
    /// minimum number of inventory state-machine passes that must take place before mining (this
    /// is used to ensure that the p2p thread attempts to download new Stacks block data before
    /// this thread tries to mine a block)
    min_network_inv_passes: u64,

    /// Inner relayer instance for forwarding broadcasted data back to the p2p thread for dispatch
    /// to neighbors
    relayer: Relayer,

    /// handle to the subordinate miner thread
    miner_thread: Option<MinerStopHandle>,
    /// miner thread's burn view
    miner_thread_burn_view: Option<BlockSnapshot>,

    /// The relayer thread reads directives from the relay_rcv, but it also periodically wakes up
    ///  to check if it should issue a block commit or try to register a VRF key
    next_initiative: Instant,
    is_miner: bool,
    /// Information about the last-sent block commit, and the relayer's view of the chain at the
    /// time it was sent.
    last_committed: Option<LastCommit>,
    /// Timeout for waiting for the first block in a tenure before submitting a block commit
    new_tenure_timeout: BurnBlockCommitTimer,
    /// Time to wait before attempting a tenure extend
    tenure_extend_time: Option<TenureExtendTime>,
}

impl RelayerThread {
    /// Instantiate relayer thread.
    /// Uses `runloop` to obtain globals, config, and `is_miner`` status
    pub fn new(
        runloop: &RunLoop,
        local_peer: LocalPeer,
        relayer: Relayer,
        keychain: Keychain,
    ) -> RelayerThread {
        let config = runloop.config().clone();
        let globals = runloop.get_globals();
        let burn_db_path = config.get_burn_db_file_path();
        let is_miner = runloop.is_miner();

        let sortdb = SortitionDB::open(&burn_db_path, true, runloop.get_burnchain().pox_constants)
            .expect("FATAL: failed to open burnchain DB");

        let chainstate =
            open_chainstate_with_faults(&config).expect("FATAL: failed to open chainstate DB");

        let mempool = config
            .connect_mempool_db()
            .expect("Database failure opening mempool");

        let bitcoin_controller = BitcoinRegtestController::new_dummy(config.clone());

        let next_initiative_delay = config.node.next_initiative_delay;

        RelayerThread {
            config,
            sortdb,
            chainstate,
            mempool,
            globals,
            keychain,
            burnchain: runloop.get_burnchain(),
            last_vrf_key_burn_height: None,
            bitcoin_controller,
            event_dispatcher: runloop.get_event_dispatcher(),
            local_peer,

            last_network_block_height: 0,
            last_network_block_height_ts: 0,
            last_network_download_passes: 0,
            min_network_download_passes: 0,
            last_network_inv_passes: 0,
            min_network_inv_passes: 0,

            relayer,

            miner_thread: None,
            miner_thread_burn_view: None,
            is_miner,
            next_initiative: Instant::now() + Duration::from_millis(next_initiative_delay),
            last_committed: None,
            new_tenure_timeout: BurnBlockCommitTimer::NotSet,
            tenure_extend_time: None,
        }
    }

    /// Get a handle to the p2p thread
    pub fn get_p2p_handle(&self) -> NetworkHandle {
        self.relayer.get_p2p_handle()
    }

    /// have we waited for the right conditions under which to start mining a block off of our
    /// chain tip?
    fn has_waited_for_latest_blocks(&self) -> bool {
        // a network download pass took place
        self.min_network_download_passes <= self.last_network_download_passes
        // we waited long enough for a download pass, but timed out waiting
        || self.last_network_block_height_ts + (self.config.node.wait_time_for_blocks as u128) < get_epoch_time_ms()
        // we're not supposed to wait at all
        || !self.config.miner.wait_for_block_download
    }

    /// Handle a NetworkResult from the p2p/http state machine.  Usually this is the act of
    /// * preprocessing and storing new blocks and microblocks
    /// * relaying blocks, microblocks, and transacctions
    /// * updating unconfirmed state views
    pub fn process_network_result(&mut self, mut net_result: NetworkResult) {
        debug!(
            "Relayer: Handle network result (from {})",
            net_result.burn_height
        );

        if self.last_network_block_height != net_result.burn_height {
            // burnchain advanced; disable mining until we also do a download pass.
            self.last_network_block_height = net_result.burn_height;
            self.min_network_download_passes = net_result.num_download_passes + 1;
            self.min_network_inv_passes = net_result.num_inv_sync_passes + 1;
            self.last_network_block_height_ts = get_epoch_time_ms();
        }

        let net_receipts = self
            .relayer
            .process_network_result(
                &self.local_peer,
                &mut net_result,
                &self.burnchain,
                &mut self.sortdb,
                &mut self.chainstate,
                &mut self.mempool,
                self.globals.sync_comms.get_ibd(),
                Some(&self.globals.coord_comms),
                Some(&self.event_dispatcher),
            )
            .expect("BUG: failure processing network results");

        if net_receipts.num_new_blocks > 0 {
            // if we received any new block data that could invalidate our view of the chain tip,
            // then stop mining until we process it
            debug!("Relayer: block mining to process newly-arrived blocks or microblocks");
            signal_mining_blocked(self.globals.get_miner_status());
        }

        let mempool_txs_added = net_receipts.mempool_txs_added.len();
        if mempool_txs_added > 0 {
            self.event_dispatcher
                .process_new_mempool_txs(net_receipts.mempool_txs_added);
        }

        // Dispatch retrieved attachments, if any.
        if net_result.has_attachments() {
            self.event_dispatcher
                .process_new_attachments(&net_result.attachments);
        }

        // resume mining if we blocked it, and if we've done the requisite download
        // passes
        self.last_network_download_passes = net_result.num_download_passes;
        self.last_network_inv_passes = net_result.num_inv_sync_passes;
        if self.has_waited_for_latest_blocks() {
            debug!("Relayer: did a download pass, so unblocking mining");
            signal_mining_ready(self.globals.get_miner_status());
        }
    }

    /// Choose a miner directive for a sortition with a winner.
    ///
    /// The decision process is a little tricky, because the right decision depends on:
    /// * whether or not we won the _given_ sortition (`sn`)
    /// * whether or not we won the sortition that started the ongoing Stacks tenure
    /// * whether or not the ongoing Stacks tenure is at or descended from the last-winning
    /// sortition
    ///
    /// Specifically:
    ///
    /// If we won the given sortition `sn`, then we can start mining immediately with a `BlockFound`
    /// tenure-change.  Otherwise, if we won the tenure which started the ongoing Stacks tenure
    /// (i.e. we're the active miner), then we _may_ start mining after a timeout _if_ the winning
    /// miner (not us) fails to submit a `BlockFound` tenure-change block for `sn`.
    fn choose_directive_sortition_with_winner(
        &mut self,
        sn: BlockSnapshot,
        mining_pkh: Hash160,
        committed_index_hash: StacksBlockId,
    ) -> Option<MinerDirective> {
        let won_sortition = sn.miner_pk_hash == Some(mining_pkh);
        if won_sortition || self.config.get_node_config(false).mock_mining {
            // a sortition happenend, and we won
            info!("Won sortition; begin tenure.";
                    "winning_sortition" => %sn.consensus_hash);
            return Some(MinerDirective::BeginTenure {
                parent_tenure_start: committed_index_hash,
                burnchain_tip: sn.clone(),
                election_block: sn,
                late: false,
            });
        }

        // a sortition happened, but we didn't win. Check if we won the ongoing tenure.
        debug!(
            "Relayer: did not win sortition {}, so stopping tenure",
            &sn.sortition
        );
        let (canonical_stacks_tip_ch, _) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortdb.conn())
                .expect("FATAL: failed to query sortition DB for stacks tip");
        let canonical_stacks_snapshot =
            SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), &canonical_stacks_tip_ch)
                .expect("FATAL: failed to query sortiiton DB for epoch")
                .expect("FATAL: no sortition for canonical stacks tip");

        let won_ongoing_tenure_sortition =
            canonical_stacks_snapshot.miner_pk_hash == Some(mining_pkh);
        if won_ongoing_tenure_sortition {
            // we won the current ongoing tenure, but not the most recent sortition. Should we attempt to extend immediately or wait for the incoming miner?
            if let Ok(has_higher) = Self::has_higher_sortition_commits_to_stacks_tip_tenure(
                &self.sortdb,
                &mut self.chainstate,
                &sn,
                &canonical_stacks_snapshot,
            ) {
                if has_higher {
                    debug!("Relayer: Did not win current sortition but won the prior valid sortition. Will attempt to extend tenure after allowing the new miner some time to come online.";
                            "tenure_extend_wait_timeout_ms" => self.config.miner.tenure_extend_wait_timeout.as_millis(),
                    );
                    self.tenure_extend_time = Some(TenureExtendTime::unresponsive_winner(
                        self.config.miner.tenure_extend_wait_timeout,
                    ));
                } else {
                    info!("Relayer: no valid sortition since our last winning sortition. Will extend tenure.");
                    self.tenure_extend_time = Some(TenureExtendTime::immediate(
                        TenureExtendReason::BadSortitionWinner,
                    ));
                }
            }
        }
        return Some(MinerDirective::StopTenure);
    }

    /// Choose a miner directive for a sortition with no winner.
    ///
    /// The decision process is a little tricky, because the right decision depends on:
    /// * whether or not we won the sortition that started the ongoing Stacks tenure
    /// * whether or not we won the last sortition with a winner
    /// * whether or not the last sortition winner has produced a Stacks block
    /// * whether or not the ongoing Stacks tenure is at or descended from the last-winning
    /// sortition
    ///
    /// Find out who won the last sortition with a winner.  If it was us, and if we haven't yet
    /// submitted a `BlockFound` tenure-change for it (which can happen if this given sortition is
    /// from a flash block), then start mining immediately with a "late" `BlockFound` tenure, _and_
    /// prepare to start mining right afterwards with an `Extended` tenure-change so as to represent
    /// the given sortition `sn`'s burn view in the Stacks chain.
    ///
    /// Otherwise, if did not win the last-winning sortition, then check to see if we're the ongoing
    /// Stack's tenure's miner. If so, then we _may_ start mining after a timeout _if_ the winner of
    /// the last-good sortition (not us) fails to submit a `BlockFound` tenure-change block.
    /// This can happen if `sn` was a flash block, and the remote miner has yet to process it.
    ///
    /// We won't always be able to mine -- for example, this could be an empty sortition, but the
    /// parent block could be an epoch 2 block.  In this case, the right thing to do is to wait for
    /// the next block-commit.
    fn choose_directive_sortition_without_winner(
        &mut self,
        sn: BlockSnapshot,
        mining_pk: Hash160,
    ) -> Option<MinerDirective> {
        let (canonical_stacks_tip_ch, _) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortdb.conn())
                .expect("FATAL: failed to query sortition DB for stacks tip");
        let canonical_stacks_snapshot =
            SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), &canonical_stacks_tip_ch)
                .expect("FATAL: failed to query sortiiton DB for epoch")
                .expect("FATAL: no sortition for canonical stacks tip");

        // find out what epoch the Stacks tip is in.
        // If it's in epoch 2.x, then we must always begin a new tenure, but we can't do so
        // right now since this sortition has no winner.
        let cur_epoch = SortitionDB::get_stacks_epoch(
            self.sortdb.conn(),
            canonical_stacks_snapshot.block_height,
        )
        .expect("FATAL: failed to query sortition DB for epoch")
        .expect("FATAL: no epoch defined for existing sortition");

        if cur_epoch.epoch_id < StacksEpochId::Epoch30 {
            debug!(
                "As of sortition {}, there has not yet been a Nakamoto tip. Cannot mine.",
                &canonical_stacks_snapshot.consensus_hash
            );
            return None;
        }

        // find out who won the last non-empty sortition. It may have been us.
        let Ok(last_winning_snapshot) = Self::get_last_winning_snapshot(&self.sortdb, &sn)
            .inspect_err(|e| {
                warn!("Relayer: Failed to load last winning snapshot: {e:?}");
            })
        else {
            // this should be unreachable, but don't tempt fate.
            info!("Relayer: No prior snapshots have a winning sortition. Will not try to mine.");
            return None;
        };

        let won_last_winning_snapshot = last_winning_snapshot.miner_pk_hash == Some(mining_pk);
        if won_last_winning_snapshot {
            debug!(
                "Relayer: we won the last winning sortition {}",
                &last_winning_snapshot.consensus_hash
            );

            if Self::need_block_found(&canonical_stacks_snapshot, &last_winning_snapshot) {
                info!(
                    "Relayer: will submit late BlockFound for {}",
                    &last_winning_snapshot.consensus_hash
                );
                // prepare to immediately extend after our BlockFound gets mined.
                self.tenure_extend_time = Some(TenureExtendTime::immediate(
                    TenureExtendReason::EmptySortition,
                ));
                return Some(MinerDirective::BeginTenure {
                    parent_tenure_start: StacksBlockId(
                        last_winning_snapshot.winning_stacks_block_hash.clone().0,
                    ),
                    burnchain_tip: sn,
                    election_block: last_winning_snapshot,
                    late: true,
                });
            }
            let tip_is_last_winning_snapshot = canonical_stacks_snapshot.block_height
                == last_winning_snapshot.block_height
                && canonical_stacks_snapshot.consensus_hash == last_winning_snapshot.consensus_hash;

            if tip_is_last_winning_snapshot {
                // this is the ongoing tenure snapshot. A BlockFound has already been issued. We
                // can instead opt to Extend immediately
                info!("Relayer: BlockFound already issued for the last winning sortition. Will extend tenure.");
                return Some(MinerDirective::ContinueTenure {
                    new_burn_view: sn.consensus_hash,
                });
            }
        }

        let won_ongoing_tenure_sortition =
            canonical_stacks_snapshot.miner_pk_hash == Some(mining_pk);
        if won_ongoing_tenure_sortition {
            info!("Relayer: No sortition, but we produced the canonical Stacks tip. Will extend tenure.");
            if !won_last_winning_snapshot {
                // delay trying to continue since the last snasphot with a sortition was won
                // by someone else -- there's a chance that this other miner will produce a
                // BlockFound in the interim.
                debug!("Relayer: Did not win last winning snapshot despite mining the ongoing tenure. Will attempt to extend tenure after allowing the new miner some time to produce a block.");
                self.tenure_extend_time = Some(TenureExtendTime::unresponsive_winner(
                    self.config.miner.tenure_extend_wait_timeout,
                ));
                return None;
            }
            return Some(MinerDirective::ContinueTenure {
                new_burn_view: sn.consensus_hash,
            });
        }

        info!("Relayer: No sortition, and we did not produce the last Stacks tip. Will not mine.");
        return None;
    }

    /// Determine if we the current tenure winner needs to issue a BlockFound.
    /// Assumes the caller has already checked that the last-winning snapshot was won by us.
    ///
    /// Returns true if the stacks tip's snapshot is an ancestor of the last-won sortition
    /// Returns false otherwise.
    fn need_block_found(
        canonical_stacks_snapshot: &BlockSnapshot,
        last_winning_snapshot: &BlockSnapshot,
    ) -> bool {
        // we won the last non-empty sortition. Has there been a BlockFound issued for it?
        // This would be true if the stacks tip's tenure is at or descends from this snapshot.
        // If there has _not_ been a BlockFound, then we should issue one.
        if canonical_stacks_snapshot.block_height > last_winning_snapshot.block_height {
            // stacks tip is ahead of this snapshot, so no BlockFound can be issued.
            test_debug!(
                "Stacks_tip_sn.block_height ({}) > last_winning_snapshot.block_height ({})",
                canonical_stacks_snapshot.block_height,
                last_winning_snapshot.block_height
            );
            false
        } else if canonical_stacks_snapshot.block_height == last_winning_snapshot.block_height
            && canonical_stacks_snapshot.consensus_hash == last_winning_snapshot.consensus_hash
        {
            // this is the ongoing tenure snapshot. A BlockFound has already been issued.
            test_debug!(
                "Ongoing tenure {} already represents last-winning snapshot",
                &canonical_stacks_snapshot.consensus_hash
            );
            false
        } else {
            // The stacks tip is behind the last-won sortition, so a BlockFound is still needed.
            true
        }
    }

    /// Given the pointer to a recently processed sortition, see if we won the sortition, and
    /// determine what miner action (if any) to take.
    ///
    /// Returns a directive to the relayer thread to either start, stop, or continue a tenure, if
    /// this sortition matches the sortition tip and we have a parent to build atop.
    ///
    /// Otherwise, returns None, meaning no action will be taken.
    // This method is covered by the e2e bitcoind tests, which do not show up
    //  in mutant coverage.
    #[cfg_attr(test, mutants::skip)]
    fn process_sortition(
        &mut self,
        consensus_hash: ConsensusHash,
        burn_hash: BurnchainHeaderHash,
        committed_index_hash: StacksBlockId,
    ) -> Result<Option<MinerDirective>, NakamotoNodeError> {
        let sn = SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), &consensus_hash)
            .expect("FATAL: failed to query sortition DB")
            .expect("FATAL: unknown consensus hash");

        let was_winning_pkh = if let (Some(ref winning_pkh), Some(ref my_pkh)) =
            (sn.miner_pk_hash, self.get_mining_key_pkh())
        {
            winning_pkh == my_pkh
        } else {
            false
        };

        let won_sortition = sn.sortition && was_winning_pkh;
        if won_sortition {
            increment_stx_blocks_mined_counter();
        }
        self.globals.set_last_sortition(sn.clone());
        self.globals.counters.bump_blocks_processed();
        self.globals.counters.bump_sortitions_processed();

        // there may be a bufferred stacks block to process, so wake up the coordinator to check
        self.globals.coord_comms.announce_new_stacks_block();

        info!(
            "Relayer: Process sortition";
            "sortition_ch" => %consensus_hash,
            "burn_hash" => %burn_hash,
            "burn_height" => sn.block_height,
            "winning_txid" => %sn.winning_block_txid,
            "committed_parent" => %committed_index_hash,
            "won_sortition?" => won_sortition,
        );

        let cur_sn = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())
            .expect("FATAL: failed to query sortition DB");

        if cur_sn.consensus_hash != consensus_hash {
            info!("Relayer: Current sortition {} is ahead of processed sortition {consensus_hash}; taking no action", &cur_sn.consensus_hash);
            self.globals
                .raise_initiative("process_sortition".to_string());
            return Ok(None);
        }
        // Reset the tenure extend time
        self.tenure_extend_time = None;
        let Some(mining_pk) = self.get_mining_key_pkh() else {
            debug!("No mining key, will not mine");
            return Ok(None);
        };
        let directive_opt = if sn.sortition {
            self.choose_directive_sortition_with_winner(sn, mining_pk, committed_index_hash)
        } else {
            self.choose_directive_sortition_without_winner(sn, mining_pk)
        };
        debug!(
            "Relayer: Processed sortition {}: Miner directive is {:?}",
            &consensus_hash, &directive_opt
        );
        Ok(directive_opt)
    }

    /// Constructs and returns a LeaderKeyRegisterOp out of the provided params
    fn make_key_register_op(
        vrf_public_key: VRFPublicKey,
        consensus_hash: &ConsensusHash,
        miner_pkh: &Hash160,
    ) -> BlockstackOperationType {
        BlockstackOperationType::LeaderKeyRegister(LeaderKeyRegisterOp {
            public_key: vrf_public_key,
            memo: miner_pkh.as_bytes().to_vec(),
            consensus_hash: *consensus_hash,
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        })
    }

    /// Create and broadcast a VRF public key registration transaction.
    /// Returns true if we succeed in doing so; false if not.
    pub fn rotate_vrf_and_register(&mut self, burn_block: &BlockSnapshot) {
        if self.last_vrf_key_burn_height.is_some() {
            // already in-flight
            return;
        }
        let cur_epoch = SortitionDB::get_stacks_epoch(self.sortdb.conn(), burn_block.block_height)
            .expect("FATAL: failed to query sortition DB")
            .expect("FATAL: no epoch defined")
            .epoch_id;
        let (vrf_pk, _) = self.keychain.make_vrf_keypair(burn_block.block_height);
        let burnchain_tip_consensus_hash = &burn_block.consensus_hash;
        let miner_pkh = self.keychain.get_nakamoto_pkh();

        debug!(
            "Submitting LeaderKeyRegister";
            "vrf_pk" => vrf_pk.to_hex(),
            "burn_block_height" => burn_block.block_height,
            "miner_pkh" => miner_pkh.to_hex(),
        );

        let op = Self::make_key_register_op(vrf_pk, burnchain_tip_consensus_hash, &miner_pkh);

        let mut op_signer = self.keychain.generate_op_signer();
        if let Ok(txid) = self
            .bitcoin_controller
            .submit_operation(cur_epoch, op, &mut op_signer, 1)
        {
            // advance key registration state
            self.last_vrf_key_burn_height = Some(burn_block.block_height);
            self.globals
                .set_pending_leader_key_registration(burn_block.block_height, txid);
            self.globals.counters.bump_naka_submitted_vrfs();
        }
    }

    /// Produce the block-commit for this upcoming tenure, if we can.
    ///
    /// Takes the Nakamoto chain tip (consensus hash, block header hash).
    ///
    /// Returns the (the most recent burn snapshot, the most recent stakcs tip, the commit-op) on success
    /// Returns None if we fail somehow.
    ///
    /// TODO: unit test
    pub(crate) fn make_block_commit(
        &mut self,
        tip_block_ch: &ConsensusHash,
        tip_block_bh: &BlockHeaderHash,
    ) -> Result<LastCommit, NakamotoNodeError> {
        let tip_block_id = StacksBlockId::new(tip_block_ch, tip_block_bh);
        let sort_tip = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())
            .map_err(|_| NakamotoNodeError::SnapshotNotFoundForChainTip)?;

        let stacks_tip = StacksBlockId::new(tip_block_ch, tip_block_bh);

        // sanity check -- this block must exist and have been processed locally
        let highest_tenure_start_block_header = NakamotoChainState::get_tenure_start_block_header(
            &mut self.chainstate.index_conn(),
            &stacks_tip,
            tip_block_ch,
        )
        .map_err(|e| {
            error!(
                "Relayer: Failed to get tenure-start block header for stacks tip {stacks_tip}: {e:?}"
            );
            NakamotoNodeError::ParentNotFound
        })?
        .ok_or_else(|| {
            error!(
                "Relayer: Failed to find tenure-start block header for stacks tip {stacks_tip}"
            );
            NakamotoNodeError::ParentNotFound
        })?;

        // load the VRF proof generated in this tenure, so we can use it to seed the VRF in the
        // upcoming tenure.  This may be an epoch2x VRF proof.
        let tip_vrf_proof = NakamotoChainState::get_block_vrf_proof(
            &mut self.chainstate.index_conn(),
            &stacks_tip,
            tip_block_ch,
        )
        .map_err(|e| {
            error!("Failed to load VRF proof for {tip_block_ch} off of {stacks_tip}: {e:?}");
            NakamotoNodeError::ParentNotFound
        })?
        .ok_or_else(|| {
            error!("No block VRF proof for {tip_block_ch} off of {stacks_tip}");
            NakamotoNodeError::ParentNotFound
        })?;

        // let's figure out the recipient set!
        let recipients = get_nakamoto_next_recipients(
            &sort_tip,
            &mut self.sortdb,
            &mut self.chainstate,
            &stacks_tip,
            &self.burnchain,
        )
        .map_err(|e| {
            error!("Relayer: Failure fetching recipient set: {e:?}");
            NakamotoNodeError::SnapshotNotFoundForChainTip
        })?;

        let commit_outs = if self
            .burnchain
            .is_in_prepare_phase(sort_tip.block_height + 1)
        {
            vec![PoxAddress::standard_burn_address(self.config.is_mainnet())]
        } else {
            RewardSetInfo::into_commit_outs(recipients, self.config.is_mainnet())
        };

        // find the sortition that kicked off this tenure (it may be different from the sortition
        // tip, such as when there is no sortition or when the miner of the current sortition never
        // produces a block).  This is used to find the parent block-commit of the block-commit
        // we'll submit.
        let Ok(Some(tip_tenure_sortition)) =
            SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), tip_block_ch)
        else {
            error!("Relayer: Failed to lookup the block snapshot of highest tenure ID"; "tenure_consensus_hash" => %tip_block_ch);
            return Err(NakamotoNodeError::ParentNotFound);
        };

        // find the parent block-commit of this commit, so we can find the parent vtxindex
        // if the parent is a shadow block, then the vtxindex would be 0.
        let commit_parent_block_burn_height = tip_tenure_sortition.block_height;
        let commit_parent_winning_vtxindex = if let Ok(Some(parent_winning_tx)) =
            SortitionDB::get_block_commit(
                self.sortdb.conn(),
                &tip_tenure_sortition.winning_block_txid,
                &tip_tenure_sortition.sortition_id,
            ) {
            parent_winning_tx.vtxindex
        } else {
            debug!(
                "{}/{} ({}) must be a shadow block, since it has no block-commit",
                &tip_block_bh, &tip_block_ch, &tip_block_id
            );
            let Ok(Some(parent_version)) =
                NakamotoChainState::get_nakamoto_block_version(self.chainstate.db(), &tip_block_id)
            else {
                error!(
                    "Relayer: Failed to lookup block version of {}",
                    &tip_block_id
                );
                return Err(NakamotoNodeError::ParentNotFound);
            };

            if !NakamotoBlockHeader::is_shadow_block_version(parent_version) {
                error!(
                    "Relayer: parent block-commit of {} not found, and it is not a shadow block",
                    &tip_block_id
                );
                return Err(NakamotoNodeError::ParentNotFound);
            }

            0
        };

        // epoch in which this commit will be sent (affects how the burnchain client processes it)
        let Ok(Some(target_epoch)) =
            SortitionDB::get_stacks_epoch(self.sortdb.conn(), sort_tip.block_height + 1)
        else {
            error!("Relayer: Failed to lookup its epoch"; "target_height" => sort_tip.block_height + 1);
            return Err(NakamotoNodeError::SnapshotNotFoundForChainTip);
        };

        // amount of burnchain tokens (e.g. sats) we'll spend across the PoX outputs
        let burn_fee_cap = get_mining_spend_amount(self.globals.get_miner_status());

        // let's commit, but target the current burnchain tip with our modulus so the commit is
        // only valid if it lands in the targeted burnchain block height
        let burn_parent_modulus = u8::try_from(sort_tip.block_height % BURN_BLOCK_MINED_AT_MODULUS)
            .map_err(|_| {
                error!("Relayer: Block mining modulus is not u8");
                NakamotoNodeError::UnexpectedChainState
            })?;

        // burnchain signer for this commit
        let sender = self.keychain.get_burnchain_signer();

        // VRF key this commit uses (i.e. the one we registered)
        let key = self
            .globals
            .get_leader_key_registration_state()
            .get_active()
            .ok_or_else(|| NakamotoNodeError::NoVRFKeyActive)?;

        let commit = LeaderBlockCommitOp {
            // NOTE: to be filled in
            treatment: vec![],
            // NOTE: PoX sunset has been disabled prior to taking effect
            sunset_burn: 0,
            // block-commits in Nakamoto commit to the ongoing tenure's tenure-start block (which,
            // when processed, become the start-block of the tenure atop which this miner will
            // produce blocks)
            block_header_hash: BlockHeaderHash(
                highest_tenure_start_block_header.index_block_hash().0,
            ),
            // the rest of this is the same as epoch2x commits, modulo the new epoch marker
            burn_fee: burn_fee_cap,
            apparent_sender: sender,
            key_block_ptr: u32::try_from(key.block_height)
                .expect("FATAL: burn block height exceeded u32"),
            key_vtxindex: u16::try_from(key.op_vtxindex).expect("FATAL: vtxindex exceeded u16"),
            memo: vec![STACKS_EPOCH_3_1_MARKER],
            new_seed: VRFSeed::from_proof(&tip_vrf_proof),
            parent_block_ptr: u32::try_from(commit_parent_block_burn_height)
                .expect("FATAL: burn block height exceeded u32"),
            parent_vtxindex: u16::try_from(commit_parent_winning_vtxindex)
                .expect("FATAL: vtxindex exceeded u16"),
            burn_parent_modulus,
            commit_outs,

            // NOTE: to be filled in
            input: (Txid([0; 32]), 0),
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        };

        Ok(LastCommit::new(
            commit,
            sort_tip,
            stacks_tip,
            highest_tenure_start_block_header.consensus_hash,
            highest_tenure_start_block_header
                .anchored_header
                .block_hash(),
            target_epoch.epoch_id,
        ))
    }

    #[cfg(test)]
    fn fault_injection_stall_miner_startup() {
        if TEST_MINER_THREAD_STALL.get() {
            // Do an extra check just so we don't log EVERY time.
            warn!("Relayer miner thread startup is stalled due to testing directive to stall the miner");
            while TEST_MINER_THREAD_STALL.get() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            warn!(
                "Relayer miner thread startup is no longer stalled due to testing directive. Continuing..."
            );
        }
    }

    #[cfg(not(test))]
    fn fault_injection_stall_miner_startup() {}

    #[cfg(test)]
    fn fault_injection_stall_miner_thread_startup() {
        if TEST_MINER_THREAD_START_STALL.get() {
            // Do an extra check just so we don't log EVERY time.
            warn!("Miner thread startup is stalled due to testing directive");
            while TEST_MINER_THREAD_START_STALL.get() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            warn!(
                "Miner thread startup is no longer stalled due to testing directive. Continuing..."
            );
        }
    }

    #[cfg(not(test))]
    fn fault_injection_stall_miner_thread_startup() {}

    /// Create the block miner thread state.
    /// Only proceeds if all of the following are true:
    /// * the miner is not blocked
    /// * last_burn_block corresponds to the canonical sortition DB's chain tip
    /// * the time of issuance is sufficiently recent
    /// * there are no unprocessed stacks blocks in the staging DB
    /// * the relayer has already tried a download scan that included this sortition (which, if a block was found, would have placed it into the staging DB and marked it as unprocessed)
    /// * a miner thread is not running already
    fn create_block_miner(
        &mut self,
        registered_key: RegisteredKey,
        burn_election_block: BlockSnapshot,
        burn_tip: BlockSnapshot,
        parent_tenure_id: StacksBlockId,
        reason: MinerReason,
        burn_tip_at_start: &ConsensusHash,
    ) -> Result<BlockMinerThread, NakamotoNodeError> {
        if fault_injection_skip_mining(&self.config.node.rpc_bind, burn_tip.block_height) {
            debug!(
                "Relayer: fault injection skip mining at block height {}",
                burn_tip.block_height
            );
            return Err(NakamotoNodeError::FaultInjection);
        }
        Self::fault_injection_stall_miner_startup();

        let burn_header_hash = burn_tip.burn_header_hash;
        let burn_chain_sn = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())
            .expect("FATAL: failed to query sortition DB for canonical burn chain tip");

        let burn_chain_tip = burn_chain_sn.burn_header_hash;

        if &burn_chain_sn.consensus_hash != burn_tip_at_start {
            info!(
                "Relayer: Drop stale RunTenure for {burn_header_hash}: current sortition is for {burn_chain_tip}"
            );
            self.globals.counters.bump_missed_tenures();
            return Err(NakamotoNodeError::MissedMiningOpportunity);
        }

        debug!(
            "Relayer: Spawn tenure thread";
            "height" => burn_tip.block_height,
            "burn_header_hash" => %burn_header_hash,
            "parent_tenure_id" => %parent_tenure_id,
            "reason" => %reason,
            "burn_election_block.consensus_hash" => %burn_election_block.consensus_hash,
            "burn_tip.consensus_hash" => %burn_tip.consensus_hash,
        );

        let miner_thread_state = BlockMinerThread::new(
            self,
            registered_key,
            burn_election_block,
            burn_tip,
            parent_tenure_id,
            burn_tip_at_start,
            reason,
        );
        Ok(miner_thread_state)
    }

    fn start_new_tenure(
        &mut self,
        parent_tenure_start: StacksBlockId,
        block_election_snapshot: BlockSnapshot,
        burn_tip: BlockSnapshot,
        reason: MinerReason,
        burn_tip_at_start: &ConsensusHash,
    ) -> Result<(), NakamotoNodeError> {
        // when starting a new tenure, block the mining thread if its currently running.
        // the new mining thread will join it (so that the new mining thread stalls, not the relayer)
        let prior_tenure_thread = self.miner_thread.take();
        self.miner_thread_burn_view = None;

        let vrf_key = self
            .globals
            .get_leader_key_registration_state()
            .get_active()
            .ok_or_else(|| {
                warn!("Trying to start new tenure, but no VRF key active");
                NakamotoNodeError::NoVRFKeyActive
            })?;
        let new_miner_state = self.create_block_miner(
            vrf_key,
            block_election_snapshot,
            burn_tip.clone(),
            parent_tenure_start,
            reason,
            burn_tip_at_start,
        )?;
        let miner_abort_flag = new_miner_state.get_abort_flag();

        debug!("Relayer: starting new tenure thread");

        let rand_id = thread_rng().gen::<u32>();

        let new_miner_handle = std::thread::Builder::new()
            .name(format!("miner.{parent_tenure_start}.{rand_id}",))
            .stack_size(BLOCK_PROCESSOR_STACK_SIZE)
            .spawn(move || {
                debug!(
                    "New block miner thread ID is {:?}",
                    std::thread::current().id()
                );
                Self::fault_injection_stall_miner_thread_startup();
                if let Err(e) = new_miner_state.run_miner(prior_tenure_thread) {
                    info!("Miner thread failed: {e:?}");
                    Err(e)
                } else {
                    Ok(())
                }
            })
            .map_err(|e| {
                error!("Relayer: Failed to start tenure thread: {e:?}");
                NakamotoNodeError::SpawnError(e)
            })?;
        debug!(
            "Relayer: started tenure thread ID {:?}",
            new_miner_handle.thread().id()
        );
        self.miner_thread
            .replace(MinerStopHandle::new(new_miner_handle, miner_abort_flag));
        self.miner_thread_burn_view.replace(burn_tip);
        Ok(())
    }

    fn stop_tenure(&mut self) -> Result<(), NakamotoNodeError> {
        // when stopping a tenure, block the mining thread if its currently running, then join it.
        // do this in a new thread will (so that the new thread stalls, not the relayer)
        let Some(prior_tenure_thread) = self.miner_thread.take() else {
            debug!("Relayer: no tenure thread to stop");
            return Ok(());
        };
        self.miner_thread_burn_view = None;

        let id = prior_tenure_thread.inner_thread().id();
        let abort_flag = prior_tenure_thread.abort_flag.clone();
        let globals = self.globals.clone();

        let stop_handle = std::thread::Builder::new()
            .name(format!(
                "tenure-stop({:?})-{}",
                id, self.local_peer.data_url
            ))
            .spawn(move || prior_tenure_thread.stop(&globals))
            .map_err(|e| {
                error!("Relayer: Failed to spawn a stop-tenure thread: {e:?}");
                NakamotoNodeError::SpawnError(e)
            })?;

        self.miner_thread
            .replace(MinerStopHandle::new(stop_handle, abort_flag));
        debug!("Relayer: stopped tenure thread ID {id:?}");
        Ok(())
    }

    /// Get the public key hash for the mining key.
    fn get_mining_key_pkh(&self) -> Option<Hash160> {
        let Some(ref mining_key) = self.config.miner.mining_key else {
            return None;
        };
        Some(Hash160::from_node_public_key(
            &StacksPublicKey::from_private(mining_key),
        ))
    }

    /// Helper method to get the last snapshot with a winner
    fn get_last_winning_snapshot(
        sortdb: &SortitionDB,
        sort_tip: &BlockSnapshot,
    ) -> Result<BlockSnapshot, NakamotoNodeError> {
        let ih = sortdb.index_handle(&sort_tip.sortition_id);
        Ok(ih.get_last_snapshot_with_sortition(sort_tip.block_height)?)
    }

    /// Returns true if the sortition `sn` commits to the tenure start block of the ongoing Stacks tenure `stacks_tip_sn`.
    /// Returns false otherwise.
    fn sortition_commits_to_stacks_tip_tenure(
        chain_state: &mut StacksChainState,
        stacks_tip_id: &StacksBlockId,
        stacks_tip_sn: &BlockSnapshot,
        sn: &BlockSnapshot,
    ) -> Result<bool, NakamotoNodeError> {
        if !sn.sortition {
            // definitely not a valid sortition
            debug!("Relayer: Sortition {} is empty", &sn.consensus_hash);
            return Ok(false);
        }
        // The sortition must commit to the tenure start block of the ongoing Stacks tenure.
        let mut ic = chain_state.index_conn();
        let parent_tenure_id = StacksBlockId(sn.winning_stacks_block_hash.clone().0);
        let highest_tenure_start_block_header = NakamotoChainState::get_tenure_start_block_header(
            &mut ic,
            stacks_tip_id,
            &stacks_tip_sn.consensus_hash,
        )?
        .ok_or_else(|| {
            error!(
                "Relayer: Failed to find tenure-start block header for stacks tip {stacks_tip_id}"
            );
            NakamotoNodeError::ParentNotFound
        })?;

        let highest_tenure_start_block_id = highest_tenure_start_block_header.index_block_hash();
        if highest_tenure_start_block_id != parent_tenure_id {
            debug!("Relayer: Sortition {} is at the tip, but does not commit to {parent_tenure_id} so cannot be valid", &sn.consensus_hash;
                "highest_tenure_start_block_header_block_id" => %highest_tenure_start_block_id);
            return Ok(false);
        }

        Ok(true)
    }

    /// Determine the highest sortition higher than `elected_tenure_id`, but no higher than
    /// `sort_tip` whose winning commit's parent tenure ID matches the `stacks_tip`,
    /// and whose consensus hash matches the `stacks_tip`'s tenure ID.
    ///
    /// Returns Ok(true) if such a sortition is found, and is higher than that of
    /// `elected_tenure_id`.
    /// Returns Ok(false) if no such sortition is found.
    /// Returns Err(..) on DB errors.
    fn has_higher_sortition_commits_to_stacks_tip_tenure(
        sortdb: &SortitionDB,
        chain_state: &mut StacksChainState,
        sortition_tip: &BlockSnapshot,
        elected_tenure: &BlockSnapshot,
    ) -> Result<bool, NakamotoNodeError> {
        let (canonical_stacks_tip_ch, canonical_stacks_tip_bh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let canonical_stacks_tip =
            StacksBlockId::new(&canonical_stacks_tip_ch, &canonical_stacks_tip_bh);

        let Ok(Some(canonical_stacks_tip_sn)) =
            SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &canonical_stacks_tip_ch)
        else {
            return Err(NakamotoNodeError::ParentNotFound);
        };

        sortdb
            .find_from(sortition_tip.clone(), |cursor| {
                debug!(
                    "Relayer: check sortition {} to see if it is valid",
                    &cursor.consensus_hash
                );
                // have we reached the last tenure we're looking at?
                if cursor.block_height <= elected_tenure.block_height {
                    return Ok(FindIter::Halt);
                }

                if Self::sortition_commits_to_stacks_tip_tenure(
                    chain_state,
                    &canonical_stacks_tip,
                    &canonical_stacks_tip_sn,
                    &cursor,
                )? {
                    return Ok(FindIter::Found(()));
                }

                // nope. continue the search
                return Ok(FindIter::Continue);
            })
            .map(|found| found.is_some())
    }

    /// Attempt to continue a miner's tenure into the next burn block.
    /// This is allowed if the miner won the last good sortition -- that is, the sortition which
    /// elected the local view of the canonical Stacks fork's ongoing tenure.
    /// Or if the miner won the last valid sortition prior to the current and the current miner
    /// has failed to produce a block before the required timeout.
    ///
    /// This function assumes that the caller has checked that the sortition referred to by
    /// `new_burn_view` does not have a sortition winner or that the winner has not produced a
    /// valid block yet.
    fn continue_tenure(&mut self, new_burn_view: ConsensusHash) -> Result<(), NakamotoNodeError> {
        if let Err(e) = self.stop_tenure() {
            error!("Relayer: Failed to stop tenure: {e:?}");
            return Ok(());
        }
        debug!("Relayer: successfully stopped tenure; will try to continue.");

        // try to extend, but only if we aren't already running a thread for the current or newer
        // burnchain view
        let Ok(sn) =
            SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn()).inspect_err(|e| {
                error!("Relayer: failed to read canonical burnchain sortition: {e:?}");
            })
        else {
            return Ok(());
        };

        if let Some(miner_thread_burn_view) = self.miner_thread_burn_view.as_ref() {
            // a miner thread is already running.  If its burn view is the same as the canonical
            // tip, then do nothing
            if sn.consensus_hash == miner_thread_burn_view.consensus_hash {
                info!("Relayer: will not tenure extend -- the current miner thread's burn view matches the sortition tip"; "sortition tip" => %sn.consensus_hash);
                return Ok(());
            }
        }

        // Get the necessary snapshots and state
        let burn_tip =
            SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), &new_burn_view)?
                .ok_or_else(|| {
                    error!("Relayer: failed to get block snapshot for new burn view");
                    NakamotoNodeError::SnapshotNotFoundForChainTip
                })?;
        let (canonical_stacks_tip_ch, canonical_stacks_tip_bh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortdb.conn()).unwrap();
        let canonical_stacks_tip =
            StacksBlockId::new(&canonical_stacks_tip_ch, &canonical_stacks_tip_bh);
        let canonical_stacks_snapshot = SortitionDB::get_block_snapshot_consensus(
            self.sortdb.conn(),
            &canonical_stacks_tip_ch,
        )?
        .ok_or_else(|| {
            error!("Relayer: failed to get block snapshot for canonical tip");
            NakamotoNodeError::SnapshotNotFoundForChainTip
        })?;
        let reason = MinerReason::Extended {
            burn_view_consensus_hash: new_burn_view.clone(),
        };

        if let Err(e) = self.start_new_tenure(
            canonical_stacks_tip.clone(),
            canonical_stacks_snapshot.clone(),
            burn_tip.clone(),
            reason.clone(),
            &new_burn_view,
        ) {
            error!("Relayer: Failed to start new tenure: {e:?}");
        } else {
            debug!("Relayer: successfully started new tenure.";
                   "parent_tenure_start" => %canonical_stacks_tip,
                   "burn_tip" => %burn_tip.consensus_hash,
                   "burn_view_snapshot" => %burn_tip.consensus_hash,
                   "block_election_snapshot" => %canonical_stacks_snapshot.consensus_hash,
                   "reason" => %reason);
        }
        Ok(())
    }

    fn handle_sortition(
        &mut self,
        consensus_hash: ConsensusHash,
        burn_hash: BurnchainHeaderHash,
        committed_index_hash: StacksBlockId,
    ) -> bool {
        let miner_instruction =
            match self.process_sortition(consensus_hash, burn_hash, committed_index_hash) {
                Ok(Some(miner_instruction)) => miner_instruction,
                Ok(None) => {
                    return true;
                }
                Err(e) => {
                    warn!("Relayer: process_sortition returned {e:?}");
                    return false;
                }
            };

        match miner_instruction {
            MinerDirective::BeginTenure {
                parent_tenure_start,
                burnchain_tip,
                election_block,
                late,
            } => match self.start_new_tenure(
                parent_tenure_start,
                election_block.clone(),
                election_block.clone(),
                MinerReason::BlockFound { late },
                &burnchain_tip.consensus_hash,
            ) {
                Ok(()) => {
                    debug!("Relayer: successfully started new tenure.";
                           "parent_tenure_start" => %parent_tenure_start,
                           "burn_tip" => %burnchain_tip.consensus_hash,
                           "burn_view_snapshot" => %burnchain_tip.consensus_hash,
                           "block_election_snapshot" => %burnchain_tip.consensus_hash,
                           "reason" => %MinerReason::BlockFound { late });
                }
                Err(e) => {
                    error!("Relayer: Failed to start new tenure: {e:?}");
                }
            },
            MinerDirective::ContinueTenure { new_burn_view } => {
                match self.continue_tenure(new_burn_view) {
                    Ok(()) => {
                        debug!("Relayer: successfully handled continue tenure.");
                    }
                    Err(e) => {
                        error!("Relayer: Failed to continue tenure: {e:?}");
                        return false;
                    }
                }
            }
            MinerDirective::StopTenure => match self.stop_tenure() {
                Ok(()) => {
                    debug!("Relayer: successfully stopped tenure.");
                }
                Err(e) => {
                    error!("Relayer: Failed to stop tenure: {e:?}");
                }
            },
        }

        self.globals.counters.bump_naka_miner_directives();
        true
    }

    #[cfg(test)]
    fn fault_injection_skip_block_commit(&self) -> bool {
        self.globals.counters.naka_skip_commit_op.get()
    }

    #[cfg(not(test))]
    fn fault_injection_skip_block_commit(&self) -> bool {
        false
    }

    /// Generate and submit the next block-commit, and record it locally
    fn issue_block_commit(&mut self) -> Result<(), NakamotoNodeError> {
        if self.fault_injection_skip_block_commit() {
            warn!("Relayer: not submitting block-commit to bitcoin network due to test directive.");
            return Ok(());
        }
        let (tip_block_ch, tip_block_bh) = SortitionDB::get_canonical_stacks_chain_tip_hash(
            self.sortdb.conn(),
        )
        .unwrap_or_else(|e| {
            panic!("Failed to load canonical stacks tip: {e:?}");
        });
        let mut last_committed = self.make_block_commit(&tip_block_ch, &tip_block_bh)?;

        // last chance -- is this tenure still the canonical tip?
        let (cur_stacks_tip_ch, _) = SortitionDB::get_canonical_stacks_chain_tip_hash(
            self.sortdb.conn(),
        )
        .unwrap_or_else(|e| {
            panic!("Failed to load canonical stacks tip: {e:?}");
        });
        if last_committed.get_tenure_id() != &cur_stacks_tip_ch {
            info!(
                "Stacks tenure changed prior to commit";
                "current_stacks_tip_ch" => %cur_stacks_tip_ch,
                "committed_tenure_ch" => %last_committed.get_tenure_id(),
                "issue_commit_tip_ch" => %tip_block_ch,
                "issue_commit_tip_bh" => %tip_block_bh
            );
            return Err(NakamotoNodeError::StacksTipChanged);
        }

        let Some(tip_height) = NakamotoChainState::get_block_header(
            self.chainstate.db(),
            &StacksBlockId::new(&tip_block_ch, &tip_block_bh),
        )
        .map_err(|e| {
            warn!("Relayer: failed to load tip {tip_block_ch}/{tip_block_bh}: {e:?}");
            NakamotoNodeError::ParentNotFound
        })?
        .map(|header| header.stacks_block_height) else {
            warn!(
                "Relayer: failed to load height for tip {tip_block_ch}/{tip_block_bh} (got None)"
            );
            return Err(NakamotoNodeError::ParentNotFound);
        };

        // sign and broadcast
        let mut op_signer = self.keychain.generate_op_signer();
        let res = self.bitcoin_controller.submit_operation(
            *last_committed.get_epoch_id(),
            BlockstackOperationType::LeaderBlockCommit(last_committed.get_block_commit().clone()),
            &mut op_signer,
            1,
        );
        let txid = match res {
            Ok(txid) => txid,
            Err(e) => {
                if self.config.node.mock_mining {
                    debug!("Relayer: Mock-mining enabled; not sending Bitcoin transaction");
                    return Ok(());
                }
                warn!("Failed to submit block-commit bitcoin transaction: {e}");
                return Err(NakamotoNodeError::BurnchainSubmissionFailed(e));
            }
        };

        info!(
            "Relayer: Submitted block-commit";
            "tip_consensus_hash" => %tip_block_ch,
            "tip_block_hash" => %tip_block_bh,
            "tip_height" => %tip_height,
            "tip_block_id" => %StacksBlockId::new(&tip_block_ch, &tip_block_bh),
            "txid" => %txid,
        );

        // update local state
        last_committed.set_txid(&txid);
        self.globals
            .counters
            .bump_naka_submitted_commits(last_committed.burn_tip.block_height, tip_height);
        self.last_committed = Some(last_committed);

        Ok(())
    }

    /// Determine what the relayer should do to advance the chain.
    /// * If this isn't a miner, then it's always nothing.
    /// * Otherwise, if we haven't done so already, go register a VRF public key
    /// * If the stacks chain tip or burnchain tip has changed, then issue a block-commit
    /// * If the last burn view we started a miner for is not the canonical burn view, then
    /// try and start a new tenure (or continue an existing one).
    fn initiative(&mut self) -> Result<Option<RelayerDirective>, NakamotoNodeError> {
        if !self.is_miner {
            return Ok(None);
        }

        match self.globals.get_leader_key_registration_state() {
            // do we need a VRF key registration?
            LeaderKeyRegistrationState::Inactive => {
                let sort_tip = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())?;
                return Ok(Some(RelayerDirective::RegisterKey(sort_tip)));
            }
            // are we still waiting on a pending registration?
            LeaderKeyRegistrationState::Pending(..) => {
                return Ok(None);
            }
            LeaderKeyRegistrationState::Active(_) => {}
        };

        // load up canonical sortition and stacks tips
        let sort_tip = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())?;

        // NOTE: this may be an epoch2x tip
        let (stacks_tip_ch, stacks_tip_bh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortdb.conn())?;
        let stacks_tip = StacksBlockId::new(&stacks_tip_ch, &stacks_tip_bh);

        // check stacks and sortition tips to see if any chainstate change has happened.
        // did our view of the sortition history change?
        // if so, then let's try and confirm the highest tenure so far.
        let burnchain_changed = self
            .last_committed
            .as_ref()
            .map(|cmt| cmt.get_burn_tip().consensus_hash != sort_tip.consensus_hash)
            .unwrap_or(true);

        let highest_tenure_changed = self
            .last_committed
            .as_ref()
            .map(|cmt| cmt.get_tenure_id() != &stacks_tip_ch)
            .unwrap_or(true);

        debug!("Relayer: initiative to commit";
               "sortititon tip" => %sort_tip.consensus_hash,
               "stacks tip" => %stacks_tip,
               "stacks_tip_ch" => %stacks_tip_ch,
               "stacks_tip_bh" => %stacks_tip_bh,
               "last-commit burn view" => %self.last_committed.as_ref().map(|cmt| cmt.get_burn_tip().consensus_hash.to_string()).unwrap_or("(not set)".to_string()),
               "last-commit ongoing tenure" => %self.last_committed.as_ref().map(|cmt| cmt.get_tenure_id().to_string()).unwrap_or("(not set)".to_string()),
               "burnchain view changed?" => %burnchain_changed,
               "highest tenure changed?" => %highest_tenure_changed);

        if !burnchain_changed && !highest_tenure_changed {
            // nothing to do
            return Ok(None);
        }

        if highest_tenure_changed {
            // highest-tenure view changed, so we need to send (or RBF) a commit
            return Ok(Some(RelayerDirective::IssueBlockCommit(
                stacks_tip_ch,
                stacks_tip_bh,
            )));
        }

        debug!("Relayer: burnchain view changed, but highest tenure did not");
        // First, check if the changed burnchain view includes any
        // sortitions. If it doesn't submit a block commit immediately.
        //
        // If it does, then wait a bit for the first block in the new
        // tenure to arrive. This is to avoid submitting a block
        // commit that will be immediately RBFed when the first
        // block arrives.
        if let Some(last_committed) = self.last_committed.as_ref() {
            // check if all the sortitions after `last_tenure` are empty sortitions. if they are,
            //  we don't need to wait at all to submit a commit
            let last_tenure_tip_height = SortitionDB::get_consensus_hash_height(
                &self.sortdb,
                last_committed.get_tenure_id(),
            )?
            .ok_or_else(|| NakamotoNodeError::ParentNotFound)?;
            let no_sortitions_after_last_tenure = self
                .sortdb
                .find_in_canonical::<_, _, NakamotoNodeError>(|cursor| {
                    if cursor.block_height <= last_tenure_tip_height {
                        return Ok(FindIter::Halt);
                    }
                    if cursor.sortition {
                        return Ok(FindIter::Found(()));
                    }
                    Ok(FindIter::Continue)
                })?
                .is_none();
            if no_sortitions_after_last_tenure {
                return Ok(Some(RelayerDirective::IssueBlockCommit(
                    stacks_tip_ch,
                    stacks_tip_bh,
                )));
            }
        }

        if self.new_tenure_timeout.is_ready(
            &sort_tip.consensus_hash,
            &self.config.miner.block_commit_delay,
        ) {
            return Ok(Some(RelayerDirective::IssueBlockCommit(
                stacks_tip_ch,
                stacks_tip_bh,
            )));
        } else {
            if let Some(deadline) = self
                .new_tenure_timeout
                .deadline(&self.config.miner.block_commit_delay)
            {
                self.next_initiative = std::cmp::min(self.next_initiative, deadline);
            }

            return Ok(None);
        }
    }

    /// Try to start up a tenure-extend if the tenure_extend_time has expired.
    ///
    /// Will check if the tenure-extend time was set and has expired. If so, will
    /// check if the current miner thread needs to issue a BlockFound or if it can
    /// immediately tenure-extend.
    ///
    /// Note: tenure_extend_time is only set to Some(_) if during sortition processing, the sortition
    /// winner commit is corrupted or the winning miner has yet to produce a block.
    fn check_tenure_timers(&mut self) {
        // Should begin a tenure-extend?
        let Some(tenure_extend_time) = self.tenure_extend_time.clone() else {
            // No tenure extend time set, so nothing to do.
            return;
        };
        if !tenure_extend_time.should_extend() {
            test_debug!(
                "Relayer: will not try to tenure-extend yet ({} <= {})",
                tenure_extend_time.elapsed().as_secs(),
                tenure_extend_time.timeout().as_secs()
            );
            return;
        }

        let Some(mining_pkh) = self.get_mining_key_pkh() else {
            // This shouldn't really ever hit, but just in case.
            warn!("Will not tenure extend -- no mining key");
            // If we don't have a mining key set, don't bother checking again.
            self.tenure_extend_time = None;
            return;
        };
        // reset timer so we can try again if for some reason a miner was already running (e.g. a
        // blockfound from earlier).
        self.tenure_extend_time
            .as_mut()
            .map(|t| t.refresh(self.config.miner.tenure_extend_poll_timeout));
        // try to extend, but only if we aren't already running a thread for the current or newer
        // burnchain view
        let Ok(burn_tip) = SortitionDB::get_canonical_burn_chain_tip(self.sortdb.conn())
            .inspect_err(|e| {
                error!("Failed to read canonical burnchain sortition: {e:?}");
            })
        else {
            return;
        };

        if let Some(miner_thread_burn_view) = self.miner_thread_burn_view.as_ref() {
            // a miner thread is already running.  If its burn view is the same as the canonical
            // tip, then do nothing for now
            if burn_tip.consensus_hash == miner_thread_burn_view.consensus_hash {
                info!("Will not try to start a tenure extend -- the current miner thread's burn view matches the sortition tip"; "sortition tip" => %burn_tip.consensus_hash);
                // Do not reset the timer, as we may be able to extend later.
                return;
            }
        }

        let (canonical_stacks_tip_ch, canonical_stacks_tip_bh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortdb.conn())
                .expect("FATAL: failed to query sortition DB for stacks tip");
        let canonical_stacks_tip =
            StacksBlockId::new(&canonical_stacks_tip_ch, &canonical_stacks_tip_bh);
        let canonical_stacks_snapshot =
            SortitionDB::get_block_snapshot_consensus(self.sortdb.conn(), &canonical_stacks_tip_ch)
                .expect("FATAL: failed to query sortiiton DB for epoch")
                .expect("FATAL: no sortition for canonical stacks tip");

        match tenure_extend_time.reason() {
            TenureExtendReason::BadSortitionWinner | TenureExtendReason::EmptySortition => {
                // Before we try to extend, check if we need to issue a BlockFound
                let Ok(last_winning_snapshot) =
                    Self::get_last_winning_snapshot(&self.sortdb, &burn_tip).inspect_err(|e| {
                        warn!("Failed to load last winning snapshot: {e:?}");
                    })
                else {
                    // this should be unreachable, but don't tempt fate.
                    info!("No prior snapshots have a winning sortition. Will not try to mine.");
                    self.tenure_extend_time = None;
                    return;
                };
                let won_last_winning_snapshot =
                    last_winning_snapshot.miner_pk_hash == Some(mining_pkh);
                if won_last_winning_snapshot
                    && Self::need_block_found(&canonical_stacks_snapshot, &last_winning_snapshot)
                {
                    info!("Will not tenure extend yet -- need to issue a BlockFound first");
                    // We may manage to extend later, so don't set the timer to None.
                    return;
                }
            }
            TenureExtendReason::UnresponsiveWinner => {}
        }

        let won_ongoing_tenure_sortition =
            canonical_stacks_snapshot.miner_pk_hash == Some(mining_pkh);
        if !won_ongoing_tenure_sortition {
            debug!("Will not tenure extend. Did not win ongoing tenure sortition";
                "burn_chain_sortition_tip_ch" => %burn_tip.consensus_hash,
                "canonical_stacks_tip_ch" => %canonical_stacks_tip_ch,
                "burn_chain_sortition_tip_mining_pk" => ?burn_tip.miner_pk_hash,
                "mining_pk" => %mining_pkh
            );
            self.tenure_extend_time = None;
            return;
        }
        // If we reach this code, we have either won the last winning snapshot and have already issued a block found for it and should extend.
        // OR we did not win the last snapshot, but the person who did has failed to produce a block and we should extend our old tenure.
        if let Err(e) = self.stop_tenure() {
            error!("Relayer: Failed to stop tenure: {e:?}");
            return;
        }
        let reason = MinerReason::Extended {
            burn_view_consensus_hash: burn_tip.consensus_hash.clone(),
        };
        debug!("Relayer: successfully stopped tenure; will try to continue.");
        if let Err(e) = self.start_new_tenure(
            canonical_stacks_tip.clone(),
            canonical_stacks_snapshot.clone(),
            burn_tip.clone(),
            reason.clone(),
            &burn_tip.consensus_hash,
        ) {
            error!("Relayer: Failed to start new tenure: {e:?}");
        } else {
            debug!("Relayer: successfully started new tenure.";
                   "parent_tenure_start" => %canonical_stacks_tip,
                   "burn_tip" => %burn_tip.consensus_hash,
                   "burn_view_snapshot" => %burn_tip.consensus_hash,
                   "block_election_snapshot" => %canonical_stacks_snapshot.consensus_hash,
                   "reason" => %reason);
            self.tenure_extend_time = None;
        }
    }

    /// Main loop of the relayer.
    /// Runs in a separate thread.
    /// Continuously receives from `relay_rcv`.
    /// Wakes up once per second to see if we need to continue mining an ongoing tenure.
    pub fn main(mut self, relay_rcv: Receiver<RelayerDirective>) {
        debug!("relayer thread ID is {:?}", std::thread::current().id());

        self.next_initiative =
            Instant::now() + Duration::from_millis(self.config.node.next_initiative_delay);

        // how often we perform a loop pass below
        let poll_frequency_ms = 1_000;

        while self.globals.keep_running() {
            self.check_tenure_timers();
            let raised_initiative = self.globals.take_initiative();
            let timed_out = Instant::now() >= self.next_initiative;
            let initiative_directive = if raised_initiative.is_some() || timed_out {
                self.next_initiative =
                    Instant::now() + Duration::from_millis(self.config.node.next_initiative_delay);
                self.initiative()
                    .inspect_err(|e| {
                        error!("Error while getting directive from initiative()"; "err" => ?e);
                    })
                    .ok()
                    .flatten()
            } else {
                None
            };

            let directive_opt = initiative_directive.or_else(|| {
                // do a time-bound recv on the relayer channel so that we can hit the `initiative()` invocation
                //  and keep_running() checks on each loop iteration
                match relay_rcv.recv_timeout(Duration::from_millis(poll_frequency_ms)) {
                    Ok(directive) => {
                        // only do this once, so we can call .initiative() again
                        Some(directive)
                    }
                    Err(RecvTimeoutError::Timeout) => None,
                    Err(RecvTimeoutError::Disconnected) => {
                        warn!("Relayer receive channel disconnected. Exiting relayer thread");
                        Some(RelayerDirective::Exit)
                    }
                }
            });

            if let Some(directive) = directive_opt {
                debug!("Relayer: main loop directive";
                       "directive" => %directive,
                       "raised_initiative" => ?raised_initiative,
                       "timed_out" => %timed_out);

                if !self.handle_directive(directive) {
                    break;
                }
            }
        }

        // kill miner if it's running
        signal_mining_blocked(self.globals.get_miner_status());

        // set termination flag so other threads die
        self.globals.signal_stop();

        debug!("Relayer exit!");
    }

    /// Try loading up a saved VRF key
    pub(crate) fn load_saved_vrf_key(path: &str, pubkey_hash: &Hash160) -> Option<RegisteredKey> {
        let mut f = match fs::File::open(path) {
            Ok(f) => f,
            Err(e) => {
                warn!("Could not open {path}: {e:?}");
                return None;
            }
        };
        let mut registered_key_bytes = vec![];
        if let Err(e) = f.read_to_end(&mut registered_key_bytes) {
            warn!("Failed to read registered key bytes from {path}: {e:?}");
            return None;
        }

        let Ok(registered_key) = serde_json::from_slice::<RegisteredKey>(&registered_key_bytes)
        else {
            warn!("Did not load registered key from {path}: could not decode JSON");
            return None;
        };

        // Check that the loaded key's memo matches the current miner's key
        if registered_key.memo != pubkey_hash.as_ref() {
            warn!("Loaded VRF key does not match mining key");
            return None;
        }

        info!("Loaded registered key from {path}");
        Some(registered_key)
    }

    /// Top-level dispatcher
    pub fn handle_directive(&mut self, directive: RelayerDirective) -> bool {
        debug!("Relayer: handling directive"; "directive" => %directive);
        let continue_running = match directive {
            RelayerDirective::HandleNetResult(net_result) => {
                self.process_network_result(net_result);
                true
            }
            // RegisterKey directives mean that the relayer should try to register a new VRF key.
            // These are triggered by the relayer waking up without an active VRF key.
            RelayerDirective::RegisterKey(last_burn_block) => {
                if !self.is_miner {
                    return true;
                }
                if self.globals.in_initial_block_download() {
                    info!("In initial block download, will not submit VRF registration");
                    return true;
                }
                let mut saved_key_opt = None;
                if let Some(path) = self.config.miner.activated_vrf_key_path.as_ref() {
                    saved_key_opt =
                        Self::load_saved_vrf_key(path, &self.keychain.get_nakamoto_pkh());
                }
                if let Some(saved_key) = saved_key_opt {
                    debug!("Relayer: resuming VRF key");
                    self.globals.resume_leader_key(saved_key);
                } else {
                    self.rotate_vrf_and_register(&last_burn_block);
                    debug!("Relayer: directive Registered VRF key");
                }
                self.globals.counters.bump_blocks_processed();
                true
            }
            // ProcessedBurnBlock directives correspond to a new sortition perhaps occurring.
            //  relayer should invoke `handle_sortition` to determine if they won the sortition,
            //  and to start their miner, or stop their miner if an active tenure is now ending
            RelayerDirective::ProcessedBurnBlock(consensus_hash, burn_hash, block_header_hash) => {
                if !self.is_miner {
                    return true;
                }
                if self.globals.in_initial_block_download() {
                    debug!("In initial block download, will not check sortition for miner");
                    return true;
                }
                self.handle_sortition(
                    consensus_hash,
                    burn_hash,
                    StacksBlockId(block_header_hash.0),
                )
            }
            // These are triggered by the relayer waking up, seeing a new consensus hash *or* a new first tenure block
            RelayerDirective::IssueBlockCommit(..) => {
                if !self.is_miner {
                    return true;
                }
                if self.globals.in_initial_block_download() {
                    debug!("In initial block download, will not issue block commit");
                    return true;
                }
                if let Err(e) = self.issue_block_commit() {
                    warn!("Relayer failed to issue block commit"; "err" => ?e);
                }
                true
            }
            RelayerDirective::Exit => false,
        };
        debug!("Relayer: handled directive"; "continue_running" => continue_running);
        continue_running
    }
}

#[cfg(test)]
pub mod test {
    use std::fs::File;
    use std::io::Write;
    use std::path::Path;
    use std::time::Duration;
    use std::u64;

    use rand::{thread_rng, Rng};
    use stacks::burnchains::Txid;
    use stacks::chainstate::burn::{BlockSnapshot, ConsensusHash, OpsHash, SortitionHash};
    use stacks::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, SortitionId, TrieHash};
    use stacks::util::hash::Hash160;
    use stacks::util::secp256k1::Secp256k1PublicKey;
    use stacks::util::vrf::VRFPublicKey;

    use super::{BurnBlockCommitTimer, RelayerThread};
    use crate::nakamoto_node::save_activated_vrf_key;
    use crate::run_loop::RegisteredKey;
    use crate::Keychain;

    #[test]
    fn load_nonexistent_vrf_key() {
        let keychain = Keychain::default(vec![0u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);

        let path = "/tmp/does_not_exist.json";
        _ = std::fs::remove_file(path);

        let res = RelayerThread::load_saved_vrf_key(path, &pubkey_hash);
        assert!(res.is_none());
    }

    #[test]
    fn load_empty_vrf_key() {
        let keychain = Keychain::default(vec![0u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);

        let path = "/tmp/empty.json";
        File::create(path).expect("Failed to create test file");
        assert!(Path::new(path).exists());

        let res = RelayerThread::load_saved_vrf_key(path, &pubkey_hash);
        assert!(res.is_none());

        std::fs::remove_file(path).expect("Failed to delete test file");
    }

    #[test]
    fn load_bad_vrf_key() {
        let keychain = Keychain::default(vec![0u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);

        let path = "/tmp/invalid_saved_key.json";
        let json_content = r#"{ "hello": "world" }"#;

        // Write the JSON content to the file
        let mut file = File::create(path).expect("Failed to create test file");
        file.write_all(json_content.as_bytes())
            .expect("Failed to write to test file");
        assert!(Path::new(path).exists());

        let res = RelayerThread::load_saved_vrf_key(path, &pubkey_hash);
        assert!(res.is_none());

        std::fs::remove_file(path).expect("Failed to delete test file");
    }

    #[test]
    fn save_load_vrf_key() {
        let keychain = Keychain::default(vec![0u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);
        let key = RegisteredKey {
            target_block_height: 101,
            block_height: 102,
            op_vtxindex: 1,
            vrf_public_key: VRFPublicKey::from_hex(
                "1da75863a7e1ef86f0f550d92b1f77dc60af23694b884b2816b703137ff94e71",
            )
            .unwrap(),
            memo: pubkey_hash.as_ref().to_vec(),
        };
        let path = "/tmp/vrf_key.json";
        save_activated_vrf_key(path, &key);

        let res = RelayerThread::load_saved_vrf_key(path, &pubkey_hash);
        assert!(res.is_some());

        std::fs::remove_file(path).expect("Failed to delete test file");
    }

    #[test]
    fn invalid_saved_memo() {
        let keychain = Keychain::default(vec![0u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);
        let key = RegisteredKey {
            target_block_height: 101,
            block_height: 102,
            op_vtxindex: 1,
            vrf_public_key: VRFPublicKey::from_hex(
                "1da75863a7e1ef86f0f550d92b1f77dc60af23694b884b2816b703137ff94e71",
            )
            .unwrap(),
            memo: pubkey_hash.as_ref().to_vec(),
        };
        let path = "/tmp/vrf_key.json";
        save_activated_vrf_key(path, &key);

        let keychain = Keychain::default(vec![1u8; 32]);
        let pk = Secp256k1PublicKey::from_private(keychain.get_nakamoto_sk());
        let pubkey_hash = Hash160::from_node_public_key(&pk);

        let res = RelayerThread::load_saved_vrf_key(path, &pubkey_hash);
        assert!(res.is_none());

        std::fs::remove_file(path).expect("Failed to delete test file");
    }

    #[test]
    fn check_need_block_found() {
        let consensus_hash_byte = thread_rng().gen();
        let canonical_stacks_snapshot = BlockSnapshot {
            block_height: thread_rng().gen::<u64>().wrapping_add(1), // Add one to ensure we can always decrease by 1 without underflowing.
            burn_header_timestamp: thread_rng().gen(),
            burn_header_hash: BurnchainHeaderHash([thread_rng().gen(); 32]),
            consensus_hash: ConsensusHash([consensus_hash_byte; 20]),
            parent_burn_header_hash: BurnchainHeaderHash([thread_rng().gen(); 32]),
            ops_hash: OpsHash([thread_rng().gen(); 32]),
            total_burn: thread_rng().gen(),
            sortition: true,
            sortition_hash: SortitionHash([thread_rng().gen(); 32]),
            winning_block_txid: Txid([thread_rng().gen(); 32]),
            winning_stacks_block_hash: BlockHeaderHash([thread_rng().gen(); 32]),
            index_root: TrieHash([thread_rng().gen(); 32]),
            num_sortitions: thread_rng().gen(),
            stacks_block_accepted: true,
            stacks_block_height: thread_rng().gen(),
            arrival_index: thread_rng().gen(),
            canonical_stacks_tip_consensus_hash: ConsensusHash([thread_rng().gen(); 20]),
            canonical_stacks_tip_hash: BlockHeaderHash([thread_rng().gen(); 32]),
            canonical_stacks_tip_height: thread_rng().gen(),
            sortition_id: SortitionId([thread_rng().gen(); 32]),
            parent_sortition_id: SortitionId([thread_rng().gen(); 32]),
            pox_valid: true,
            accumulated_coinbase_ustx: thread_rng().gen::<u64>() as u128,
            miner_pk_hash: Some(Hash160([thread_rng().gen(); 20])),
        };

        // The consensus_hashes are the same, and the block heights are the same. Therefore, don't need a block found.
        let last_winning_block_snapshot = canonical_stacks_snapshot.clone();
        assert!(!RelayerThread::need_block_found(
            &canonical_stacks_snapshot,
            &last_winning_block_snapshot
        ));

        // The block height of the canonical tip is higher than the last winning snapshot. We already issued a block found.
        let mut canonical_stacks_snapshot_is_higher_than_last_winning_snapshot =
            last_winning_block_snapshot.clone();
        canonical_stacks_snapshot_is_higher_than_last_winning_snapshot.block_height =
            canonical_stacks_snapshot.block_height.saturating_sub(1);
        assert!(!RelayerThread::need_block_found(
            &canonical_stacks_snapshot,
            &canonical_stacks_snapshot_is_higher_than_last_winning_snapshot
        ));

        // The block height is the same, but we have different consensus hashes. We need to issue a block found.
        let mut tip_consensus_hash_mismatch = last_winning_block_snapshot.clone();
        tip_consensus_hash_mismatch.consensus_hash =
            ConsensusHash([consensus_hash_byte.wrapping_add(1); 20]);
        assert!(RelayerThread::need_block_found(
            &canonical_stacks_snapshot,
            &tip_consensus_hash_mismatch
        ));

        // The block height is the same, but we have different consensus hashes. We need to issue a block found.
        let mut tip_consensus_hash_mismatch = last_winning_block_snapshot.clone();
        tip_consensus_hash_mismatch.consensus_hash =
            ConsensusHash([consensus_hash_byte.wrapping_add(1); 20]);
        assert!(RelayerThread::need_block_found(
            &canonical_stacks_snapshot,
            &tip_consensus_hash_mismatch
        ));

        // The block height of the canonical tip is lower than the last winning snapshot blockheight. We need to issue a block found.
        let mut canonical_stacks_snapshot_is_lower_than_last_winning_snapshot =
            last_winning_block_snapshot.clone();
        canonical_stacks_snapshot_is_lower_than_last_winning_snapshot.block_height =
            canonical_stacks_snapshot.block_height.saturating_add(1);
        assert!(RelayerThread::need_block_found(
            &canonical_stacks_snapshot,
            &canonical_stacks_snapshot_is_lower_than_last_winning_snapshot
        ));
    }

    #[test]
    fn burn_block_commit_timer_units() {
        let mut burn_block_timer = BurnBlockCommitTimer::NotSet;
        assert_eq!(burn_block_timer.elapsed_secs(), 0);

        let ch_0 = ConsensusHash([0; 20]);
        let ch_1 = ConsensusHash([1; 20]);
        let ch_2 = ConsensusHash([2; 20]);

        assert!(!burn_block_timer.is_ready(&ch_0, &Duration::from_secs(1)));
        let BurnBlockCommitTimer::Set { burn_tip, .. } = &burn_block_timer else {
            panic!("The burn block timer should be set");
        };
        assert_eq!(burn_tip, &ch_0);

        std::thread::sleep(Duration::from_secs(1));

        assert!(burn_block_timer.is_ready(&ch_0, &Duration::from_secs(0)));
        let BurnBlockCommitTimer::Set { burn_tip, .. } = &burn_block_timer else {
            panic!("The burn block timer should be set");
        };
        assert_eq!(burn_tip, &ch_0);

        assert!(!burn_block_timer.is_ready(&ch_1, &Duration::from_secs(0)));
        let BurnBlockCommitTimer::Set { burn_tip, .. } = &burn_block_timer else {
            panic!("The burn block timer should be set");
        };
        assert_eq!(burn_tip, &ch_1);

        assert!(!burn_block_timer.is_ready(&ch_1, &Duration::from_secs(u64::MAX)));
        let BurnBlockCommitTimer::Set { burn_tip, .. } = &burn_block_timer else {
            panic!("The burn block timer should be set");
        };
        assert_eq!(burn_tip, &ch_1);

        std::thread::sleep(Duration::from_secs(1));
        assert!(!burn_block_timer.is_ready(&ch_2, &Duration::from_secs(0)));
        let BurnBlockCommitTimer::Set { burn_tip, .. } = &burn_block_timer else {
            panic!("The burn block timer should be set");
        };
        assert_eq!(burn_tip, &ch_2);
    }
}
