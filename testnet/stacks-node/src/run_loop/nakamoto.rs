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
use std::sync::atomic::AtomicBool;
use std::sync::mpsc::sync_channel;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::{cmp, thread};

use stacks::burnchains::bitcoin::address::{BitcoinAddress, LegacyBitcoinAddressType};
use stacks::burnchains::{Burnchain, Error as burnchain_error};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::BlockSnapshot;
use stacks::chainstate::coordinator::comm::{CoordinatorChannels, CoordinatorReceivers};
use stacks::chainstate::coordinator::{
    ChainsCoordinator, ChainsCoordinatorConfig, CoordinatorCommunication,
};
use stacks::chainstate::stacks::db::{ChainStateBootData, StacksChainState};
use stacks::chainstate::stacks::miner::{signal_mining_blocked, signal_mining_ready, MinerStatus};
use stacks::core::StacksEpochId;
use stacks::net::atlas::{AtlasConfig, AtlasDB, Attachment};
use stacks_common::types::PublicKey;
use stacks_common::util::hash::Hash160;
use stacks_common::util::{get_epoch_time_secs, sleep_ms};
use stx_genesis::GenesisData;

use crate::burnchains::make_bitcoin_indexer;
use crate::globals::Globals as GenericGlobals;
use crate::monitoring::{start_serving_monitoring_metrics, MonitoringError};
use crate::nakamoto_node::{self, StacksNode, BLOCK_PROCESSOR_STACK_SIZE, RELAYER_MAX_BUFFER};
use crate::neon_node::LeaderKeyRegistrationState;
use crate::node::{
    get_account_balances, get_account_lockups, get_names, get_namespaces,
    use_test_genesis_chainstate,
};
use crate::run_loop::boot_nakamoto::Neon2NakaData;
use crate::run_loop::neon;
use crate::run_loop::neon::Counters;
use crate::syncctl::{PoxSyncWatchdog, PoxSyncWatchdogComms};
use crate::{
    run_loop, BitcoinRegtestController, BurnchainController, Config, EventDispatcher, Keychain,
};

pub const STDERR: i32 = 2;
pub type Globals = GenericGlobals<nakamoto_node::relayer::RelayerDirective>;

/// Coordinating a node running in nakamoto mode. This runloop operates very similarly to the neon runloop.
pub struct RunLoop {
    config: Config,
    globals: Option<Globals>,
    counters: Counters,
    coordinator_channels: Option<(CoordinatorReceivers, CoordinatorChannels)>,
    should_keep_running: Arc<AtomicBool>,
    event_dispatcher: EventDispatcher,
    #[allow(dead_code)]
    pox_watchdog: Option<PoxSyncWatchdog>, // can't be instantiated until .start() is called
    is_miner: Option<bool>,       // not known until .start() is called
    burnchain: Option<Burnchain>, // not known until .start() is called
    pox_watchdog_comms: PoxSyncWatchdogComms,
    /// NOTE: this is duplicated in self.globals, but it needs to be accessible before globals is
    /// instantiated (namely, so the test framework can access it).
    miner_status: Arc<Mutex<MinerStatus>>,
    monitoring_thread: Option<JoinHandle<Result<(), MonitoringError>>>,
}

impl RunLoop {
    /// Sets up a runloop and node, given a config.
    pub fn new(
        config: Config,
        should_keep_running: Option<Arc<AtomicBool>>,
        counters: Option<Counters>,
        monitoring_thread: Option<JoinHandle<Result<(), MonitoringError>>>,
    ) -> Self {
        let channels = CoordinatorCommunication::instantiate();
        let should_keep_running =
            should_keep_running.unwrap_or_else(|| Arc::new(AtomicBool::new(true)));
        let pox_watchdog_comms = PoxSyncWatchdogComms::new(should_keep_running.clone());
        let miner_status = Arc::new(Mutex::new(MinerStatus::make_ready(
            config.burnchain.burn_fee_cap,
        )));

        let mut event_dispatcher = EventDispatcher::new();
        for observer in config.events_observers.iter() {
            event_dispatcher.register_observer(observer, config.get_working_dir());
        }

        Self {
            config,
            globals: None,
            coordinator_channels: Some(channels),
            counters: counters.unwrap_or_default(),
            should_keep_running,
            event_dispatcher,
            pox_watchdog: None,
            is_miner: None,
            burnchain: None,
            pox_watchdog_comms,
            miner_status,
            monitoring_thread,
        }
    }

    pub(crate) fn get_globals(&self) -> Globals {
        self.globals
            .clone()
            .expect("FATAL: globals not instantiated")
    }

    fn set_globals(&mut self, globals: Globals) {
        self.globals = Some(globals);
    }

    pub(crate) fn get_coordinator_channel(&self) -> Option<CoordinatorChannels> {
        self.coordinator_channels.as_ref().map(|x| x.1.clone())
    }

    pub(crate) fn get_counters(&self) -> Counters {
        self.counters.clone()
    }

    pub(crate) fn config(&self) -> &Config {
        &self.config
    }

    pub(crate) fn get_event_dispatcher(&self) -> EventDispatcher {
        self.event_dispatcher.clone()
    }

    pub(crate) fn is_miner(&self) -> bool {
        self.is_miner.unwrap_or(false)
    }

    pub(crate) fn get_termination_switch(&self) -> Arc<AtomicBool> {
        self.should_keep_running.clone()
    }

    pub(crate) fn get_burnchain(&self) -> Burnchain {
        self.burnchain
            .clone()
            .expect("FATAL: tried to get runloop burnchain before calling .start()")
    }

    pub(crate) fn get_miner_status(&self) -> Arc<Mutex<MinerStatus>> {
        self.miner_status.clone()
    }

    /// Seconds to wait before retrying UTXO check during startup
    const UTXO_RETRY_INTERVAL: u64 = 10;
    /// Number of times to retry UTXO check during startup
    const UTXO_RETRY_COUNT: u64 = 6;

    /// Determine if we're the miner.
    /// If there's a network error, then assume that we're not a miner.
    fn check_is_miner(&mut self, burnchain: &mut BitcoinRegtestController) -> bool {
        if self.config.node.miner {
            let keychain = Keychain::default(self.config.node.seed.clone());
            let mut op_signer = keychain.generate_op_signer();
            if let Err(e) = burnchain.create_wallet_if_dne() {
                warn!("Error when creating wallet: {e:?}");
            }
            let mut btc_addrs = vec![(
                StacksEpochId::Epoch2_05,
                // legacy
                BitcoinAddress::from_bytes_legacy(
                    self.config.burnchain.get_bitcoin_network().1,
                    LegacyBitcoinAddressType::PublicKeyHash,
                    &Hash160::from_data(&op_signer.get_public_key().to_bytes()).0,
                )
                .expect("FATAL: failed to construct legacy bitcoin address"),
            )];
            if self.config.miner.segwit {
                btc_addrs.push((
                    StacksEpochId::Epoch21,
                    // segwit p2wpkh
                    BitcoinAddress::from_bytes_segwit_p2wpkh(
                        self.config.burnchain.get_bitcoin_network().1,
                        &Hash160::from_data(&op_signer.get_public_key().to_bytes_compressed()).0,
                    )
                    .expect("FATAL: failed to construct segwit p2wpkh address"),
                ));
            }

            // retry UTXO check a few times, in case bitcoind is still starting up
            for _ in 0..Self::UTXO_RETRY_COUNT {
                for (epoch_id, btc_addr) in &btc_addrs {
                    info!("Miner node: checking UTXOs at address: {btc_addr}");
                    let utxos =
                        burnchain.get_utxos(*epoch_id, &op_signer.get_public_key(), 1, None, 0);
                    if utxos.is_none() {
                        warn!("UTXOs not found for {btc_addr}. If this is unexpected, please ensure that your bitcoind instance is indexing transactions for the address {btc_addr} (importaddress)");
                    } else {
                        info!("UTXOs found - will run as a Miner node");
                        return true;
                    }
                }
                if self.config.get_node_config(false).mock_mining {
                    info!("No UTXOs found, but configured to mock mine");
                    return true;
                }
                thread::sleep(std::time::Duration::from_secs(Self::UTXO_RETRY_INTERVAL));
            }
            panic!("No UTXOs found, exiting");
        } else {
            info!("Will run as a Follower node");
            false
        }
    }

    /// Boot up the stacks chainstate.
    /// Instantiate the chainstate and push out the boot receipts to observers
    /// This is only public so we can test it.
    fn boot_chainstate(&mut self, burnchain_config: &Burnchain) -> StacksChainState {
        let use_test_genesis_data = use_test_genesis_chainstate(&self.config);

        // load up genesis balances
        let initial_balances = self
            .config
            .initial_balances
            .iter()
            .map(|e| (e.address.clone(), e.amount))
            .collect();

        // instantiate chainstate
        let mut boot_data = ChainStateBootData {
            initial_balances,
            post_flight_callback: None,
            first_burnchain_block_hash: burnchain_config.first_block_hash,
            first_burnchain_block_height: burnchain_config.first_block_height as u32,
            first_burnchain_block_timestamp: burnchain_config.first_block_timestamp,
            pox_constants: burnchain_config.pox_constants.clone(),
            get_bulk_initial_lockups: Some(Box::new(move || {
                get_account_lockups(use_test_genesis_data)
            })),
            get_bulk_initial_balances: Some(Box::new(move || {
                get_account_balances(use_test_genesis_data)
            })),
            get_bulk_initial_namespaces: Some(Box::new(move || {
                get_namespaces(use_test_genesis_data)
            })),
            get_bulk_initial_names: Some(Box::new(move || get_names(use_test_genesis_data))),
        };

        let (chain_state_db, receipts) = StacksChainState::open_and_exec(
            self.config.is_mainnet(),
            self.config.burnchain.chain_id,
            &self.config.get_chainstate_path_str(),
            Some(&mut boot_data),
            Some(self.config.node.get_marf_opts()),
        )
        .unwrap();
        run_loop::announce_boot_receipts(
            &mut self.event_dispatcher,
            &chain_state_db,
            &burnchain_config.pox_constants,
            &receipts,
        );
        chain_state_db
    }

    /// Instantiate the Stacks chain state and start the chains coordinator thread.
    /// Returns the coordinator thread handle, and the receiving end of the coordinator's atlas
    /// attachment channel.
    fn spawn_chains_coordinator(
        &mut self,
        burnchain_config: &Burnchain,
        coordinator_receivers: CoordinatorReceivers,
        miner_status: Arc<Mutex<MinerStatus>>,
    ) -> JoinHandle<()> {
        let use_test_genesis_data = use_test_genesis_chainstate(&self.config);

        // load up genesis Atlas attachments
        let mut atlas_config = AtlasConfig::new(self.config.is_mainnet());
        let genesis_attachments = GenesisData::new(use_test_genesis_data)
            .read_name_zonefiles()
            .map(|z| Attachment::new(z.zonefile_content.as_bytes().to_vec()))
            .collect();
        atlas_config.genesis_attachments = Some(genesis_attachments);

        let chain_state_db = self.boot_chainstate(burnchain_config);

        // NOTE: re-instantiate AtlasConfig so we don't have to keep the genesis attachments around
        let moved_atlas_config = self.config.atlas.clone();
        let moved_config = self.config.clone();
        let moved_burnchain_config = burnchain_config.clone();
        let coordinator_dispatcher = self.event_dispatcher.clone();
        let atlas_db = AtlasDB::connect(
            moved_atlas_config.clone(),
            &self.config.get_atlas_db_file_path(),
            true,
        )
        .expect("Failed to connect Atlas DB during startup");
        let coordinator_indexer =
            make_bitcoin_indexer(&self.config, Some(self.should_keep_running.clone()));

        let coordinator_thread_handle = thread::Builder::new()
            .name(format!(
                "chains-coordinator-{}",
                &moved_config.node.rpc_bind
            ))
            .stack_size(BLOCK_PROCESSOR_STACK_SIZE)
            .spawn(move || {
                debug!(
                    "chains-coordinator thread ID is {:?}",
                    thread::current().id()
                );
                let mut cost_estimator = moved_config.make_cost_estimator();
                let mut fee_estimator = moved_config.make_fee_estimator();

                let coord_config = ChainsCoordinatorConfig {
                    assume_present_anchor_blocks: moved_config.node.assume_present_anchor_blocks,
                    always_use_affirmation_maps: moved_config.node.always_use_affirmation_maps,
                    require_affirmed_anchor_blocks: moved_config
                        .node
                        .require_affirmed_anchor_blocks,
                    txindex: moved_config.node.txindex,
                };
                ChainsCoordinator::run(
                    coord_config,
                    chain_state_db,
                    moved_burnchain_config,
                    &coordinator_dispatcher,
                    coordinator_receivers,
                    moved_atlas_config,
                    cost_estimator.as_deref_mut(),
                    fee_estimator.as_deref_mut(),
                    miner_status,
                    coordinator_indexer,
                    atlas_db,
                );
            })
            .expect("FATAL: failed to start chains coordinator thread");

        coordinator_thread_handle
    }

    /// Start Prometheus logging
    fn start_prometheus(&mut self) {
        if self.monitoring_thread.is_some() {
            info!("Monitoring thread already running, nakamoto run-loop will not restart it");
            return;
        }
        let Some(prometheus_bind) = self.config.node.prometheus_bind.clone() else {
            return;
        };
        let monitoring_thread = thread::Builder::new()
            .name("prometheus".to_string())
            .spawn(move || {
                debug!("prometheus thread ID is {:?}", thread::current().id());
                start_serving_monitoring_metrics(prometheus_bind)
            })
            .expect("FATAL: failed to start monitoring thread");

        self.monitoring_thread.replace(monitoring_thread);
    }

    /// Get the sortition DB's highest block height, aligned to a reward cycle boundary, and the
    /// highest sortition.
    /// Returns (height at rc start, sortition)
    fn get_reward_cycle_sortition_db_height(
        sortdb: &SortitionDB,
        burnchain_config: &Burnchain,
    ) -> (u64, BlockSnapshot) {
        let (stacks_ch, _) = SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn())
            .expect("BUG: failed to load canonical stacks chain tip hash");

        let sn = match SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &stacks_ch)
            .expect("BUG: failed to query sortition DB")
        {
            Some(sn) => sn,
            None => {
                debug!("No canonical stacks chain tip hash present");
                let sn = SortitionDB::get_first_block_snapshot(sortdb.conn())
                    .expect("BUG: failed to get first-ever block snapshot");
                sn
            }
        };

        (
            burnchain_config.reward_cycle_to_block_height(
                burnchain_config
                    .block_height_to_reward_cycle(sn.block_height)
                    .expect("BUG: snapshot preceeds first reward cycle"),
            ),
            sn,
        )
    }

    /// Starts the node runloop.
    ///
    /// This function will block by looping infinitely.
    /// It will start the burnchain (separate thread), set-up a channel in
    /// charge of coordinating the new blocks coming from the burnchain and
    /// the nodes, taking turns on tenures.  
    pub fn start(
        &mut self,
        burnchain_opt: Option<Burnchain>,
        mut mine_start: u64,
        data_from_neon: Option<Neon2NakaData>,
    ) {
        let (coordinator_receivers, coordinator_senders) = self
            .coordinator_channels
            .take()
            .expect("Run loop already started, can only start once after initialization.");

        // setup the termination handler, allow it to error if a prior runloop already set it
        neon::RunLoop::setup_termination_handler(self.should_keep_running.clone(), true);

        let burnchain_result = neon::RunLoop::instantiate_burnchain_state(
            &self.config,
            self.should_keep_running.clone(),
            burnchain_opt,
            coordinator_senders.clone(),
        );

        let mut burnchain = match burnchain_result {
            Ok(burnchain_controller) => burnchain_controller,
            Err(burnchain_error::ShutdownInitiated) => {
                info!("Exiting stacks-node");
                return;
            }
            Err(e) => {
                error!("Error initializing burnchain: {e}");
                info!("Exiting stacks-node");
                return;
            }
        };

        let burnchain_config = burnchain.get_burnchain();
        self.burnchain = Some(burnchain_config.clone());

        // can we mine?
        let is_miner = self.check_is_miner(&mut burnchain);
        self.is_miner = Some(is_miner);

        // relayer linkup
        let (relay_send, relay_recv) = sync_channel(RELAYER_MAX_BUFFER);

        // set up globals so other subsystems can instantiate off of the runloop state.
        let globals = Globals::new(
            coordinator_senders,
            self.get_miner_status(),
            relay_send,
            self.counters.clone(),
            self.pox_watchdog_comms.clone(),
            self.should_keep_running.clone(),
            mine_start,
            LeaderKeyRegistrationState::default(),
        );
        self.set_globals(globals.clone());

        // have headers; boot up the chains coordinator and instantiate the chain state
        let coordinator_thread_handle = self.spawn_chains_coordinator(
            &burnchain_config,
            coordinator_receivers,
            globals.get_miner_status(),
        );
        self.start_prometheus();

        // We announce a new burn block so that the chains coordinator
        // can resume prior work and handle eventual unprocessed sortitions
        // stored during a previous session.
        globals.coord().announce_new_burn_block();

        // Make sure at least one sortition has happened, and make sure it's globally available
        let sortdb = burnchain.sortdb_mut();
        let (rc_aligned_height, sn) =
            RunLoop::get_reward_cycle_sortition_db_height(sortdb, &burnchain_config);

        let burnchain_tip_snapshot = if sn.block_height == burnchain_config.first_block_height {
            // need at least one sortition to happen.
            burnchain
                .wait_for_sortitions(globals.coord().clone(), sn.block_height + 1)
                .expect("Unable to get burnchain tip")
                .block_snapshot
        } else {
            sn
        };

        globals.set_last_sortition(burnchain_tip_snapshot);

        // Boot up the p2p network and relayer, and figure out how many sortitions we have so far
        // (it could be non-zero if the node is resuming from chainstate)
        let mut node = StacksNode::spawn(self, globals.clone(), relay_recv, data_from_neon);

        // Wait for all pending sortitions to process
        let burnchain_db = burnchain_config
            .open_burnchain_db(false)
            .expect("FATAL: failed to open burnchain DB");
        let burnchain_db_tip = burnchain_db
            .get_canonical_chain_tip()
            .expect("FATAL: failed to query burnchain DB");
        let mut burnchain_tip = burnchain
            .wait_for_sortitions(globals.coord().clone(), burnchain_db_tip.block_height)
            .expect("Unable to get burnchain tip");

        // Start the runloop
        debug!("Runloop: Begin run loop");
        self.counters.bump_blocks_processed();

        let mut sortition_db_height = rc_aligned_height;
        let mut burnchain_height = sortition_db_height;
        let mut num_sortitions_in_last_cycle;

        // prepare to fetch the first reward cycle!
        let mut target_burnchain_block_height = cmp::min(
            burnchain_config.reward_cycle_to_block_height(
                burnchain_config
                    .block_height_to_reward_cycle(burnchain_height)
                    .expect("BUG: block height is not in a reward cycle")
                    + 1,
            ),
            burnchain.get_headers_height() - 1,
        );

        debug!("Runloop: Begin main runloop starting a burnchain block {sortition_db_height}");

        let mut last_tenure_sortition_height = 0;
        let mut poll_deadline = 0;

        loop {
            if !globals.keep_running() {
                // The p2p thread relies on the same atomic_bool, it will
                // discontinue its execution after completing its ongoing runloop epoch.
                info!("Terminating p2p process");
                info!("Terminating relayer");
                info!("Terminating chains-coordinator");

                globals.coord().stop_chains_coordinator();
                coordinator_thread_handle.join().unwrap();
                node.join();

                info!("Exiting stacks-node");
                break;
            }

            let remote_chain_height = burnchain.get_headers_height() - 1;

            // wait for the p2p state-machine to do at least one pass
            debug!("Runloop: Wait until Stacks block downloads reach a quiescent state before processing more burnchain blocks"; "remote_chain_height" => remote_chain_height, "local_chain_height" => burnchain_height);

            // TODO: for now, we just set initial block download false.
            //   I think that the sync watchdog probably needs to change a fair bit
            //   for nakamoto. There may be some opportunity to refactor this runloop
            //   as well (e.g., the `mine_start` should be integrated with the
            //   watchdog so that there's just one source of truth about ibd),
            //   but I think all of this can be saved for post-neon work.
            let ibd = false;
            self.pox_watchdog_comms.set_ibd(ibd);

            // calculate burnchain sync percentage
            let percent: f64 = if remote_chain_height > 0 {
                burnchain_tip.block_snapshot.block_height as f64 / remote_chain_height as f64
            } else {
                0.0
            };

            // Download each burnchain block and process their sortitions.  This, in turn, will
            // cause the node's p2p and relayer threads to go fetch and download Stacks blocks and
            // process them.  This loop runs for one reward cycle, so that the next pass of the
            // runloop will cause the PoX sync watchdog to wait until it believes that the node has
            // obtained all the Stacks blocks it can.
            debug!(
                "Runloop: Download burnchain blocks up to reward cycle #{} (height {target_burnchain_block_height})",
                burnchain_config
                    .block_height_to_reward_cycle(target_burnchain_block_height)
                    .expect("FATAL: target burnchain block height does not have a reward cycle");
                "total_burn_sync_percent" => %percent,
                "local_burn_height" => burnchain_tip.block_snapshot.block_height,
                "remote_tip_height" => remote_chain_height
            );

            loop {
                if !globals.keep_running() {
                    break;
                }

                if poll_deadline > get_epoch_time_secs() {
                    sleep_ms(1_000);
                    continue;
                }
                poll_deadline = get_epoch_time_secs() + self.config().burnchain.poll_time_secs;

                let (next_burnchain_tip, tip_burnchain_height) =
                    match burnchain.sync(Some(target_burnchain_block_height)) {
                        Ok(x) => x,
                        Err(e) => {
                            warn!("Runloop: Burnchain controller stopped: {e}");
                            continue;
                        }
                    };

                // *now* we know the burnchain height
                burnchain_tip = next_burnchain_tip;
                burnchain_height = tip_burnchain_height;

                let sortition_tip = &burnchain_tip.block_snapshot.sortition_id;
                let next_sortition_height = burnchain_tip.block_snapshot.block_height;

                if next_sortition_height != last_tenure_sortition_height {
                    info!(
                        "Runloop: Downloaded burnchain blocks up to height {burnchain_height}; target height is {target_burnchain_block_height}; remote_chain_height = {remote_chain_height} next_sortition_height = {next_sortition_height}, sortition_db_height = {sortition_db_height}"
                    );
                }

                if next_sortition_height > sortition_db_height {
                    debug!(
                        "Runloop: New burnchain block height {next_sortition_height} > {sortition_db_height}"
                    );

                    let mut sort_count = 0;

                    debug!("Runloop: block mining until we process all sortitions");
                    signal_mining_blocked(globals.get_miner_status());

                    // first, let's process all blocks in (sortition_db_height, next_sortition_height]
                    for block_to_process in (sortition_db_height + 1)..(next_sortition_height + 1) {
                        // stop mining so we can advance the sortition DB and so our
                        // ProcessTenure() directive (sent by relayer_sortition_notify() below)
                        // will be unblocked.

                        let block = {
                            let ic = burnchain.sortdb_ref().index_conn();
                            SortitionDB::get_ancestor_snapshot(&ic, block_to_process, sortition_tip)
                                .unwrap()
                                .expect(
                                    "Failed to find block in fork processed by burnchain indexer",
                                )
                        };
                        if block.sortition {
                            sort_count += 1;
                        }

                        let sortition_id = &block.sortition_id;

                        // Have the node process the new block, that can include, or not, a sortition.
                        if let Err(e) = node.process_burnchain_state(
                            self.config(),
                            burnchain.sortdb_mut(),
                            sortition_id,
                            ibd,
                        ) {
                            // relayer errored, exit.
                            error!("Runloop: Block relayer and miner errored, exiting."; "err" => ?e);
                            return;
                        }
                    }

                    debug!("Runloop: enable miner after processing sortitions");
                    signal_mining_ready(globals.get_miner_status());

                    num_sortitions_in_last_cycle = sort_count;
                    debug!(
                        "Runloop: Synchronized sortitions up to block height {next_sortition_height} from {sortition_db_height} (chain tip height is {burnchain_height}); {num_sortitions_in_last_cycle} sortitions"
                    );

                    sortition_db_height = next_sortition_height;
                } else if ibd {
                    // drive block processing after we reach the burnchain tip.
                    // we may have downloaded all the blocks already,
                    // so we can't rely on the relayer alone to
                    // drive it.
                    globals.coord().announce_new_stacks_block();
                }

                if burnchain_height >= target_burnchain_block_height
                    || burnchain_height >= remote_chain_height
                {
                    break;
                }
            }

            // advance one reward cycle at a time.
            // If we're still downloading, then this is simply target_burnchain_block_height + reward_cycle_len.
            // Otherwise, this is burnchain_tip + reward_cycle_len
            let next_target_burnchain_block_height = cmp::min(
                burnchain_config.reward_cycle_to_block_height(
                    burnchain_config
                        .block_height_to_reward_cycle(target_burnchain_block_height)
                        .expect("FATAL: burnchain height before system start")
                        + 1,
                ),
                remote_chain_height,
            );

            debug!("Runloop: Advance target burnchain block height from {target_burnchain_block_height} to {next_target_burnchain_block_height} (sortition height {sortition_db_height})");
            target_burnchain_block_height = next_target_burnchain_block_height;

            if sortition_db_height >= burnchain_height && !ibd {
                let canonical_stacks_tip_height =
                    SortitionDB::get_canonical_burn_chain_tip(burnchain.sortdb_ref().conn())
                        .map(|snapshot| snapshot.canonical_stacks_tip_height)
                        .unwrap_or(0);
                if canonical_stacks_tip_height < mine_start {
                    info!(
                        "Runloop: Synchronized full burnchain, but stacks tip height is {canonical_stacks_tip_height}, and we are trying to boot to {mine_start}, not mining until reaching chain tip"
                    );
                } else {
                    // once we've synced to the chain tip once, don't apply this check again.
                    //  this prevents a possible corner case in the event of a PoX fork.
                    mine_start = 0;

                    // at tip, and not downloading. proceed to mine.
                    if last_tenure_sortition_height != sortition_db_height {
                        if is_miner {
                            info!(
                                "Runloop: Synchronized full burnchain up to height {sortition_db_height}. Proceeding to mine blocks"
                            );
                        } else {
                            info!(
                                "Runloop: Synchronized full burnchain up to height {sortition_db_height}."
                            );
                        }
                        last_tenure_sortition_height = sortition_db_height;
                        globals.raise_initiative("runloop-synced".to_string());
                    }
                }
            }
        }
    }
}
