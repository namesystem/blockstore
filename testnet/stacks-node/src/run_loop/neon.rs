#[cfg(test)]
use std::sync::atomic::AtomicU64;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::sync_channel;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::{cmp, thread};

use libc;
use stacks::burnchains::bitcoin::address::{BitcoinAddress, LegacyBitcoinAddressType};
use stacks::burnchains::{Burnchain, Error as burnchain_error};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::burn::BlockSnapshot;
use stacks::chainstate::coordinator::comm::{CoordinatorChannels, CoordinatorReceivers};
use stacks::chainstate::coordinator::{
    migrate_chainstate_dbs, static_get_canonical_affirmation_map,
    static_get_heaviest_affirmation_map, static_get_stacks_tip_affirmation_map, ChainsCoordinator,
    ChainsCoordinatorConfig, CoordinatorCommunication, Error as coord_error,
};
use stacks::chainstate::stacks::db::{ChainStateBootData, StacksChainState};
use stacks::chainstate::stacks::miner::{signal_mining_blocked, signal_mining_ready, MinerStatus};
use stacks::core::StacksEpochId;
use stacks::net::atlas::{AtlasConfig, AtlasDB, Attachment};
#[cfg(test)]
use stacks::util::tests::TestFlag;
use stacks::util_lib::db::Error as db_error;
use stacks_common::deps_common::ctrlc as termination;
use stacks_common::deps_common::ctrlc::SignalId;
use stacks_common::types::PublicKey;
use stacks_common::util::hash::Hash160;
use stacks_common::util::{get_epoch_time_secs, sleep_ms};
use stx_genesis::GenesisData;

use super::RunLoopCallbacks;
use crate::burnchains::{make_bitcoin_indexer, Error};
use crate::globals::NeonGlobals as Globals;
use crate::monitoring::{start_serving_monitoring_metrics, MonitoringError};
use crate::neon_node::{
    LeaderKeyRegistrationState, StacksNode, BLOCK_PROCESSOR_STACK_SIZE, RELAYER_MAX_BUFFER,
};
use crate::node::{
    get_account_balances, get_account_lockups, get_names, get_namespaces,
    use_test_genesis_chainstate,
};
use crate::run_loop::boot_nakamoto::Neon2NakaData;
use crate::syncctl::{PoxSyncWatchdog, PoxSyncWatchdogComms};
use crate::{
    run_loop, BitcoinRegtestController, BurnchainController, Config, EventDispatcher, Keychain,
};

pub const STDERR: i32 = 2;

#[cfg(test)]
#[derive(Clone)]
pub struct RunLoopCounter(pub Arc<AtomicU64>);

#[cfg(not(test))]
#[derive(Clone)]
pub struct RunLoopCounter();

#[cfg(test)]
const UNCONDITIONAL_CHAIN_LIVENESS_CHECK: u64 = 30;

#[cfg(not(test))]
const UNCONDITIONAL_CHAIN_LIVENESS_CHECK: u64 = 300;

impl Default for RunLoopCounter {
    #[cfg(test)]
    fn default() -> Self {
        RunLoopCounter(Arc::new(AtomicU64::new(0)))
    }
    #[cfg(not(test))]
    fn default() -> Self {
        Self()
    }
}

impl RunLoopCounter {
    #[cfg(test)]
    pub fn get(&self) -> u64 {
        self.0.load(Ordering::SeqCst)
    }

    #[cfg(test)]
    pub fn load(&self, ordering: Ordering) -> u64 {
        self.0.load(ordering)
    }
}

#[cfg(test)]
impl std::ops::Deref for RunLoopCounter {
    type Target = Arc<AtomicU64>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Default)]
pub struct Counters {
    pub blocks_processed: RunLoopCounter,
    pub microblocks_processed: RunLoopCounter,
    pub missed_tenures: RunLoopCounter,
    pub missed_microblock_tenures: RunLoopCounter,
    pub cancelled_commits: RunLoopCounter,

    pub sortitions_processed: RunLoopCounter,

    pub naka_submitted_vrfs: RunLoopCounter,
    pub naka_submitted_commits: RunLoopCounter,
    /// the burn block height when the last commit was submitted
    pub naka_submitted_commit_last_burn_height: RunLoopCounter,
    pub naka_mined_blocks: RunLoopCounter,
    pub naka_rejected_blocks: RunLoopCounter,
    pub naka_proposed_blocks: RunLoopCounter,
    pub naka_mined_tenures: RunLoopCounter,
    pub naka_signer_pushed_blocks: RunLoopCounter,
    pub naka_miner_directives: RunLoopCounter,
    pub naka_submitted_commit_last_stacks_tip: RunLoopCounter,

    pub naka_miner_current_rejections: RunLoopCounter,
    pub naka_miner_current_rejections_timeout_secs: RunLoopCounter,

    #[cfg(test)]
    pub naka_skip_commit_op: TestFlag<bool>,
}

impl Counters {
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(test)]
    fn inc(ctr: &RunLoopCounter) {
        ctr.0.fetch_add(1, Ordering::SeqCst);
    }

    #[cfg(not(test))]
    fn inc(_ctr: &RunLoopCounter) {}

    #[cfg(test)]
    fn set(ctr: &RunLoopCounter, value: u64) {
        ctr.0.store(value, Ordering::SeqCst);
    }

    #[cfg(not(test))]
    fn set(_ctr: &RunLoopCounter, _value: u64) {}

    pub fn bump_blocks_processed(&self) {
        Counters::inc(&self.blocks_processed);
    }

    pub fn bump_sortitions_processed(&self) {
        Counters::inc(&self.sortitions_processed);
    }

    pub fn bump_microblocks_processed(&self) {
        Counters::inc(&self.microblocks_processed);
    }

    pub fn bump_missed_tenures(&self) {
        Counters::inc(&self.missed_tenures);
    }

    pub fn bump_missed_microblock_tenures(&self) {
        Counters::inc(&self.missed_microblock_tenures);
    }

    pub fn bump_cancelled_commits(&self) {
        Counters::inc(&self.cancelled_commits);
    }

    pub fn bump_naka_submitted_vrfs(&self) {
        Counters::inc(&self.naka_submitted_vrfs);
    }

    pub fn bump_naka_submitted_commits(
        &self,
        committed_burn_height: u64,
        committed_stacks_height: u64,
    ) {
        Counters::inc(&self.naka_submitted_commits);
        Counters::set(
            &self.naka_submitted_commit_last_burn_height,
            committed_burn_height,
        );
        Counters::set(
            &self.naka_submitted_commit_last_stacks_tip,
            committed_stacks_height,
        );
    }

    pub fn bump_naka_mined_blocks(&self) {
        Counters::inc(&self.naka_mined_blocks);
    }

    pub fn bump_naka_proposed_blocks(&self) {
        Counters::inc(&self.naka_proposed_blocks);
    }

    pub fn bump_naka_rejected_blocks(&self) {
        Counters::inc(&self.naka_rejected_blocks);
    }

    pub fn bump_naka_signer_pushed_blocks(&self) {
        Counters::inc(&self.naka_signer_pushed_blocks);
    }

    pub fn bump_naka_mined_tenures(&self) {
        Counters::inc(&self.naka_mined_tenures);
    }

    pub fn bump_naka_miner_directives(&self) {
        Counters::inc(&self.naka_miner_directives);
    }

    pub fn set_microblocks_processed(&self, value: u64) {
        Counters::set(&self.microblocks_processed, value)
    }

    pub fn set_miner_current_rejections_timeout_secs(&self, value: u64) {
        Counters::set(&self.naka_miner_current_rejections_timeout_secs, value)
    }

    pub fn set_miner_current_rejections(&self, value: u32) {
        Counters::set(&self.naka_miner_current_rejections, u64::from(value))
    }
}

/// Coordinating a node running in neon mode.
pub struct RunLoop {
    config: Config,
    pub callbacks: RunLoopCallbacks,
    globals: Option<Globals>,
    counters: Counters,
    coordinator_channels: Option<(CoordinatorReceivers, CoordinatorChannels)>,
    should_keep_running: Arc<AtomicBool>,
    event_dispatcher: EventDispatcher,
    pox_watchdog: Option<PoxSyncWatchdog>, // can't be instantiated until .start() is called
    is_miner: Option<bool>,                // not known until .start() is called
    burnchain: Option<Burnchain>,          // not known until .start() is called
    pox_watchdog_comms: PoxSyncWatchdogComms,
    /// NOTE: this is duplicated in self.globals, but it needs to be accessible before globals is
    /// instantiated (namely, so the test framework can access it).
    miner_status: Arc<Mutex<MinerStatus>>,
    monitoring_thread: Option<JoinHandle<Result<(), MonitoringError>>>,
}

/// Write to stderr in an async-safe manner.
/// See signal-safety(7)
fn async_safe_write_stderr(msg: &str) {
    #[cfg(windows)]
    unsafe {
        // write(2) inexplicably has a different ABI only on Windows.
        libc::write(
            STDERR,
            msg.as_ptr() as *const libc::c_void,
            msg.len() as u32,
        );
    }
    #[cfg(not(windows))]
    unsafe {
        libc::write(STDERR, msg.as_ptr() as *const libc::c_void, msg.len());
    }
}

impl RunLoop {
    /// Sets up a runloop and node, given a config.
    pub fn new(config: Config) -> Self {
        let channels = CoordinatorCommunication::instantiate();
        let should_keep_running = Arc::new(AtomicBool::new(true));
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
            callbacks: RunLoopCallbacks::new(),
            counters: Counters::default(),
            should_keep_running,
            event_dispatcher,
            pox_watchdog: None,
            is_miner: None,
            burnchain: None,
            pox_watchdog_comms,
            miner_status,
            monitoring_thread: None,
        }
    }

    pub fn get_globals(&self) -> Globals {
        self.globals
            .clone()
            .expect("FATAL: globals not instantiated")
    }

    fn set_globals(&mut self, globals: Globals) {
        self.globals = Some(globals);
    }

    pub fn get_coordinator_channel(&self) -> Option<CoordinatorChannels> {
        self.coordinator_channels.as_ref().map(|x| x.1.clone())
    }

    pub fn get_blocks_processed_arc(&self) -> RunLoopCounter {
        self.counters.blocks_processed.clone()
    }

    pub fn get_microblocks_processed_arc(&self) -> RunLoopCounter {
        self.counters.microblocks_processed.clone()
    }

    pub fn get_missed_tenures_arc(&self) -> RunLoopCounter {
        self.counters.missed_tenures.clone()
    }

    pub fn get_missed_microblock_tenures_arc(&self) -> RunLoopCounter {
        self.counters.missed_microblock_tenures.clone()
    }

    pub fn get_cancelled_commits_arc(&self) -> RunLoopCounter {
        self.counters.cancelled_commits.clone()
    }

    pub fn get_counters(&self) -> Counters {
        self.counters.clone()
    }

    pub fn config(&self) -> &Config {
        &self.config
    }

    pub fn get_event_dispatcher(&self) -> EventDispatcher {
        self.event_dispatcher.clone()
    }

    pub fn is_miner(&self) -> bool {
        self.is_miner.unwrap_or(false)
    }

    pub fn get_pox_sync_comms(&self) -> PoxSyncWatchdogComms {
        self.pox_watchdog_comms.clone()
    }

    pub fn get_termination_switch(&self) -> Arc<AtomicBool> {
        self.should_keep_running.clone()
    }

    pub fn get_burnchain(&self) -> Burnchain {
        self.burnchain
            .clone()
            .expect("FATAL: tried to get runloop burnchain before calling .start()")
    }

    pub fn get_pox_watchdog(&mut self) -> &mut PoxSyncWatchdog {
        self.pox_watchdog
            .as_mut()
            .expect("FATAL: tried to get PoX watchdog before calling .start()")
    }

    pub fn get_miner_status(&self) -> Arc<Mutex<MinerStatus>> {
        self.miner_status.clone()
    }

    /// Set up termination handler.  Have a signal set the `should_keep_running` atomic bool to
    /// false.  Panics of called more than once.
    pub fn setup_termination_handler(keep_running_writer: Arc<AtomicBool>, allow_err: bool) {
        let install = termination::set_handler(move |sig_id| match sig_id {
            SignalId::Bus => {
                let msg = "Caught SIGBUS; crashing immediately and dumping core\n";
                async_safe_write_stderr(msg);
                unsafe {
                    libc::abort();
                }
            }
            _ => {
                let msg = format!("Graceful termination request received (signal `{sig_id}`), will complete the ongoing runloop cycles and terminate\n");
                async_safe_write_stderr(&msg);
                keep_running_writer.store(false, Ordering::SeqCst);
            }
        });

        if let Err(e) = install {
            // integration tests can do this
            if cfg!(test) || allow_err {
                info!("Error setting up signal handler, may have already been set");
            } else {
                panic!("FATAL: error setting termination handler - {e}");
            }
        }
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

    /// Instantiate the burnchain client and databases.
    /// Fetches headers and instantiates the burnchain.
    /// Panics on failure.
    pub fn instantiate_burnchain_state(
        config: &Config,
        should_keep_running: Arc<AtomicBool>,
        burnchain_opt: Option<Burnchain>,
        coordinator_senders: CoordinatorChannels,
    ) -> Result<BitcoinRegtestController, burnchain_error> {
        // Initialize and start the burnchain.
        let mut burnchain_controller = BitcoinRegtestController::with_burnchain(
            config.clone(),
            Some(coordinator_senders),
            burnchain_opt,
            Some(should_keep_running.clone()),
        );

        let burnchain = burnchain_controller.get_burnchain();
        let epochs = burnchain_controller.get_stacks_epochs();

        // sanity check -- epoch data must be valid
        Config::assert_valid_epoch_settings(&burnchain, &epochs);

        // Upgrade chainstate databases if they exist already
        // NOTE: this has to be done before the subsequent call to
        // `burnchain_controller.connect_dbs()` below!
        match migrate_chainstate_dbs(
            &epochs,
            &burnchain,
            &config.get_burn_db_file_path(),
            &config.get_chainstate_path_str(),
            Some(config.node.get_marf_opts()),
        ) {
            Ok(_) => {}
            Err(coord_error::DBError(db_error::TooOldForEpoch)) => {
                error!(
                    "FATAL: chainstate database(s) are not compatible with the current system epoch"
                );
                panic!();
            }
            Err(e) => {
                panic!("FATAL: unable to query filesystem or databases: {e:?}");
            }
        }

        info!("Start syncing Bitcoin headers, feel free to grab a cup of coffee, this can take a while");

        let burnchain_config = burnchain_controller.get_burnchain();
        let target_burnchain_block_height = match burnchain_config
            .get_highest_burnchain_block()
            .expect("FATAL: failed to access burnchain database")
        {
            Some(burnchain_tip) => {
                // database exists already, and has blocks -- just sync to its tip.
                let target_height = burnchain_tip.block_height + 1;
                debug!("Burnchain DB exists and has blocks up to {}; synchronizing from where it left off up to {target_height}", burnchain_tip.block_height);
                target_height
            }
            None => {
                // database does not exist yet
                let target_height = 1.max(burnchain_config.first_block_height + 1);
                debug!("Burnchain DB does not exist or does not have blocks; synchronizing to first burnchain block height {target_height}");
                target_height
            }
        };

        burnchain_controller
            .start(Some(target_burnchain_block_height))
            .map_err(|e| {
                if matches!(e, Error::CoordinatorClosed)
                    && !should_keep_running.load(Ordering::SeqCst)
                {
                    info!("Shutdown initiated during burnchain initialization: {e}");
                    return burnchain_error::ShutdownInitiated;
                }
                error!("Burnchain controller stopped: {e}");
                panic!();
            })?;

        // if the chainstate DBs don't exist, this will instantiate them
        if let Err(e) = burnchain_controller.connect_dbs() {
            error!("Failed to connect to burnchain databases: {e}");
            panic!();
        };

        // TODO (hack) instantiate the sortdb in the burnchain
        let _ = burnchain_controller.sortdb_mut();
        Ok(burnchain_controller)
    }

    /// Boot up the stacks chainstate.
    /// Instantiate the chainstate and push out the boot receipts to observers
    /// This is only public so we can test it.
    pub fn boot_chainstate(&mut self, burnchain_config: &Burnchain) -> StacksChainState {
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

        info!("About to call open_and_exec");
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

    /// Instantiate the PoX watchdog
    fn instantiate_pox_watchdog(&mut self) {
        let pox_watchdog = PoxSyncWatchdog::new(&self.config, self.pox_watchdog_comms.clone())
            .expect("FATAL: failed to instantiate PoX sync watchdog");
        self.pox_watchdog = Some(pox_watchdog);
    }

    /// Start Prometheus logging
    fn start_prometheus(&mut self) {
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

    pub fn take_monitoring_thread(&mut self) -> Option<JoinHandle<Result<(), MonitoringError>>> {
        self.monitoring_thread.take()
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

    /// Wake up and drive stacks block processing if there's been a PoX reorg.
    /// Be careful not to saturate calls to announce new stacks blocks, because that will disable
    /// mining (which would prevent a miner attempting to fix a hidden PoX anchor block from making
    /// progress).
    fn drive_pox_reorg_stacks_block_processing(
        globals: &Globals,
        config: &Config,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        last_stacks_pox_reorg_recover_time: &mut u128,
    ) {
        let miner_config = config.get_miner_config();
        let delay = cmp::max(
            config.node.chain_liveness_poll_time_secs,
            cmp::max(
                miner_config.first_attempt_time_ms,
                miner_config.subsequent_attempt_time_ms,
            ) / 1000,
        );

        if *last_stacks_pox_reorg_recover_time + (delay as u128) >= get_epoch_time_secs().into() {
            // too soon
            return;
        }

        // compare stacks and heaviest AMs
        let burnchain_db = burnchain
            .open_burnchain_db(false)
            .expect("FATAL: failed to open burnchain DB");

        let sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .expect("FATAL: could not read sortition DB");

        let indexer = make_bitcoin_indexer(config, Some(globals.should_keep_running.clone()));

        let heaviest_affirmation_map = match static_get_heaviest_affirmation_map(
            burnchain,
            &indexer,
            &burnchain_db,
            sortdb,
            &sn.sortition_id,
        ) {
            Ok(am) => am,
            Err(e) => {
                warn!("Failed to find heaviest affirmation map: {e:?}");
                return;
            }
        };

        let highest_sn = SortitionDB::get_highest_known_burn_chain_tip(sortdb.conn())
            .expect("FATAL: could not read sortition DB");

        let canonical_burnchain_tip = burnchain_db
            .get_canonical_chain_tip()
            .expect("FATAL: could not read burnchain DB");

        let sortition_tip_affirmation_map =
            match SortitionDB::find_sortition_tip_affirmation_map(sortdb, &sn.sortition_id) {
                Ok(am) => am,
                Err(e) => {
                    warn!("Failed to find sortition affirmation map: {e:?}");
                    return;
                }
            };

        let stacks_tip_affirmation_map = static_get_stacks_tip_affirmation_map(
            &burnchain_db,
            sortdb,
            &sn.sortition_id,
            &sn.canonical_stacks_tip_consensus_hash,
            &sn.canonical_stacks_tip_hash,
        )
        .expect("FATAL: could not query stacks DB");

        if stacks_tip_affirmation_map.len() < heaviest_affirmation_map.len()
            || stacks_tip_affirmation_map
                .find_divergence(&heaviest_affirmation_map)
                .is_some()
        {
            // the sortition affirmation map might also be inconsistent, so we'll need to fix that
            // (i.e. the underlying sortitions) before we can fix the stacks fork
            if sortition_tip_affirmation_map.len() < heaviest_affirmation_map.len()
                || sortition_tip_affirmation_map
                    .find_divergence(&heaviest_affirmation_map)
                    .is_some()
            {
                debug!("Drive burn block processing: possible PoX reorg (sortition tip: {sortition_tip_affirmation_map}, heaviest: {heaviest_affirmation_map})");
                globals.coord().announce_new_burn_block();
            } else if highest_sn.block_height == sn.block_height
                && sn.block_height == canonical_burnchain_tip.block_height
            {
                // need to force an affirmation reorg because there will be no more burn block
                // announcements.
                debug!("Drive burn block processing: possible PoX reorg (sortition tip: {sortition_tip_affirmation_map}, heaviest: {heaviest_affirmation_map}, burn height {})", sn.block_height);
                globals.coord().announce_new_burn_block();
            }

            debug!(
                "Drive stacks block processing: possible PoX reorg (stacks tip: {stacks_tip_affirmation_map}, heaviest: {heaviest_affirmation_map})"
            );
            globals.coord().announce_new_stacks_block();
        } else {
            debug!(
                "Drive stacks block processing: no need (stacks tip: {stacks_tip_affirmation_map}, heaviest: {heaviest_affirmation_map})"
            );

            // announce a new stacks block to force the chains coordinator
            //  to wake up anyways. this isn't free, so we have to make sure
            //  the chain-liveness thread doesn't wake up too often
            globals.coord().announce_new_stacks_block();
        }

        *last_stacks_pox_reorg_recover_time = get_epoch_time_secs().into();
    }

    /// Wake up and drive sortition processing if there's been a PoX reorg.
    /// Be careful not to saturate calls to announce new burn blocks, because that will disable
    /// mining (which would prevent a miner attempting to fix a hidden PoX anchor block from making
    /// progress).
    ///
    /// only call if no in ibd
    fn drive_pox_reorg_burn_block_processing(
        globals: &Globals,
        config: &Config,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        chain_state_db: &StacksChainState,
        last_burn_pox_reorg_recover_time: &mut u128,
        last_announce_time: &mut u128,
    ) {
        let miner_config = config.get_miner_config();
        let delay = cmp::max(
            config.node.chain_liveness_poll_time_secs,
            cmp::max(
                miner_config.first_attempt_time_ms,
                miner_config.subsequent_attempt_time_ms,
            ) / 1000,
        );

        if *last_burn_pox_reorg_recover_time + (delay as u128) >= get_epoch_time_secs().into() {
            // too soon
            return;
        }

        // compare sortition and heaviest AMs
        let burnchain_db = burnchain
            .open_burnchain_db(false)
            .expect("FATAL: failed to open burnchain DB");

        let highest_sn = SortitionDB::get_highest_known_burn_chain_tip(sortdb.conn())
            .expect("FATAL: could not read sortition DB");

        let canonical_burnchain_tip = burnchain_db
            .get_canonical_chain_tip()
            .expect("FATAL: could not read burnchain DB");

        if canonical_burnchain_tip.block_height > highest_sn.block_height {
            // still processing sortitions
            test_debug!(
                "Drive burn block processing: still processing sortitions ({} > {})",
                canonical_burnchain_tip.block_height,
                highest_sn.block_height
            );
            return;
        }

        // NOTE: this could be lower than the highest_sn
        let sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())
            .expect("FATAL: could not read sortition DB");

        let sortition_tip_affirmation_map =
            match SortitionDB::find_sortition_tip_affirmation_map(sortdb, &sn.sortition_id) {
                Ok(am) => am,
                Err(e) => {
                    warn!("Failed to find sortition affirmation map: {e:?}");
                    return;
                }
            };

        let indexer = make_bitcoin_indexer(config, Some(globals.should_keep_running.clone()));

        let heaviest_affirmation_map = match static_get_heaviest_affirmation_map(
            burnchain,
            &indexer,
            &burnchain_db,
            sortdb,
            &sn.sortition_id,
        ) {
            Ok(am) => am,
            Err(e) => {
                warn!("Failed to find heaviest affirmation map: {e:?}");
                return;
            }
        };

        let canonical_affirmation_map = match static_get_canonical_affirmation_map(
            burnchain,
            &indexer,
            &burnchain_db,
            sortdb,
            chain_state_db,
            &sn.sortition_id,
        ) {
            Ok(am) => am,
            Err(e) => {
                warn!("Failed to find canonical affirmation map: {e:?}");
                return;
            }
        };

        if sortition_tip_affirmation_map.len() < heaviest_affirmation_map.len()
            || sortition_tip_affirmation_map
                .find_divergence(&heaviest_affirmation_map)
                .is_some()
            || sn.block_height < highest_sn.block_height
        {
            debug!("Drive burn block processing: possible PoX reorg (sortition tip: {sortition_tip_affirmation_map}, heaviest: {heaviest_affirmation_map}, {} <? {})", sn.block_height, highest_sn.block_height);
            globals.coord().announce_new_burn_block();
            globals.coord().announce_new_stacks_block();
            *last_announce_time = get_epoch_time_secs().into();
        } else if sortition_tip_affirmation_map.len() >= heaviest_affirmation_map.len()
            && sortition_tip_affirmation_map.len() <= canonical_affirmation_map.len()
        {
            if let Some(divergence_rc) =
                canonical_affirmation_map.find_divergence(&sortition_tip_affirmation_map)
            {
                if divergence_rc + 1 >= (heaviest_affirmation_map.len() as u64) {
                    // we have unaffirmed PoX anchor blocks that are not yet processed in the sortition history
                    debug!("Drive burnchain processing: possible PoX reorg from unprocessed anchor block(s) (sortition tip: {sortition_tip_affirmation_map}, heaviest: {heaviest_affirmation_map}, canonical: {canonical_affirmation_map})");
                    globals.coord().announce_new_burn_block();
                    globals.coord().announce_new_stacks_block();
                    *last_announce_time = get_epoch_time_secs().into();
                }
            }
        } else {
            debug!(
                "Drive burn block processing: no need (sortition tip: {sortition_tip_affirmation_map}, heaviest: {heaviest_affirmation_map}, {} </ {})",
                sn.block_height,
                highest_sn.block_height
            );
        }

        *last_burn_pox_reorg_recover_time = get_epoch_time_secs().into();

        // unconditionally bump every 5 minutes, just in case.
        // this can get the node un-stuck if we're short on sortition processing but are unable to
        // sync with the remote node because it keeps NACK'ing us, leading to a runloop stall.
        if *last_announce_time + (UNCONDITIONAL_CHAIN_LIVENESS_CHECK as u128)
            < get_epoch_time_secs().into()
        {
            debug!("Drive burnchain processing: unconditional bump");
            globals.coord().announce_new_burn_block();
            globals.coord().announce_new_stacks_block();
            *last_announce_time = get_epoch_time_secs().into();
        }
    }

    /// In a separate thread, periodically drive coordinator liveness by checking to see if there's
    /// a pending reorg and if so, waking up the coordinator to go and process new blocks
    fn drive_chain_liveness(
        globals: Globals,
        config: Config,
        burnchain: Burnchain,
        sortdb: SortitionDB,
        chain_state_db: StacksChainState,
    ) {
        let mut last_burn_pox_reorg_recover_time = 0;
        let mut last_stacks_pox_reorg_recover_time = 0;
        let mut last_burn_announce_time = 0;

        debug!("Chain-liveness thread start!");

        while globals.keep_running() {
            debug!("Chain-liveness checkup");
            Self::drive_pox_reorg_burn_block_processing(
                &globals,
                &config,
                &burnchain,
                &sortdb,
                &chain_state_db,
                &mut last_burn_pox_reorg_recover_time,
                &mut last_burn_announce_time,
            );
            Self::drive_pox_reorg_stacks_block_processing(
                &globals,
                &config,
                &burnchain,
                &sortdb,
                &mut last_stacks_pox_reorg_recover_time,
            );

            sleep_ms(3000);
        }

        debug!("Chain-liveness thread exit!");
    }

    /// Spawn a thread to drive chain liveness
    fn spawn_chain_liveness_thread(&self, globals: Globals) -> JoinHandle<()> {
        let config = self.config.clone();
        let burnchain = self.get_burnchain();
        let sortdb = burnchain
            .open_sortition_db(true)
            .expect("FATAL: could not open sortition DB");

        let (chain_state_db, _) = StacksChainState::open(
            config.is_mainnet(),
            config.burnchain.chain_id,
            &config.get_chainstate_path_str(),
            Some(config.node.get_marf_opts()),
        )
        .unwrap();

        thread::Builder::new()
            .name(format!("chain-liveness-{}", config.node.rpc_bind))
            .stack_size(BLOCK_PROCESSOR_STACK_SIZE)
            .spawn(move || {
                Self::drive_chain_liveness(globals, config, burnchain, sortdb, chain_state_db)
            })
            .expect("FATAL: failed to spawn chain liveness thread")
    }

    /// Starts the node runloop.
    ///
    /// This function will block by looping infinitely.
    /// It will start the burnchain (separate thread), set-up a channel in
    /// charge of coordinating the new blocks coming from the burnchain and
    /// the nodes, taking turns on tenures.
    ///
    /// Returns `Option<NeonGlobals>` so that data can be passed to `NakamotoNode`
    pub fn start(
        &mut self,
        burnchain_opt: Option<Burnchain>,
        mut mine_start: u64,
    ) -> Option<Neon2NakaData> {
        let (coordinator_receivers, coordinator_senders) = self
            .coordinator_channels
            .take()
            .expect("Run loop already started, can only start once after initialization.");

        Self::setup_termination_handler(self.should_keep_running.clone(), false);

        let burnchain_result = Self::instantiate_burnchain_state(
            &self.config,
            self.should_keep_running.clone(),
            burnchain_opt,
            coordinator_senders.clone(),
        );

        let mut burnchain = match burnchain_result {
            Ok(burnchain_controller) => burnchain_controller,
            Err(burnchain_error::ShutdownInitiated) => {
                info!("Exiting stacks-node");
                return None;
            }
            Err(e) => {
                error!("Error initializing burnchain: {e}");
                info!("Exiting stacks-node");
                return None;
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
        self.instantiate_pox_watchdog();
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
        let mut node = StacksNode::spawn(self, globals.clone(), relay_recv);
        let liveness_thread = self.spawn_chain_liveness_thread(globals.clone());

        // Wait for all pending sortitions to process
        let mut burnchain_db = burnchain_config
            .open_burnchain_db(true)
            .expect("FATAL: failed to open burnchain DB");
        if !self.config.burnchain.affirmation_overrides.is_empty() {
            let tx = burnchain_db
                .tx_begin()
                .expect("FATAL: failed to begin burnchain DB tx");
            for (reward_cycle, affirmation) in self.config.burnchain.affirmation_overrides.iter() {
                tx.set_override_affirmation_map(*reward_cycle, affirmation.clone()).unwrap_or_else(|_| panic!("FATAL: failed to set affirmation override ({affirmation}) for reward cycle {reward_cycle}"));
            }
            tx.commit()
                .expect("FATAL: failed to commit burnchain DB tx");
        }
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

        // prepare to fetch the first reward cycle!
        debug!("Runloop: Begin main runloop starting a burnchain block {sortition_db_height}");

        let mut last_tenure_sortition_height = 0;

        loop {
            if !globals.keep_running() {
                // The p2p thread relies on the same atomic_bool, it will
                // discontinue its execution after completing its ongoing runloop epoch.
                info!("Terminating p2p process");
                info!("Terminating relayer");
                info!("Terminating chains-coordinator");

                globals.coord().stop_chains_coordinator();
                coordinator_thread_handle.join().unwrap();
                let peer_network = node.join();
                liveness_thread.join().unwrap();

                // Data that will be passed to Nakamoto run loop
                // Only gets transfered on clean shutdown of neon run loop
                let data_to_naka = Neon2NakaData::new(globals, peer_network);

                info!("Exiting stacks-node");
                break Some(data_to_naka);
            }

            let remote_chain_height = burnchain.get_headers_height() - 1;

            // wait until it's okay to process the next reward cycle's sortitions.
            let (ibd, target_burnchain_block_height) = match self.get_pox_watchdog().pox_sync_wait(
                &burnchain_config,
                &burnchain_tip,
                remote_chain_height,
            ) {
                Ok(x) => x,
                Err(e) => {
                    debug!("Runloop: PoX sync wait routine aborted: {e:?}");
                    continue;
                }
            };

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

                        let sortition_id = &block.sortition_id;

                        // Have the node process the new block, that can include, or not, a sortition.
                        node.process_burnchain_state(
                            self.config(),
                            burnchain.sortdb_mut(),
                            sortition_id,
                            ibd,
                        );

                        // Now, tell the relayer to check if it won a sortition during this block,
                        // and, if so, to process and advertize the block.  This is basically a
                        // no-op during boot-up.
                        //
                        // _this will block if the relayer's buffer is full_
                        if !node.relayer_sortition_notify() {
                            // First check if we were supposed to cleanly exit
                            if !globals.keep_running() {
                                // The p2p thread relies on the same atomic_bool, it will
                                // discontinue its execution after completing its ongoing runloop epoch.
                                info!("Terminating p2p process");
                                info!("Terminating relayer");
                                info!("Terminating chains-coordinator");

                                globals.coord().stop_chains_coordinator();
                                coordinator_thread_handle.join().unwrap();
                                let peer_network = node.join();
                                liveness_thread.join().unwrap();

                                // Data that will be passed to Nakamoto run loop
                                // Only gets transfered on clean shutdown of neon run loop
                                let data_to_naka = Neon2NakaData::new(globals, peer_network);

                                info!("Exiting stacks-node");
                                return Some(data_to_naka);
                            }
                            // relayer hung up, exit.
                            error!("Runloop: Block relayer and miner hung up, exiting.");
                            return None;
                        }
                    }

                    debug!("Runloop: enable miner after processing sortitions");
                    signal_mining_ready(globals.get_miner_status());

                    debug!(
                        "Runloop: Synchronized sortitions up to block height {next_sortition_height} from {sortition_db_height} (chain tip height is {burnchain_height})"
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
                    globals.set_start_mining_height_if_zero(sortition_db_height);

                    // at tip, and not downloading. proceed to mine.
                    if last_tenure_sortition_height != sortition_db_height {
                        info!(
                            "Runloop: Synchronized full burnchain up to height {sortition_db_height}. Proceeding to mine blocks"
                        );
                        last_tenure_sortition_height = sortition_db_height;
                    }

                    if !node.relayer_issue_tenure(ibd) {
                        // First check if we were supposed to cleanly exit
                        if !globals.keep_running() {
                            // The p2p thread relies on the same atomic_bool, it will
                            // discontinue its execution after completing its ongoing runloop epoch.
                            info!("Terminating p2p process");
                            info!("Terminating relayer");
                            info!("Terminating chains-coordinator");

                            globals.coord().stop_chains_coordinator();
                            coordinator_thread_handle.join().unwrap();
                            let peer_network = node.join();
                            liveness_thread.join().unwrap();

                            // Data that will be passed to Nakamoto run loop
                            // Only gets transfered on clean shutdown of neon run loop
                            let data_to_naka = Neon2NakaData::new(globals, peer_network);

                            info!("Exiting stacks-node");
                            return Some(data_to_naka);
                        }
                        // relayer hung up, exit.
                        error!("Runloop: Block relayer and miner hung up, exiting.");
                        break None;
                    }
                }
            }
        }
    }
}
