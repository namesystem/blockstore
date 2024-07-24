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
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::Duration;
use std::{fmt, fs, thread};

use stacks::burnchains::Burnchain;
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::coordinator::comm::CoordinatorChannels;
use stacks::core::StacksEpochExtension;
use stacks::net::p2p::PeerNetwork;
use stacks_common::types::{StacksEpoch, StacksEpochId};

use crate::globals::NeonGlobals;
use crate::neon::Counters;
use crate::neon_node::LeaderKeyRegistrationState;
use crate::run_loop::nakamoto::RunLoop as NakaRunLoop;
use crate::run_loop::neon::RunLoop as NeonRunLoop;
use crate::Config;

/// Data which should persist through transition from Neon => Nakamoto run loop
#[derive(Default)]
pub struct Neon2NakaData {
    pub leader_key_registration_state: LeaderKeyRegistrationState,
    pub peer_network: Option<PeerNetwork>,
}

impl Neon2NakaData {
    /// Take needed values from `NeonGlobals` and optionally `PeerNetwork`, consuming them
    pub fn new(globals: NeonGlobals, peer_network: Option<PeerNetwork>) -> Self {
        let key_state = globals
            .leader_key_registration_state
            .lock()
            .unwrap_or_else(|e| {
                // can only happen due to a thread panic in the relayer
                error!("FATAL: leader key registration mutex is poisoned: {e:?}");
                panic!();
            });

        Self {
            leader_key_registration_state: (*key_state).clone(),
            peer_network,
        }
    }
}

const BOOT_THREAD_NAME: &str = "epoch-2/3-boot";

const LOG_SOURCE: &str = "nakamoto-boot";

/// This runloop handles booting to Nakamoto:
/// During epochs [1.0, 2.5], it runs a neon run_loop.
/// Once epoch 3.0 is reached, it stops the neon run_loop
///  and starts nakamoto.
pub struct BootRunLoop {
    config: Config,
    active_loop: InnerLoops,
    coordinator_channels: Arc<Mutex<CoordinatorChannels>>,
}

enum InnerLoops {
    Epoch2(NeonRunLoop),
    Epoch3(NakaRunLoop),
}

impl fmt::Display for InnerLoops {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InnerLoops::Epoch2(_) => write!(f, "{}", StacksEpochId::Epoch20),
            InnerLoops::Epoch3(_) => write!(f, "{}", StacksEpochId::Epoch30),
        }
    }
}

impl BootRunLoop {
    pub fn new(config: Config) -> Result<Self, String> {
        let (coordinator_channels, active_loop) = if !Self::reached_epoch_30_transition(&config)? {
            let neon = NeonRunLoop::new(config.clone());
            (
                neon.get_coordinator_channel().unwrap(),
                InnerLoops::Epoch2(neon),
            )
        } else {
            let naka = NakaRunLoop::new(config.clone(), None, None, None);
            (
                naka.get_coordinator_channel().unwrap(),
                InnerLoops::Epoch3(naka),
            )
        };

        Ok(BootRunLoop {
            config,
            active_loop,
            coordinator_channels: Arc::new(Mutex::new(coordinator_channels)),
        })
    }

    /// Get a mutex-guarded pointer to this run-loops coordinator channels.
    ///  The reason this must be mutex guarded is that the run loop will switch
    ///  from a "neon" coordinator to a "nakamoto" coordinator, and update the
    ///  backing coordinator channel. That way, anyone still holding the Arc<>
    ///  should be able to query the new coordinator channel.
    pub fn coordinator_channels(&self) -> Arc<Mutex<CoordinatorChannels>> {
        self.coordinator_channels.clone()
    }

    /// Get the runtime counters for the inner runloop. The nakamoto
    ///  runloop inherits the counters object from the neon node,
    ///  so no need for another layer of indirection/mutex.
    pub fn counters(&self) -> Counters {
        match &self.active_loop {
            InnerLoops::Epoch2(x) => x.get_counters(),
            InnerLoops::Epoch3(x) => x.get_counters(),
        }
    }

    /// Get the termination switch from the active run loop.
    pub fn get_termination_switch(&self) -> Arc<AtomicBool> {
        match &self.active_loop {
            InnerLoops::Epoch2(x) => x.get_termination_switch(),
            InnerLoops::Epoch3(x) => x.get_termination_switch(),
        }
    }

    /// The main entry point for the run loop. This starts either a 2.x-neon or 3.x-nakamoto
    /// node depending on the current burnchain height.
    pub fn start(&mut self, burnchain_opt: Option<Burnchain>, mine_start: u64) {
        match self.active_loop {
            InnerLoops::Epoch2(_) => return self.start_from_neon(burnchain_opt, mine_start),
            InnerLoops::Epoch3(_) => return self.start_from_naka(burnchain_opt, mine_start),
        }
    }

    fn start_from_naka(&mut self, burnchain_opt: Option<Burnchain>, mine_start: u64) {
        let InnerLoops::Epoch3(ref mut naka_loop) = self.active_loop else {
            panic!(
                "Attempted to start from epoch {} when the latest epoch was {}.",
                StacksEpochId::Epoch30,
                self.active_loop
            );
        };

        naka_loop.start(burnchain_opt, mine_start, None)
    }

    fn start_from_neon(&mut self, burnchain_opt: Option<Burnchain>, mine_start: u64) {
        let InnerLoops::Epoch2(ref mut neon_loop) = self.active_loop else {
            panic!(
                "Attempted to start from epoch {} when the latest epoch was {}.",
                StacksEpochId::Epoch20,
                self.active_loop
            );
        };

        let termination_switch = neon_loop.get_termination_switch();
        let counters = neon_loop.get_counters();

        let boot_thread = Self::spawn_stopper(&self.config, neon_loop).unwrap_or_else(|error| {
            panic!("Failed to spawn {} thread: {:?}", BOOT_THREAD_NAME, error)
        });

        let data_to_naka = neon_loop.start(burnchain_opt.clone(), mine_start);
        let monitoring_thread = neon_loop.take_monitoring_thread();

        // did we exit because of the epoch-3.0 transition, or some other reason?
        let exited_for_transition = boot_thread.join().unwrap_or_else(|error| {
            panic!("Failed to join {} thread: {:?}", BOOT_THREAD_NAME, error)
        });

        if !exited_for_transition {
            info!(#LOG_SOURCE, "Shutting down epoch {} → {} transition thread.", StacksEpochId::Epoch20, StacksEpochId::Epoch30);
            return;
        }

        info!(#LOG_SOURCE, "Reached epoch {} boundary, starting Nakamoto node.", StacksEpochId::Epoch30);
        termination_switch.store(true, Ordering::SeqCst);

        let naka = NakaRunLoop::new(
            self.config.clone(),
            Some(termination_switch),
            Some(counters),
            monitoring_thread,
        );

        let new_coord_channels = naka
            .get_coordinator_channel()
            .expect("A coordinator channel was not found for node.");
        {
            let mut coord_channel = self
                .coordinator_channels
                .lock()
                .expect("Coordinator channel thread panicked while holding the lock.");
            *coord_channel = new_coord_channels;
        }

        self.active_loop = InnerLoops::Epoch3(naka);

        let InnerLoops::Epoch3(ref mut naka_loop) = self.active_loop else {
            panic!(
                "Unexpectedly found epoch {} after setting {} active.",
                StacksEpochId::Epoch20,
                StacksEpochId::Epoch30
            );
        };

        naka_loop.start(burnchain_opt, mine_start, data_to_naka)
    }

    fn spawn_stopper(
        config: &Config,
        neon: &NeonRunLoop,
    ) -> Result<JoinHandle<bool>, std::io::Error> {
        let neon_term_switch = neon.get_termination_switch();
        let config = config.clone();

        thread::Builder::new()
            .name(BOOT_THREAD_NAME.into())
            .spawn(move || {
                loop {
                    let do_transition = Self::reached_epoch_30_transition(&config)
                        .unwrap_or_else(|err| {
                            warn!(#LOG_SOURCE, "Failed to check epoch {} transition: {err:?}. Assuming transition did not occur yet.", StacksEpochId::Epoch30);
                            false
                        });
                    if do_transition {
                        break;
                    }
                    if !neon_term_switch.load(Ordering::SeqCst) {
                        info!(#LOG_SOURCE, "Stop requested. Exiting epoch {} → {} transition thread.", StacksEpochId::Epoch20, StacksEpochId::Epoch30);
                        return false;
                    }
                    thread::sleep(Duration::from_secs(1));
                }
                // if loop exited, do the transition
                info!(#LOG_SOURCE, "Epoch {} boundary reached, stopping {}", StacksEpochId::Epoch30, StacksEpochId::Epoch20);
                neon_term_switch.store(false, Ordering::SeqCst);
                true
            })
    }

    fn reached_epoch_30_transition(config: &Config) -> Result<bool, String> {
        let burn_height = Self::get_burn_height(config)?;

        let epochs = StacksEpoch::get_epochs(
            config.burnchain.get_bitcoin_network().1,
            config.burnchain.epochs.as_ref(),
        );

        let epoch_3 = &epochs[StacksEpoch::find_epoch_by_id(&epochs, StacksEpochId::Epoch30)
            .ok_or(format!("No epoch {} defined.", StacksEpochId::Epoch30))?];

        Ok(u64::from(burn_height) >= epoch_3.start_height - 1)
    }

    fn get_burn_height(config: &Config) -> Result<u32, String> {
        let burnchain = config.get_burnchain();
        let sortdb_path = config.get_burn_db_file_path();

        if let Err(error) = fs::metadata(&sortdb_path) {
            // if the sortition db doesn't exist yet, don't try to open() it, because that creates the
            // db file even if it doesn't instantiate the tables, which breaks connect() logic.
            info!(#LOG_SOURCE, "Failed to open Sortition database while checking current burn height: {error}. Assuming current height is 0."; "db_path" => sortdb_path);
            return Ok(0);
        }

        let sortdb_or_error = SortitionDB::open(&sortdb_path, false, burnchain.pox_constants);

        if let Err(error) = sortdb_or_error {
            info!(#LOG_SOURCE, "Failed to open Sortition database while checking current burn height: {error}. Assuming current height is 0."; "db_path" => sortdb_path, "readwrite" => false);
            return Ok(0);
        };

        let sortdb = sortdb_or_error.unwrap();
        let tip_sn_or_error = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn());

        if let Err(error) = tip_sn_or_error {
            info!(#LOG_SOURCE, "Failed to query Sortition database for current burn height: {error}. Assuming current height is 0."; "db_path" => sortdb_path);
            return Ok(0);
        };

        let block_height = tip_sn_or_error.unwrap().block_height;

        Ok(u32::try_from(block_height).expect(&format!(
            "Burn height {} exceeds the max allowed value of {}",
            block_height,
            u32::MAX
        )))
    }
}
