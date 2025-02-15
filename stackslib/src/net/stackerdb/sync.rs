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

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::mem;

use clarity::vm::types::QualifiedContractIdentifier;
use rand::prelude::SliceRandom;
use rand::{thread_rng, Rng, RngCore};
use stacks_common::types::chainstate::{ConsensusHash, StacksAddress};
use stacks_common::util::get_epoch_time_secs;
use stacks_common::util::hash::Hash160;

use crate::net::chat::ConversationP2P;
use crate::net::connection::ReplyHandleP2P;
use crate::net::db::PeerDB;
use crate::net::neighbors::comms::ToNeighborKey;
use crate::net::neighbors::NeighborComms;
use crate::net::p2p::PeerNetwork;
use crate::net::stackerdb::{
    StackerDBConfig, StackerDBSync, StackerDBSyncResult, StackerDBSyncState, StackerDBs,
};
use crate::net::{
    Error as net_error, NackData, NackErrorCodes, Neighbor, NeighborAddress, NeighborKey,
    StackerDBChunkData, StackerDBChunkInvData, StackerDBGetChunkData, StackerDBGetChunkInvData,
    StackerDBPushChunkData, StacksMessageType,
};

const MAX_CHUNKS_IN_FLIGHT: usize = 6;
const MAX_DB_NEIGHBORS: usize = 32;

impl<NC: NeighborComms> StackerDBSync<NC> {
    pub fn new(
        smart_contract: QualifiedContractIdentifier,
        config: &StackerDBConfig,
        comms: NC,
        stackerdbs: StackerDBs,
    ) -> StackerDBSync<NC> {
        let mut dbsync = StackerDBSync {
            state: StackerDBSyncState::ConnectBegin,
            rc_consensus_hash: None,
            smart_contract_id: smart_contract,
            num_slots: config.num_slots() as usize,
            write_freq: config.write_freq,
            chunk_invs: HashMap::new(),
            chunk_fetch_priorities: vec![],
            chunk_push_priorities: vec![],
            chunk_push_receipts: HashMap::new(),
            next_chunk_fetch_priority: 0,
            next_chunk_push_priority: 0,
            expected_versions: vec![],
            downloaded_chunks: HashMap::new(),
            replicas: HashSet::new(),
            connected_replicas: HashSet::new(),
            comms,
            stackerdbs,
            request_capacity: MAX_CHUNKS_IN_FLIGHT,
            max_neighbors: MAX_DB_NEIGHBORS,
            total_stored: 0,
            total_pushed: 0,
            last_run_ts: 0,
            need_resync: false,
            stale_inv: false,
            stale_neighbors: HashSet::new(),
            num_connections: 0,
            num_attempted_connections: 0,
            rounds: 0,
            push_round: 0,
            last_eviction_time: get_epoch_time_secs(),
        };
        dbsync.reset(None, config);
        dbsync
    }

    /// Find stackerdb replicas and apply filtering rules
    fn find_qualified_replicas(
        &self,
        network: &PeerNetwork,
    ) -> Result<HashSet<NeighborAddress>, net_error> {
        let mut found = HashSet::new();
        let mut min_age =
            get_epoch_time_secs().saturating_sub(network.get_connection_opts().max_neighbor_age);

        let local_naddr = network.get_local_peer().to_neighbor_addr();

        while found.len() < self.max_neighbors {
            let peers_iter = PeerDB::find_stacker_db_replicas(
                network.peerdb_conn(),
                network.get_local_peer().network_id,
                &self.smart_contract_id,
                min_age,
                self.max_neighbors,
            )?
            .into_iter()
            .map(|neighbor| {
                (
                    NeighborAddress::from_neighbor(&neighbor),
                    neighbor.last_contact_time,
                )
            })
            .filter(|(naddr, _)| {
                if naddr.addrbytes.is_anynet() {
                    return false;
                }
                if naddr.public_key_hash == local_naddr.public_key_hash {
                    // don't talk to us by another address
                    return false;
                }
                if !network.get_connection_opts().private_neighbors
                    && naddr.addrbytes.is_in_private_range()
                {
                    return false;
                }
                true
            });

            for (peer, last_contact) in peers_iter {
                found.insert(peer);
                if found.len() >= self.max_neighbors {
                    break;
                }
                min_age = min_age.min(last_contact);
            }

            // search for older neighbors
            if min_age > 1 {
                min_age = 1;
            } else if min_age <= 1 {
                break;
            }
        }
        Ok(found)
    }

    /// Calculate the new set of replicas to contact.
    /// This is the same as the set that was connected on the last sync, plus any
    /// config hints and discovered nodes from the DB.
    fn find_new_replicas(
        &self,
        mut connected_replicas: HashSet<NeighborAddress>,
        network: Option<&PeerNetwork>,
        config: &StackerDBConfig,
    ) -> Result<HashSet<NeighborAddress>, net_error> {
        // keep all connected replicas, and replenish from config hints and the DB as needed
        let mut peers = config.hint_replicas.clone();
        if let Some(network) = network {
            let extra_peers = self.find_qualified_replicas(network)?;
            peers.extend(extra_peers);
        }

        peers.shuffle(&mut thread_rng());

        for peer in peers {
            if connected_replicas.len() >= config.max_neighbors {
                break;
            }
            connected_replicas.insert(peer);
        }
        Ok(connected_replicas)
    }

    /// Reset this state machine, and get the StackerDBSyncResult with newly-obtained chunk data
    /// and newly-learned information about connection statistics
    pub fn reset(
        &mut self,
        network: Option<&PeerNetwork>,
        config: &StackerDBConfig,
    ) -> StackerDBSyncResult {
        debug!(
            "{}: Reset with config {:?}",
            &self.smart_contract_id, config
        );
        let mut chunks = vec![];
        let downloaded_chunks = mem::replace(&mut self.downloaded_chunks, HashMap::new());
        for (_, mut data) in downloaded_chunks.into_iter() {
            chunks.append(&mut data);
        }

        let chunk_invs = mem::replace(&mut self.chunk_invs, HashMap::new());
        let result = StackerDBSyncResult {
            contract_id: self.smart_contract_id.clone(),
            chunk_invs,
            chunks_to_store: chunks,
            stale: std::mem::replace(&mut self.stale_neighbors, HashSet::new()),
            num_connections: self.num_connections,
            num_attempted_connections: self.num_attempted_connections,
        };

        // keep all connected replicas, and replenish from config hints and the DB as needed
        let connected_replicas = mem::replace(&mut self.connected_replicas, HashSet::new());
        let next_connected_replicas =
            if let Ok(new_replicas) = self.find_new_replicas(connected_replicas, network, config) {
                new_replicas
            } else {
                self.replicas.clone()
            };

        self.replicas = next_connected_replicas;

        self.chunk_fetch_priorities.clear();
        self.chunk_push_priorities.clear();
        self.next_chunk_fetch_priority = 0;
        self.next_chunk_push_priority = 0;
        self.chunk_push_receipts.clear();
        self.expected_versions.clear();
        self.downloaded_chunks.clear();

        // reset comms, but keep all connected replicas pinned.
        // Randomly evict one every so often.
        self.comms.reset();
        if let Some(network) = network {
            let mut eviction_index = None;
            if self.last_eviction_time + 60 < get_epoch_time_secs() {
                self.last_eviction_time = get_epoch_time_secs();
                if !self.replicas.is_empty() {
                    eviction_index = Some(thread_rng().gen_range(0..self.replicas.len()));
                }
            }

            let remove_naddr = eviction_index.and_then(|idx| {
                let removed = self.replicas.iter().nth(idx).cloned();
                if let Some(naddr) = removed.as_ref() {
                    debug!(
                        "{:?}: {}: don't reuse connection for replica {:?}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                    );
                }
                removed
            });

            if let Some(naddr) = remove_naddr {
                self.replicas.remove(&naddr);
            }

            // retain the remaining replica connections
            for naddr in self.replicas.iter() {
                if let Some(event_id) = network.get_event_id(&naddr.to_neighbor_key(network)) {
                    self.comms.pin_connection(event_id);
                    debug!(
                        "{:?}: {}: reuse connection for replica {:?} on event {}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        event_id
                    );
                }
            }
        }

        // reload from config
        self.num_slots = config.num_slots() as usize;
        self.write_freq = config.write_freq;

        self.need_resync = false;
        self.stale_inv = false;
        self.last_run_ts = get_epoch_time_secs();

        self.state = StackerDBSyncState::ConnectBegin;
        self.num_connections = 0;
        self.num_attempted_connections = 0;
        self.rounds += 1;
        self.rc_consensus_hash = None;
        result
    }

    /// Get the set of connection IDs in use
    pub fn get_pinned_connections(&self) -> &HashSet<usize> {
        self.comms.get_pinned_connections()
    }

    /// Unpin and remove a connected replica by naddr
    pub fn unpin_connected_replica(&mut self, network: &PeerNetwork, naddr: &NeighborAddress) {
        let nk = naddr.to_neighbor_key(network);
        if let Some(event_id) = network.get_event_id(&nk) {
            self.comms.unpin_connection(event_id);
        }
        self.connected_replicas.remove(naddr);
    }

    /// Make a chunk inv request
    pub fn make_getchunkinv(&self, rc_consensus_hash: &ConsensusHash) -> StacksMessageType {
        StacksMessageType::StackerDBGetChunkInv(StackerDBGetChunkInvData {
            contract_id: self.smart_contract_id.clone(),
            rc_consensus_hash: rc_consensus_hash.clone(),
        })
    }

    /// Given the downloaded set of chunk inventories, identify:
    /// * which chunks we need to fetch, because they're newer than ours.
    /// * what order to fetch chunks in, in rarest-first order
    /// Returns a list of (chunk requests, list of neighbors that can service them), which is
    /// ordered from rarest chunk to most-common chunk.
    pub fn make_chunk_request_schedule(
        &self,
        network: &PeerNetwork,
        local_slot_versions_opt: Option<Vec<u32>>,
    ) -> Result<Vec<(StackerDBGetChunkData, Vec<NeighborAddress>)>, net_error> {
        let rc_consensus_hash = network.get_chain_view().rc_consensus_hash.clone();
        let local_slot_versions = if let Some(local_slot_versions) = local_slot_versions_opt {
            local_slot_versions
        } else {
            self.stackerdbs.get_slot_versions(&self.smart_contract_id)?
        };

        let local_write_timestamps = self
            .stackerdbs
            .get_slot_write_timestamps(&self.smart_contract_id)?;

        if local_slot_versions.len() != local_write_timestamps.len() {
            let msg = format!("{}: Local slot versions ({}) out of sync with DB slot versions ({}); abandoning sync and trying again", &self.smart_contract_id, local_slot_versions.len(), local_write_timestamps.len());
            warn!("{}", &msg);
            return Err(net_error::Transient(msg));
        }

        let mut need_chunks: HashMap<usize, (StackerDBGetChunkData, Vec<NeighborAddress>)> =
            HashMap::new();
        let now = get_epoch_time_secs();

        // who has data we need?
        for (i, local_version) in local_slot_versions.iter().enumerate() {
            let write_ts = local_write_timestamps[i];
            if self.write_freq > 0 && write_ts + self.write_freq > now {
                debug!(
                    "{:?}: {}: Chunk {} was written too frequently ({} + {} > {}) in {}, so will not fetch chunk",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    i,
                    write_ts,
                    self.write_freq,
                    now,
                    &self.smart_contract_id,
                );
                continue;
            }

            for (naddr, chunk_inv) in self.chunk_invs.iter() {
                if chunk_inv.slot_versions.len() != local_slot_versions.len() {
                    // remote peer and our DB are out of sync, so just skip this
                    continue;
                }

                if *local_version >= chunk_inv.slot_versions[i] {
                    // remote peer has same view as local peer, or stale
                    continue;
                }

                let (request, available) = if let Some(x) = need_chunks.get_mut(&i) {
                    // someone has this chunk already
                    x
                } else {
                    // haven't seen anyone with this data yet.
                    // Add a record for it
                    need_chunks.insert(
                        i,
                        (
                            StackerDBGetChunkData {
                                contract_id: self.smart_contract_id.clone(),
                                rc_consensus_hash,
                                slot_id: i as u32,
                                slot_version: chunk_inv.slot_versions[i],
                            },
                            vec![naddr.clone()],
                        ),
                    );
                    continue;
                };

                match request.slot_version.cmp(&chunk_inv.slot_versions[i]) {
                    Ordering::Less => {
                        // this peer has a newer view
                        available.clear();
                        available.push(naddr.clone());
                        *request = StackerDBGetChunkData {
                            contract_id: self.smart_contract_id.clone(),
                            rc_consensus_hash,
                            slot_id: i as u32,
                            slot_version: chunk_inv.slot_versions[i],
                        };
                    }
                    Ordering::Equal => {
                        // this peer has the same view as a prior peer.
                        // just track how many times we see this
                        available.push(naddr.clone());
                    }
                    Ordering::Greater => {}
                };
            }
        }

        // prioritize requests by rarest-chunk-first order, but choose neighbors in random order
        let mut schedule: Vec<_> = need_chunks
            .into_iter()
            .map(|(_, (stackerdb_getchunkdata, mut neighbors))| {
                neighbors.shuffle(&mut thread_rng());
                (stackerdb_getchunkdata, neighbors)
            })
            .collect();

        schedule.sort_by(|item_1, item_2| item_1.1.len().cmp(&item_2.1.len()));
        schedule.reverse();

        debug!(
            "{:?}: {}: Will request up to {} chunks. Schedule: {:?}",
            network.get_local_peer(),
            &self.smart_contract_id,
            &schedule.len(),
            &schedule
        );
        Ok(schedule)
    }

    /// Given the downloaded set of chunk inventories, identify:
    /// * which chunks we need to push, because we have them and the neighbor does not
    /// * what order to push them in, in rarest-first order
    pub fn make_chunk_push_schedule(
        &self,
        network: &PeerNetwork,
    ) -> Result<Vec<(StackerDBPushChunkData, Vec<NeighborAddress>)>, net_error> {
        let rc_consensus_hash = network.get_chain_view().rc_consensus_hash.clone();
        let local_slot_versions = self.stackerdbs.get_slot_versions(&self.smart_contract_id)?;

        let mut need_chunks: HashMap<usize, (StackerDBPushChunkData, Vec<NeighborAddress>)> =
            HashMap::new();

        // who needs data we can serve?
        for (i, local_version) in local_slot_versions.iter().enumerate() {
            let mut local_chunk = None;
            for (naddr, chunk_inv) in self.chunk_invs.iter() {
                if chunk_inv.slot_versions.len() != local_slot_versions.len() {
                    // remote peer and our DB are out of sync, so just skip this
                    continue;
                }

                if *local_version <= chunk_inv.slot_versions[i] {
                    // remote peer has same or newer view than local peer
                    continue;
                }

                if local_chunk.is_none() {
                    let chunk_data = if let Some(chunk_data) = self.stackerdbs.get_chunk(
                        &self.smart_contract_id,
                        i as u32,
                        *local_version,
                    )? {
                        chunk_data
                    } else {
                        // we don't have this chunk
                        break;
                    };
                    local_chunk = Some(StackerDBPushChunkData {
                        contract_id: self.smart_contract_id.clone(),
                        rc_consensus_hash: rc_consensus_hash.clone(),
                        chunk_data,
                    });
                }

                let our_chunk = if let Some(chunk) = local_chunk.as_ref() {
                    chunk
                } else {
                    // we don't have this chunk
                    break;
                };

                // replicate with probability 1/num-outbound-replicas
                let do_replicate = if chunk_inv.num_outbound_replicas == 0 {
                    true
                } else {
                    thread_rng().gen::<u32>() % chunk_inv.num_outbound_replicas == 0
                };

                debug!(
                    "{:?}: {}: Can push chunk StackerDBChunk(id={},ver={}) to {}. Replicate? {}",
                    &network.get_local_peer(),
                    &self.smart_contract_id,
                    our_chunk.chunk_data.slot_id,
                    our_chunk.chunk_data.slot_version,
                    &naddr,
                    do_replicate
                );

                if !do_replicate {
                    continue;
                }

                if let Some((_, receivers)) = need_chunks.get_mut(&i) {
                    // someone needs this chunk already
                    receivers.push(naddr.clone());
                } else {
                    // haven't seen anyone that needs this data yet.
                    // Add a record for it.
                    need_chunks.insert(i, (our_chunk.clone(), vec![naddr.clone()]));
                };
            }
        }

        // prioritize requests by rarest-chunk-first order.
        // no need to randomize; we'll pick recipients at random
        let mut schedule: Vec<_> = need_chunks
            .into_iter()
            .map(|(_, (stackerdb_chunkdata, neighbors))| (stackerdb_chunkdata, neighbors))
            .collect();

        schedule.sort_by(|item_1, item_2| item_1.1.len().cmp(&item_2.1.len()));
        debug!(
            "{:?}: {}: Will push up to {} chunks",
            network.get_local_peer(),
            &self.smart_contract_id,
            &schedule.len(),
        );
        Ok(schedule)
    }

    /// Validate a downloaded chunk
    pub fn validate_downloaded_chunk(
        &self,
        network: &PeerNetwork,
        config: &StackerDBConfig,
        data: &StackerDBChunkData,
    ) -> Result<bool, net_error> {
        // validate -- must be a valid chunk
        if !network.validate_received_chunk(
            &self.smart_contract_id,
            config,
            data,
            &self.expected_versions,
        )? {
            return Ok(false);
        }

        // no need to validate the timestamp, because we already skipped requesting it if it was
        // written too recently.

        Ok(true)
    }

    /// Store a downloaded chunk to RAM, and update bookkeeping
    pub fn add_downloaded_chunk(&mut self, naddr: NeighborAddress, data: StackerDBChunkData) {
        let slot_id = data.slot_id;
        let _slot_version = data.slot_version;

        if let Some(data_list) = self.downloaded_chunks.get_mut(&naddr) {
            data_list.push(data);
        } else {
            self.downloaded_chunks.insert(naddr.clone(), vec![data]);
        }

        self.chunk_fetch_priorities
            .retain(|(chunk, ..)| chunk.slot_id != slot_id);

        if !self.chunk_fetch_priorities.is_empty() {
            let next_chunk_fetch_priority =
                self.next_chunk_fetch_priority % self.chunk_fetch_priorities.len();
            self.next_chunk_fetch_priority = next_chunk_fetch_priority;
        }

        self.total_stored += 1;
    }

    /// Update bookkeeping about which chunks we have pushed.
    /// Stores the new chunk inventory to RAM.
    /// Returns true if the inventory changed (indicating that we need to resync)
    /// Returns false otherwise
    pub fn add_pushed_chunk(
        &mut self,
        _network: &PeerNetwork,
        naddr: NeighborAddress,
        new_inv: StackerDBChunkInvData,
        slot_id: u32,
    ) -> bool {
        // safety (should already be checked) -- don't accept if the size is wrong
        if new_inv.slot_versions.len() != self.num_slots {
            return false;
        }

        let need_resync = if let Some(old_inv) = self.chunk_invs.get(&naddr) {
            let mut resync = false;
            for (old_slot_id, old_version) in old_inv.slot_versions.iter().enumerate() {
                if *old_version < new_inv.slot_versions[old_slot_id] {
                    // remote peer indicated that it has a newer version of this chunk.
                    debug!(
                        "{:?}: {}: peer {:?} has a newer version of slot {} ({} < {})",
                        _network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        old_slot_id,
                        old_version,
                        new_inv.slot_versions[old_slot_id],
                    );
                    resync = true;
                    break;
                }
            }
            resync
        } else {
            false
        };

        self.chunk_invs.insert(naddr, new_inv);

        self.chunk_push_priorities
            .retain(|(chunk, ..)| chunk.chunk_data.slot_id != slot_id);

        if !self.chunk_push_priorities.is_empty() {
            let next_chunk_push_priority =
                self.next_chunk_push_priority % self.chunk_push_priorities.len();
            self.next_chunk_push_priority = next_chunk_push_priority;
        }

        self.total_pushed += 1;
        need_resync
    }

    /// Ask inbound neighbors who replicate this DB for their chunk inventories.
    /// Don't send them a message if they're also outbound.
    /// Logs errors but does not return them.
    fn send_getchunkinv_to_inbound_neighbors(
        &mut self,
        network: &mut PeerNetwork,
        already_sent: &[NeighborAddress],
    ) {
        let sent_naddr_set: HashSet<_> = already_sent.iter().collect();
        let mut to_send = vec![];
        for event_id in network.iter_peer_event_ids() {
            let convo = if let Some(c) = network.get_p2p_convo(*event_id) {
                c
            } else {
                continue;
            };

            // only want inbound peers that replicate this DB
            if convo.is_outbound() {
                continue;
            }
            if !convo.replicates_stackerdb(&self.smart_contract_id) {
                continue;
            }

            let naddr = convo.to_neighbor_address();
            if sent_naddr_set.contains(&naddr) {
                continue;
            }

            let has_reciprocal_outbound = network
                .get_pubkey_events(&naddr.public_key_hash)
                .iter()
                .find(|event_id| {
                    if let Some(convo) = network.get_p2p_convo(**event_id) {
                        if !convo.is_outbound() {
                            return false;
                        }
                        let other_naddr = convo.to_neighbor_address();
                        if sent_naddr_set.contains(&other_naddr) {
                            return true;
                        }
                    }
                    return false;
                })
                .is_some();

            if has_reciprocal_outbound {
                // this inbound neighbor is also connected to us as an outbound neighbor, and we
                // already sent it a getchunkinv request
                continue;
            }

            let chunks_req = self.make_getchunkinv(&network.get_chain_view().rc_consensus_hash);
            to_send.push((naddr, chunks_req));
        }

        for (naddr, chunks_req) in to_send.into_iter() {
            debug!("{:?}: {}: send_getchunksinv_to_inbound_neighbors: Send StackerDBGetChunkInv at {} to inbound {:?}", network.get_local_peer(), &self.smart_contract_id, &network.get_chain_view().rc_consensus_hash, &naddr);
            if let Err(_e) = self.comms.neighbor_send(network, &naddr, chunks_req) {
                info!(
                    "{:?}: {}: Failed to send StackerDBGetChunkInv to inbound {:?}: {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    &naddr,
                    &_e
                );
            }
        }
    }

    /// Establish sessions with remote replicas.
    /// We might not be connected to any yet.
    /// Clears self.replicas, and fills in self.connected_replicas with already-connected neighbors
    /// Returns Ok(true) if we can proceed to sync
    /// Returns Ok(false) if we should try this again
    /// Returns Err(NoSuchNeighbor) if we don't have anyone to talk to
    /// Returns Err(..) on DB query error
    pub fn connect_begin(&mut self, network: &mut PeerNetwork) -> Result<bool, net_error> {
        if self.replicas.is_empty() {
            // find some from the peer DB
            let replicas = self.find_qualified_replicas(network)?;
            self.replicas = replicas;
        }
        debug!(
            "{:?}: {}: connect_begin: establish StackerDB sessions to {} neighbors (out of {} p2p peers)",
            network.get_local_peer(),
            &self.smart_contract_id,
            self.replicas.len(),
            network.get_num_p2p_convos();
            "replicas" => ?self.replicas
        );
        if self.replicas.is_empty() {
            // nothing to do
            return Err(net_error::NoSuchNeighbor);
        }

        let naddrs = mem::replace(&mut self.replicas, HashSet::new());
        for naddr in naddrs.into_iter() {
            if self.comms.is_neighbor_connecting(network, &naddr) {
                debug!(
                    "{:?}: {}: connect_begin: already connecting to StackerDB peer {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    &naddr
                );
                self.replicas.insert(naddr);
                continue;
            }
            if self.comms.has_neighbor_session(network, &naddr) {
                debug!(
                    "{:?}: {}: connect_begin: already connected to StackerDB peer {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    &naddr
                );
                self.connected_replicas.insert(naddr);
                continue;
            }

            debug!(
                "{:?}: {}: connect_begin: Send Handshake to StackerDB peer {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &naddr
            );
            match self.comms.neighbor_session_begin(network, &naddr) {
                Ok(true) => {
                    // connected!
                    debug!(
                        "{:?}: {}: connect_begin: connected to StackerDB peer {:?}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr
                    );
                    self.num_attempted_connections += 1;
                    self.num_connections += 1;
                    self.connected_replicas.insert(naddr);
                }
                Ok(false) => {
                    // need to retry
                    self.num_attempted_connections += 1;
                    self.replicas.insert(naddr);
                }
                Err(_e) => {
                    debug!(
                        "{:?}: {}: Failed to begin session with {:?}: {:?}",
                        &network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        &_e
                    );
                }
            }
        }
        Ok(!self.connected_replicas.is_empty())
    }

    /// Finish up connecting to our replicas.
    /// Fills in self.connected_replicas based on receipt of a handshake accept.
    /// Returns true if we've received all pending messages
    /// Returns false otherwise
    pub fn connect_try_finish(&mut self, network: &mut PeerNetwork) -> Result<bool, net_error> {
        for (naddr, message) in self.comms.collect_replies(network).into_iter() {
            let data = match message.payload {
                StacksMessageType::StackerDBHandshakeAccept(_, db_data) => {
                    if network.get_chain_view().rc_consensus_hash != db_data.rc_consensus_hash {
                        // stale or inconsistent view. Do not proceed
                        debug!(
                            "{:?}: {}: remote peer {:?} has stale view ({} != {})",
                            network.get_local_peer(),
                            &self.smart_contract_id,
                            &naddr,
                            &network.get_chain_view().rc_consensus_hash,
                            &db_data.rc_consensus_hash
                        );
                        // don't unpin, since it's usually transient
                        self.connected_replicas.remove(&naddr);
                        continue;
                    }
                    db_data
                }
                StacksMessageType::Nack(data) => {
                    debug!(
                        "{:?}: {}: remote peer {:?} NACK'ed our StackerDBHandshake with code {}",
                        &network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        data.error_code
                    );
                    if data.error_code == NackErrorCodes::StaleView
                        || data.error_code == NackErrorCodes::FutureView
                    {
                        self.connected_replicas.remove(&naddr);
                        self.stale_neighbors.insert(naddr);
                    } else {
                        self.unpin_connected_replica(network, &naddr);
                    }
                    continue;
                }
                x => {
                    info!(
                        "{:?}: {}: Received unexpected message {:?}",
                        &network.get_local_peer(),
                        &self.smart_contract_id,
                        &x
                    );
                    continue;
                }
            };

            if data
                .smart_contracts
                .iter()
                .find(|db_id| *db_id == &self.smart_contract_id)
                .is_none()
            {
                debug!(
                    "{:?}: {}: remote peer does not replicate",
                    network.get_local_peer(),
                    &self.smart_contract_id
                );

                // disconnect
                self.unpin_connected_replica(network, &naddr);
                continue;
            }

            debug!(
                "{:?}: {}: connect_try_finish: Received StackerDBHandshakeAccept from {:?} for {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &naddr,
                &data
            );

            // this neighbor is good
            self.connected_replicas.insert(naddr);
        }

        if self.comms.count_inflight() > 0 {
            // still blocked
            return Ok(false);
        }

        if self.connected_replicas.is_empty() {
            // no one to talk to
            debug!(
                "{:?}: {}: connect_try_finish: no valid replicas",
                &self.smart_contract_id,
                network.get_local_peer()
            );
            return Err(net_error::PeerNotConnected);
        }

        Ok(true)
    }

    /// Ask each replica for its chunk inventories.
    /// Also ask each inbound neighbor.
    /// Clears self.connected_replicas.
    /// StackerDBGetChunksInv
    /// Always succeeds; does not block.
    pub fn getchunksinv_begin(&mut self, network: &mut PeerNetwork) {
        let naddrs = mem::replace(&mut self.connected_replicas, HashSet::new());
        let mut already_sent = vec![];
        debug!(
            "{:?}: {}: getchunksinv_begin: Send StackerDBGetChunksInv to {} replicas",
            network.get_local_peer(),
            &self.smart_contract_id,
            naddrs.len();
            "connected_replicas" => ?naddrs,
        );
        for naddr in naddrs.into_iter() {
            debug!(
                "{:?}: {}: getchunksinv_begin: Send StackerDBGetChunksInv at {} to {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &network.get_chain_view().rc_consensus_hash,
                &naddr,
            );
            let chunks_req = self.make_getchunkinv(&network.get_chain_view().rc_consensus_hash);
            if let Err(e) = self.comms.neighbor_send(network, &naddr, chunks_req) {
                debug!(
                    "{:?}: {}: failed to send StackerDBGetChunkInv to {:?}: {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    &naddr,
                    &e
                );
                continue;
            }
            already_sent.push(naddr);
        }
        self.send_getchunkinv_to_inbound_neighbors(network, &already_sent);
    }

    /// Collect each chunk inventory request.
    /// Restores self.connected_replicas based on messages received.
    /// Return Ok(true) if we've received all pending messages
    /// Return Ok(false) if not
    pub fn getchunksinv_try_finish(
        &mut self,
        network: &mut PeerNetwork,
    ) -> Result<bool, net_error> {
        for (naddr, message) in self.comms.collect_replies(network).into_iter() {
            let chunk_inv_opt = match message.payload {
                StacksMessageType::StackerDBChunkInv(data) => {
                    if data.slot_versions.len() != self.num_slots {
                        info!("{:?}: {}: Received malformed StackerDBChunkInv from {:?}: expected {} chunks, got {}", network.get_local_peer(), &self.smart_contract_id, &naddr, self.num_slots, data.slot_versions.len());
                        None
                    } else {
                        Some(data)
                    }
                }
                StacksMessageType::Nack(data) => {
                    debug!(
                        "{:?}: {}: remote peer {:?} NACK'ed our StackerDBGetChunksInv with code {}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        data.error_code
                    );
                    if data.error_code == NackErrorCodes::StaleView
                        || data.error_code == NackErrorCodes::FutureView
                    {
                        self.connected_replicas.remove(&naddr);
                        self.stale_neighbors.insert(naddr);
                    } else {
                        self.unpin_connected_replica(network, &naddr);
                    }
                    continue;
                }
                x => {
                    info!(
                        "{:?}: {}: Received unexpected message {:?}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &x
                    );
                    self.unpin_connected_replica(network, &naddr);
                    continue;
                }
            };
            debug!(
                "{:?}: {}: getchunksinv_try_finish: Received StackerDBChunkInv from {:?}: {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &naddr,
                &chunk_inv_opt
            );

            if let Some(chunk_inv) = chunk_inv_opt {
                self.chunk_invs.insert(naddr.clone(), chunk_inv);
                self.connected_replicas.insert(naddr);
            }
        }
        if self.comms.count_inflight() > 0 {
            // not done yet, so blocked
            return Ok(false);
        }

        // got everything. Calculate download priority
        let priorities = self.make_chunk_request_schedule(network, None)?;
        let expected_versions = self.stackerdbs.get_slot_versions(&self.smart_contract_id)?;

        self.chunk_fetch_priorities = priorities;
        self.expected_versions = expected_versions;
        Ok(true)
    }

    /// Ask each prioritized replica for some chunks we need.
    /// Return Ok(true) if we processed all requested chunks
    /// Return Ok(false) if there are still some requests to make
    pub fn getchunks_begin(&mut self, network: &mut PeerNetwork) -> Result<bool, net_error> {
        if self.chunk_fetch_priorities.is_empty() {
            // done
            debug!(
                "{:?}: {}: getchunks_begin: no chunks prioritized",
                network.get_local_peer(),
                &self.smart_contract_id
            );
            return Ok(true);
        }

        let mut cur_priority = self.next_chunk_fetch_priority % self.chunk_fetch_priorities.len();

        debug!(
            "{:?}: {}: getchunks_begin: Issue up to {} StackerDBGetChunk requests",
            &network.get_local_peer(),
            &self.smart_contract_id,
            self.request_capacity;
            "chunk_fetch_priorities" => ?self.chunk_fetch_priorities,
        );

        let mut requested = 0;
        let mut unpin = HashSet::new();

        // fill up our comms with $capacity requests
        for _i in 0..self.request_capacity {
            if self.comms.count_inflight() >= self.request_capacity {
                break;
            }

            let chunk_request = self.chunk_fetch_priorities[cur_priority].0.clone();
            let selected_neighbor_opt = self.chunk_fetch_priorities[cur_priority]
                .1
                .iter()
                .enumerate()
                .find(|(_i, naddr)| !self.comms.has_inflight(naddr));

            let (idx, selected_neighbor) = if let Some(x) = selected_neighbor_opt {
                x
            } else {
                continue;
            };

            debug!(
                "{:?}: {}: getchunks_begin: Send StackerDBGetChunk(id={},ver={}) at {} to {}",
                &network.get_local_peer(),
                &self.smart_contract_id,
                chunk_request.slot_id,
                chunk_request.slot_version,
                &chunk_request.rc_consensus_hash,
                &selected_neighbor
            );

            if let Err(e) = self.comms.neighbor_send(
                network,
                selected_neighbor,
                StacksMessageType::StackerDBGetChunk(chunk_request.clone()),
            ) {
                info!(
                    "{:?}: {} Failed to request chunk {} from {:?}: {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    chunk_request.slot_id,
                    selected_neighbor,
                    &e
                );
                unpin.insert(selected_neighbor.clone());
                continue;
            }

            requested += 1;

            // don't ask this neighbor again
            self.chunk_fetch_priorities[cur_priority].1.remove(idx);

            // next-prioritized chunk
            cur_priority = (cur_priority + 1) % self.chunk_fetch_priorities.len();
        }
        let _ = unpin
            .into_iter()
            .map(|naddr| self.unpin_connected_replica(network, &naddr));

        if requested == 0 && self.comms.count_inflight() == 0 {
            return Err(net_error::PeerNotConnected);
        }

        self.next_chunk_fetch_priority = cur_priority;

        Ok(self.chunk_fetch_priorities.is_empty())
    }

    /// Collect chunk replies from neighbors
    /// Returns Ok(true) if all inflight messages have been received (or dealt with)
    /// Returns Ok(false) otherwise
    pub fn getchunks_try_finish(
        &mut self,
        network: &mut PeerNetwork,
        config: &StackerDBConfig,
    ) -> Result<bool, net_error> {
        for (naddr, message) in self.comms.collect_replies(network).into_iter() {
            let data = match message.payload {
                StacksMessageType::StackerDBChunk(data) => data,
                StacksMessageType::Nack(data) => {
                    debug!(
                        "{:?}: {}: remote peer {:?} NACK'ed our StackerDBGetChunk with code {}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        data.error_code
                    );
                    if data.error_code == NackErrorCodes::StaleView
                        || data.error_code == NackErrorCodes::FutureView
                    {
                        self.stale_neighbors.insert(naddr);
                    } else if data.error_code == NackErrorCodes::StaleVersion {
                        // try again immediately, without throttling
                        self.stale_inv = true;
                    }
                    continue;
                }
                x => {
                    info!(
                        "{:?}: {}: Received unexpected message {:?}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &x
                    );
                    self.unpin_connected_replica(network, &naddr);
                    continue;
                }
            };

            // validate
            if !self.validate_downloaded_chunk(network, config, &data)? {
                info!(
                    "{:?}: {}: Remote neighbor {:?} served an invalid chunk for ID {}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    &naddr,
                    data.slot_id
                );
                self.unpin_connected_replica(network, &naddr);
                continue;
            }

            // update bookkeeping
            debug!(
                "{:?}: {}, getchunks_try_finish: Received StackerDBChunk from {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &naddr
            );
            self.add_downloaded_chunk(naddr, data);
        }

        Ok(self.comms.count_inflight() == 0)
    }

    /// Push out chunks to peers
    /// Returns true if there are no more chunks to push.
    /// Returns false if there are
    pub fn pushchunks_begin(&mut self, network: &mut PeerNetwork) -> Result<bool, net_error> {
        if self.chunk_push_priorities.is_empty() && self.push_round != self.rounds {
            // only do this once per round
            let priorities = self.make_chunk_push_schedule(network)?;
            self.chunk_push_priorities = priorities;
            self.push_round = self.rounds;
        }
        if self.chunk_push_priorities.is_empty() {
            // done
            debug!(
                "{:?}:{}: pushchunks_begin: no chunks prioritized",
                network.get_local_peer(),
                &self.smart_contract_id
            );
            return Ok(true);
        }

        let mut cur_priority = self.next_chunk_push_priority % self.chunk_push_priorities.len();

        debug!(
            "{:?}: {}: pushchunks_begin: Send up to {} StackerDBChunk pushes",
            &network.get_local_peer(),
            &self.smart_contract_id,
            self.chunk_push_priorities.len();
            "chunk_push_priorities" => ?self.chunk_push_priorities
        );

        // fill up our comms with $capacity requests
        let mut num_sent = 0;
        for _i in 0..self.chunk_push_priorities.len() {
            if self.comms.count_inflight() >= self.request_capacity {
                break;
            }

            let chunk_push = self.chunk_push_priorities[cur_priority].0.clone();
            // try the first neighbor in the chunk_push_priorities list
            let selected_neighbor_opt = self.chunk_push_priorities[cur_priority]
                .1
                .first()
                .map(|neighbor| (0, neighbor));

            let Some((idx, selected_neighbor)) = selected_neighbor_opt else {
                debug!("{:?}: {}: pushchunks_begin: no available neighbor to send StackerDBChunk(id={},ver={}) to",
                    &network.get_local_peer(),
                    &self.smart_contract_id,
                    chunk_push.chunk_data.slot_id,
                    chunk_push.chunk_data.slot_version,
                );

                // next-prioritized chunk
                cur_priority = (cur_priority + 1) % self.chunk_push_priorities.len();
                continue;
            };

            debug!(
                "{:?}: {}: pushchunks_begin: Send StackerDBChunk(id={},ver={}) at {} to {}",
                &network.get_local_peer(),
                &self.smart_contract_id,
                chunk_push.chunk_data.slot_id,
                chunk_push.chunk_data.slot_version,
                &chunk_push.rc_consensus_hash,
                &selected_neighbor
            );

            let slot_id = chunk_push.chunk_data.slot_id;
            let slot_version = chunk_push.chunk_data.slot_version;
            if let Err(e) = self.comms.neighbor_send(
                network,
                selected_neighbor,
                StacksMessageType::StackerDBPushChunk(chunk_push),
            ) {
                info!(
                    "{:?}: {}: Failed to send chunk {} from {:?}: {:?}",
                    network.get_local_peer(),
                    &self.smart_contract_id,
                    slot_id,
                    selected_neighbor,
                    &e
                );
                continue;
            }

            // record what we just sent
            self.chunk_push_receipts
                .insert(selected_neighbor.clone(), (slot_id, slot_version));

            // don't send to this neighbor again
            self.chunk_push_priorities[cur_priority].1.remove(idx);

            // next-prioritized chunk
            cur_priority = (cur_priority + 1) % self.chunk_push_priorities.len();

            num_sent += 1;
            if num_sent > self.request_capacity {
                break;
            }
        }
        self.next_chunk_push_priority = cur_priority;
        Ok(self
            .chunk_push_priorities
            .iter()
            .fold(0usize, |acc, (_chunk, num_naddrs)| {
                acc.saturating_add(num_naddrs.len())
            })
            == 0)
    }

    /// Collect push-chunk replies from neighbors.
    /// If a remote neighbor replies with a chunk-inv for a pushed chunk which contains newer data
    /// than we have, then set `self.need_resync` to true.
    /// Returns true if all inflight messages have been received (or dealt with)
    /// Returns false otherwise
    pub fn pushchunks_try_finish(&mut self, network: &mut PeerNetwork) -> bool {
        for (naddr, message) in self.comms.collect_replies(network).into_iter() {
            let new_chunk_inv = match message.payload {
                StacksMessageType::StackerDBChunkInv(data) => data,
                StacksMessageType::Nack(data) => {
                    debug!(
                        "{:?}: {}: remote peer {:?} NACK'ed our StackerDBChunk with code {}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &naddr,
                        data.error_code
                    );
                    if data.error_code == NackErrorCodes::StaleView
                        || data.error_code == NackErrorCodes::FutureView
                    {
                        self.stale_neighbors.insert(naddr);
                    }
                    continue;
                }
                x => {
                    info!(
                        "{:?}: {}: Received unexpected message {:?}",
                        network.get_local_peer(),
                        &self.smart_contract_id,
                        &x
                    );
                    continue;
                }
            };

            // must be well-formed
            if new_chunk_inv.slot_versions.len() != self.num_slots {
                info!("{:?}: {}: Received malformed StackerDBChunkInv from {:?}: expected {} chunks, got {}", network.get_local_peer(), &self.smart_contract_id, &naddr, self.num_slots, new_chunk_inv.slot_versions.len());
                continue;
            }

            // update bookkeeping
            debug!(
                "{:?}: {}: pushchunks_try_finish: Received StackerDBChunkInv from {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &naddr
            );

            if let Some((slot_id, _)) = self.chunk_push_receipts.get(&naddr) {
                self.need_resync = self.need_resync
                    || self.add_pushed_chunk(network, naddr, new_chunk_inv, *slot_id);
            }
        }

        let inflight = self.comms.count_inflight();
        debug!(
            "{:?}: {}: inflight messages: {:?}",
            network.get_local_peer(),
            &self.smart_contract_id,
            inflight
        );
        inflight == 0
    }

    /// Recalculate the download schedule based on chunkinvs received on push
    pub fn recalculate_chunk_request_schedule(
        &mut self,
        network: &PeerNetwork,
    ) -> Result<(), net_error> {
        // figure out the new expected versions
        let mut expected_versions = vec![0u32; self.num_slots];
        for (_, chunk_inv) in self.chunk_invs.iter() {
            for (slot_id, slot_version) in chunk_inv.slot_versions.iter().enumerate() {
                expected_versions[slot_id] = (*slot_version).max(expected_versions[slot_id]);
            }
        }

        let priorities =
            self.make_chunk_request_schedule(network, Some(expected_versions.clone()))?;

        self.chunk_fetch_priorities = priorities;
        self.expected_versions = expected_versions;
        Ok(())
    }

    /// Forcibly wake up the state machine if it is throttled
    pub fn wakeup(&mut self) {
        debug!("wake up StackerDB sync for {}", &self.smart_contract_id);
        self.last_run_ts = 0;
    }

    /// Run the state machine.
    /// If we run to completion, then reset and return the sync result.
    /// Otherwise, if there's still more work to do, then return None
    pub fn run(
        &mut self,
        network: &mut PeerNetwork,
        config: &StackerDBConfig,
    ) -> Result<Option<StackerDBSyncResult>, net_error> {
        if network.get_connection_opts().disable_stackerdb_sync {
            test_debug!(
                "{:?}: stacker DB sync is disabled",
                network.get_local_peer()
            );
            return Ok(None);
        }

        // make sure we have an up-to-date chain view.
        // If not, then abort and immediately retry the sync (since any queued messages we have are
        // likely gonna fail)
        if let Some(rc_consensus_hash) = self.rc_consensus_hash.as_ref() {
            if network.get_chain_view().rc_consensus_hash != *rc_consensus_hash {
                debug!("{:?}: {}: Resetting and restarting running StackerDB sync due to chain view change", network.get_local_peer(), &self.smart_contract_id);
                let result = self.reset(Some(network), config);
                self.state = StackerDBSyncState::ConnectBegin;
                self.rc_consensus_hash = Some(network.get_chain_view().rc_consensus_hash.clone());
                self.wakeup();
                return Ok(Some(result));
            }
        } else {
            self.rc_consensus_hash = Some(network.get_chain_view().rc_consensus_hash.clone());
        }

        // throttle to write_freq
        if self.last_run_ts + config.write_freq.max(1) > get_epoch_time_secs() {
            debug!(
                "{:?}: {}: stacker DB sync is throttled until {}",
                network.get_local_peer(),
                &self.smart_contract_id,
                self.last_run_ts + config.write_freq
            );
            return Ok(None);
        }

        loop {
            debug!(
                "{:?}: {}: stacker DB sync state is {:?}",
                network.get_local_peer(),
                &self.smart_contract_id,
                &self.state
            );

            let mut blocked = true;
            match self.state {
                StackerDBSyncState::ConnectBegin => {
                    let done = match self.connect_begin(network) {
                        Ok(done) => done,
                        Err(net_error::NoSuchNeighbor) => {
                            // nothing to do
                            self.state = StackerDBSyncState::Finished;
                            blocked = false;
                            false
                        }
                        Err(e) => {
                            return Err(e);
                        }
                    };
                    if done {
                        self.state = StackerDBSyncState::ConnectFinish;
                        blocked = false;
                    }
                }
                StackerDBSyncState::ConnectFinish => {
                    let done = self.connect_try_finish(network)?;
                    if done {
                        self.state = StackerDBSyncState::GetChunksInvBegin;
                        blocked = false;
                    }
                }
                StackerDBSyncState::GetChunksInvBegin => {
                    // does not block
                    self.getchunksinv_begin(network);
                    self.state = StackerDBSyncState::GetChunksInvFinish;
                    blocked = false;
                }
                StackerDBSyncState::GetChunksInvFinish => {
                    let done = self.getchunksinv_try_finish(network)?;
                    if done {
                        self.state = StackerDBSyncState::GetChunks;
                        blocked = false;
                    }
                }
                StackerDBSyncState::GetChunks => {
                    if network.get_connection_opts().disable_stackerdb_get_chunks {
                        // fault injection -- force the system to rely exclusively on push-chunk
                        // behavior
                        self.state = StackerDBSyncState::PushChunks;
                        continue;
                    }

                    let requests_finished = self.getchunks_begin(network)?;
                    let inflight_finished = self.getchunks_try_finish(network, config)?;
                    let done = requests_finished && inflight_finished;
                    if done {
                        self.state = StackerDBSyncState::PushChunks;
                        blocked = false;
                    }
                }
                StackerDBSyncState::PushChunks => {
                    let pushes_finished = self.pushchunks_begin(network)?;
                    let inflight_finished = self.pushchunks_try_finish(network);
                    let done = pushes_finished && inflight_finished;
                    if done {
                        if self.need_resync
                            && !network.get_connection_opts().disable_stackerdb_get_chunks
                        {
                            // someone pushed newer chunk data to us, and getting chunks is
                            // enabled, so immediately go request them
                            debug!(
                                "{:?}: {}: immediately retry StackerDB GetChunks due to PushChunk NACK",
                                network.get_local_peer(),
                                &self.smart_contract_id
                            );
                            self.recalculate_chunk_request_schedule(network)?;
                            self.state = StackerDBSyncState::GetChunks;
                        } else {
                            // done syncing
                            self.state = StackerDBSyncState::Finished;
                        }
                        self.need_resync = false;
                        blocked = false;
                    }
                }
                StackerDBSyncState::Finished => {
                    let stale_inv = self.stale_inv;

                    let result = self.reset(Some(network), config);
                    self.state = StackerDBSyncState::ConnectBegin;

                    if stale_inv {
                        debug!(
                            "{:?}: {}: immediately retry StackerDB sync due to stale inventory",
                            network.get_local_peer(),
                            &self.smart_contract_id
                        );
                        self.wakeup();
                    }
                    return Ok(Some(result));
                }
            };

            if blocked {
                return Ok(None);
            }
        }
    }
}
