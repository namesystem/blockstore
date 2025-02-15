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

use std::cmp::{self, Ordering};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{Read, Write};
use std::net::SocketAddr;

use p2p::DropSource;
use rand;
use rand::seq::SliceRandom;
use rand::{thread_rng, Rng};
use stacks_common::types::chainstate::{BlockHeaderHash, PoxId, SortitionId};
use stacks_common::util::hash::to_hex;
use stacks_common::util::secp256k1::{Secp256k1PrivateKey, Secp256k1PublicKey};
use stacks_common::util::{get_epoch_time_ms, get_epoch_time_secs, log};

use crate::burnchains::{Burnchain, BurnchainView};
use crate::chainstate::burn::db::sortdb::{
    BlockHeaderCache, SortitionDB, SortitionDBConn, SortitionHandleConn,
};
use crate::chainstate::burn::{BlockSnapshot, ConsensusHashExtensions};
use crate::chainstate::stacks::db::StacksChainState;
use crate::net::asn::ASEntry4;
use crate::net::chat::ConversationP2P;
use crate::net::codec::*;
use crate::net::connection::{ConnectionOptions, ConnectionP2P, ReplyHandleP2P};
use crate::net::db::{PeerDB, *};
use crate::net::neighbors::MAX_NEIGHBOR_BLOCK_DELAY;
use crate::net::p2p::{DropReason, PeerNetwork, PeerNetworkWorkState};
use crate::net::{
    Error as net_error, GetBlocksInv, Neighbor, NeighborKey, PeerAddress, StacksMessage, StacksP2P,
    *,
};
use crate::util_lib::db::{DBConn, Error as db_error};

/// This module is responsible for synchronizing block inventories with other peers
#[cfg(not(test))]
pub const INV_SYNC_INTERVAL: u64 = 150;
#[cfg(test)]
pub const INV_SYNC_INTERVAL: u64 = 3;

pub const INV_REWARD_CYCLES: u64 = 2;

#[derive(Debug, PartialEq, Clone)]
pub struct PeerBlocksInv {
    /// Bitmap of which anchored blocks this peer has
    pub block_inv: Vec<u8>,
    /// Bitmap of which microblock streams this peer has
    pub microblocks_inv: Vec<u8>,
    /// Bitmap of PoX anchor block knowledge this peer has
    pub pox_inv: Vec<u8>,
    /// Number of sortitions we know this peer knows about (after successive
    /// getblocksinv/blocksinv rounds)
    pub num_sortitions: u64,
    /// Number of reward cycles we know this peer knows about
    pub num_reward_cycles: u64,
    /// Time of last update, in seconds
    pub last_updated_at: u64,
    /// Burn block height of first sortition
    pub first_block_height: u64,
}

impl PeerBlocksInv {
    pub fn empty(first_block_height: u64) -> PeerBlocksInv {
        PeerBlocksInv {
            block_inv: vec![],
            microblocks_inv: vec![],
            pox_inv: vec![],
            num_sortitions: 0,
            num_reward_cycles: 0,
            last_updated_at: 0,
            first_block_height,
        }
    }

    pub fn new(
        block_inv: Vec<u8>,
        microblocks_inv: Vec<u8>,
        pox_inv: Vec<u8>,
        num_sortitions: u64,
        num_reward_cycles: u64,
        first_block_height: u64,
    ) -> PeerBlocksInv {
        assert_eq!(block_inv.len(), microblocks_inv.len());
        PeerBlocksInv {
            block_inv,
            microblocks_inv,
            num_sortitions,
            num_reward_cycles,
            pox_inv,
            last_updated_at: get_epoch_time_secs(),
            first_block_height,
        }
    }

    /// Does this remote neighbor have the ith block (for the ith sortition)?
    /// (note that block_height is the _absolute_ block height)
    pub fn has_ith_block(&self, block_height: u64) -> bool {
        if block_height < self.first_block_height {
            return false;
        }

        let sortition_height = block_height - self.first_block_height;
        let idx = (sortition_height / 8) as usize;
        let bit = sortition_height % 8;

        if idx >= self.block_inv.len() {
            false
        } else {
            (self.block_inv[idx] & (1 << bit)) != 0
        }
    }

    /// Does this remote neighbor have the ith microblock stream (for the ith sortition)?
    /// (note that block_height is the _absolute_ block height)
    pub fn has_ith_microblock_stream(&self, block_height: u64) -> bool {
        if block_height < self.first_block_height {
            return false;
        }

        let sortition_height = block_height - self.first_block_height;
        let idx = (sortition_height / 8) as usize;
        let bit = sortition_height % 8;

        if idx >= self.microblocks_inv.len() {
            false
        } else {
            (self.microblocks_inv[idx] & (1 << bit)) != 0
        }
    }

    /// Does this remote neighbor have certainty about the ith PoX anchor block?
    #[cfg_attr(test, mutants::skip)]
    pub fn has_ith_anchor_block(&self, reward_cycle: u64) -> bool {
        if self.num_reward_cycles <= reward_cycle {
            return false;
        }

        let idx = (reward_cycle / 8) as usize;
        let bit = reward_cycle % 8;

        if idx >= self.pox_inv.len() {
            false
        } else {
            (self.pox_inv[idx] & (1 << bit)) != 0
        }
    }

    /// Merge a blocksinv into our knowledge of what blocks exist for this neighbor.
    /// block_height corresponds to bitvec[0] & 0x01
    /// bitlen = number of sortitions represented by this inv.
    /// If clear_bits is true, then any 0-bits in the given bitvecs will be set as well as 1-bits.
    /// returns the number of bits set in each bitvec
    pub fn merge_blocks_inv(
        &mut self,
        block_height: u64,
        bitlen: u64,
        block_bitvec: Vec<u8>,
        microblocks_bitvec: Vec<u8>,
        clear_bits: bool,
    ) -> (usize, usize) {
        assert!(block_height >= self.first_block_height);
        let sortition_height = block_height - self.first_block_height;

        self.num_sortitions = if self.num_sortitions < sortition_height + bitlen {
            sortition_height + bitlen
        } else {
            self.num_sortitions
        };

        let mut insert_index = sortition_height;
        let mut new_blocks = 0;
        let mut new_microblocks = 0;

        // add each bit in, growing the block inv as needed
        for i in 0..bitlen {
            let idx = (i / 8) as usize;
            let bit = i % 8;
            let block_set = (block_bitvec[idx] & (1 << bit)) != 0;
            let microblock_set = (microblocks_bitvec[idx] & (1 << bit)) != 0;

            let set_idx = (insert_index / 8) as usize;
            let set_bit = insert_index % 8;
            if set_idx >= self.block_inv.len() {
                self.block_inv.resize(set_idx + 1, 0);
            }
            if set_idx >= self.microblocks_inv.len() {
                self.microblocks_inv.resize(set_idx + 1, 0);
            }

            if block_set {
                if self.block_inv[set_idx] & (1 << set_bit) == 0 {
                    // new
                    new_blocks += 1;
                }

                self.block_inv[set_idx] |= 1 << set_bit;
            } else if clear_bits {
                // unset
                self.block_inv[set_idx] &= !(1 << set_bit);
            }

            if microblock_set {
                if self.microblocks_inv[set_idx] & (1 << set_bit) == 0 {
                    // new
                    new_microblocks += 1;
                }

                self.microblocks_inv[set_idx] |= 1 << set_bit;
            } else if clear_bits {
                // unset
                self.microblocks_inv[set_idx] &= !(1 << set_bit);
            }

            insert_index += 1;
        }

        self.last_updated_at = get_epoch_time_secs();

        assert!(insert_index / 8 <= self.block_inv.len() as u64);
        assert!(self.num_sortitions / 8 <= self.block_inv.len() as u64);

        (new_blocks, new_microblocks)
    }

    /// Invalidate block and microblock inventories as a result of learning a new reward cycle's status.
    /// Drop all blocks and microblocks at and after the given reward cycle.
    /// Returns how many bits were dropped.
    pub fn truncate_block_inventories(&mut self, burnchain: &Burnchain, reward_cycle: u64) -> u64 {
        // invalidate all blocks and microblocks that come after this
        let highest_agreed_block_height = burnchain.reward_cycle_to_block_height(reward_cycle);

        assert!(
            highest_agreed_block_height >= self.first_block_height,
            "BUG: highest agreed block height is lower than the first-ever block"
        );

        if self.first_block_height + self.num_sortitions >= highest_agreed_block_height {
            // clear block/microblock inventories
            let num_bits =
                self.first_block_height + self.num_sortitions - highest_agreed_block_height;
            let mut zeros: Vec<u8> = Vec::with_capacity((num_bits / 8 + 1) as usize);
            for _i in 0..(num_bits / 8 + 1) {
                zeros.push(0x00);
            }

            test_debug!(
                "Clear all blocks after height {} (reward cycle {}; {} bits)",
                highest_agreed_block_height,
                reward_cycle,
                num_bits
            );
            self.merge_blocks_inv(
                highest_agreed_block_height,
                num_bits,
                zeros.clone(),
                zeros,
                true,
            );
            self.num_sortitions = highest_agreed_block_height - self.first_block_height;
            num_bits
        } else {
            0
        }
    }

    /// Invalidate PoX inventories as a result of learning a new reward cycle's status
    /// Returns how many bits were dropped
    #[cfg_attr(test, mutants::skip)]
    pub fn truncate_pox_inventory(&mut self, burnchain: &Burnchain, reward_cycle: u64) -> u64 {
        let highest_agreed_block_height = burnchain.reward_cycle_to_block_height(reward_cycle);

        assert!(
            highest_agreed_block_height >= self.first_block_height,
            "BUG: highest agreed block height is lower than the first-ever block"
        );

        if reward_cycle < self.num_reward_cycles {
            // clear pox inventories
            let num_bits = self.num_reward_cycles - reward_cycle;
            let mut zeros: Vec<u8> = Vec::with_capacity((num_bits / 8 + 1) as usize);
            for _i in 0..(num_bits / 8 + 1) {
                zeros.push(0x00);
            }

            self.merge_pox_inv(burnchain, reward_cycle, num_bits, zeros, true);
            let diff = self.num_reward_cycles - reward_cycle;
            self.num_reward_cycles = reward_cycle;
            diff
        } else {
            0
        }
    }

    /// Merge a remote peer's PoX bitvector into our view of its PoX bitvector.
    /// If we flip a 0 to a 1, then invalidate the block/microblock bits for that reward cycle _and
    /// all subsequent reward cycles_.
    /// Returns the lowest reward cycle number that changed from a 0 to a 1, if such a flip happens
    pub fn merge_pox_inv(
        &mut self,
        burnchain: &Burnchain,
        reward_cycle: u64,
        bitlen: u64,
        pox_bitvec: Vec<u8>,
        clear_bits: bool,
    ) -> Option<u64> {
        self.num_reward_cycles = if self.num_reward_cycles < reward_cycle + bitlen {
            reward_cycle + bitlen
        } else {
            self.num_reward_cycles
        };

        let mut insert_index = reward_cycle;
        let mut reward_cycle_flipped = None;

        // add each bit in, growing the pox inv as needed
        for i in 0..bitlen {
            let idx = (i / 8) as usize;
            let bit = i % 8;
            let anchor_block_set = (pox_bitvec[idx] & (1 << bit)) != 0;

            let set_idx = (insert_index / 8) as usize;
            let set_bit = insert_index % 8;
            if set_idx >= self.pox_inv.len() {
                self.pox_inv.resize(set_idx + 1, 0);
            }

            if anchor_block_set {
                if self.pox_inv[set_idx] & (1 << set_bit) == 0 {
                    // we didn't know about this bit
                    if reward_cycle_flipped.is_none() {
                        reward_cycle_flipped = Some(insert_index);
                    }
                }

                self.pox_inv[set_idx] |= 1 << set_bit;
            } else if clear_bits {
                // unset
                self.pox_inv[set_idx] &= !(1 << set_bit);
            }

            insert_index += 1;
        }

        if let Some(flipped_reward_cycle) = reward_cycle_flipped.as_ref() {
            self.truncate_block_inventories(burnchain, *flipped_reward_cycle);
        }

        self.last_updated_at = get_epoch_time_secs();

        assert!(insert_index / 8 <= self.pox_inv.len() as u64);
        assert!(self.num_reward_cycles / 8 <= self.pox_inv.len() as u64);

        reward_cycle_flipped
    }

    /// Set a block's bit as available.
    /// Return whether or not the block bit was flipped to 1.
    pub fn set_block_bit(&mut self, block_height: u64) -> bool {
        let (new_blocks, _) = self.merge_blocks_inv(block_height, 1, vec![0x01], vec![0x00], false);
        new_blocks != 0
    }

    /// Set a confirmed microblock stream's bit as available.
    /// Return whether or not the bit was flipped to 1.
    pub fn set_microblocks_bit(&mut self, block_height: u64) -> bool {
        let (_, new_mblocks) =
            self.merge_blocks_inv(block_height, 1, vec![0x00], vec![0x01], false);
        new_mblocks != 0
    }

    /// Clear a block bit
    #[cfg_attr(test, mutants::skip)]
    pub fn clear_block_bit(&mut self, block_height: u64) {
        self.merge_blocks_inv(block_height, 1, vec![0x01], vec![0x00], true);
    }

    /// Clear a microblock bit
    pub fn clear_microblock_bit(&mut self, microblock_height: u64) {
        self.merge_blocks_inv(microblock_height, 1, vec![0x00], vec![0x01], true);
    }

    /// Set a confirmed anchor block detection.
    /// Return whether or not the bit was flipped to 1
    pub fn set_pox_bit(&mut self, burnchain: &Burnchain, reward_cycle: u64) -> bool {
        let bits_set = self.merge_pox_inv(burnchain, reward_cycle, 1, vec![0x01], true);
        bits_set.unwrap_or(0) != 0
    }

    /// Count up the number of blocks represented
    pub fn num_blocks(&self) -> u64 {
        let mut total = 0;
        for i in 0..self.num_sortitions {
            if self.has_ith_block(i + self.first_block_height) {
                total += 1;
            }
        }
        total
    }

    /// Count up the number of microblock streams represented
    pub fn num_microblock_streams(&self) -> u64 {
        let mut total = 0;
        for i in 0..self.num_sortitions {
            if self.has_ith_microblock_stream(i + self.first_block_height) {
                total += 1;
            }
        }
        total
    }

    /// Count up the number of anchor blocks represented
    pub fn num_pox_anchor_blocks(&self) -> u64 {
        let mut total = 0;
        for i in 0..self.num_reward_cycles {
            if self.has_ith_anchor_block(i) {
                total += 1;
            }
        }
        total
    }

    /// Determine the lowest reward cycle that this pox inv disagrees with a given pox id
    /// Returns (disagreed reward cycle, my-inv-bit, poxid-inv-bit)
    /// If one is longer than the other, there will be disagreement
    pub fn pox_inv_cmp(&self, pox_id: &PoxId) -> Option<(u64, bool, bool)> {
        let min = cmp::min((pox_id.len() as u64) - 1, self.num_reward_cycles);
        for i in 0..min {
            let my_bit = self.has_ith_anchor_block(i);
            let pox_bit = pox_id.has_ith_anchor_block(i as usize);
            if my_bit != pox_bit {
                return Some((i, my_bit, pox_bit));
            }
        }
        let reward_cycle = (pox_id.len() as u64) - 1;
        match reward_cycle.cmp(&self.num_reward_cycles) {
            Ordering::Less => {
                // pox inv is longer
                Some((reward_cycle, self.has_ith_anchor_block(reward_cycle), false))
            }
            Ordering::Equal => {
                // all agreed
                None
            }
            Ordering::Greater => {
                // our inv is longer
                Some((
                    self.num_reward_cycles,
                    false,
                    pox_id.has_ith_anchor_block(self.num_reward_cycles as usize),
                ))
            }
        }
    }

    /// What's the block height represented here?
    pub fn get_block_height(&self) -> u64 {
        self.first_block_height + self.num_sortitions
    }

    /// What's the number of PoX reward cycles we know about?
    pub fn get_pox_height(&self) -> u64 {
        self.num_reward_cycles
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum InvWorkState {
    GetPoxInvBegin,
    GetPoxInvFinish,
    GetBlocksInvBegin,
    GetBlocksInvFinish,
    Done,
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum NodeStatus {
    Online,
    Broken,
    Diverged,
    Stale,
    Dead,
}

#[derive(Debug)]
pub struct NeighborBlockStats {
    /// Who are we talking to?
    pub nk: NeighborKey,
    /// What blocks do we know this peer has?
    pub inv: PeerBlocksInv,
    /// Current scan height for PoX (in reward cycles)
    pub pox_reward_cycle: u64,
    /// Scan height for block invs (in reward cycles)
    pub block_reward_cycle: u64,
    /// Scan state
    pub state: InvWorkState,
    /// Peer status
    pub status: NodeStatus,
    /// Ongoing request
    pub request: Option<ReplyHandleP2P>,
    /// How many blocks do we expect, if this is a BlocksInv we're expecting
    pub num_blocks_expected: u64,
    /// Ongoing request's PoX target reward cycle
    pub target_pox_reward_cycle: u64,
    /// Ongoing request's block target reward cycle
    pub target_block_reward_cycle: u64,
    /// Received PoxInv
    pub pox_inv: Option<PoxInvData>,
    /// Received BlocksInv
    pub blocks_inv: Option<BlocksInvData>,
    /// Last time we did a scan
    pub last_rescan_timestamp: u64,
    /// Finished synchronizing?
    pub done: bool,
    /// Did we learn anything new?
    pub learned_data: bool,
    /// What height do we learn at?
    pub learned_data_height: u64,
    /// How many times have we hit up this neighbor?
    pub scans: u64,
    /// Is this an always-allowed peer?
    pub is_bootstrap_peer: bool,
}

impl NeighborBlockStats {
    pub fn new(
        nk: NeighborKey,
        first_block_height: u64,
        is_bootstrap_peer: bool,
    ) -> NeighborBlockStats {
        NeighborBlockStats {
            nk,
            inv: PeerBlocksInv::empty(first_block_height),
            pox_reward_cycle: 0,
            block_reward_cycle: 0,
            state: InvWorkState::GetPoxInvBegin,
            status: NodeStatus::Online,
            num_blocks_expected: 0,
            target_pox_reward_cycle: 0,
            target_block_reward_cycle: 0,
            request: None,
            pox_inv: None,
            blocks_inv: None,
            last_rescan_timestamp: 0,
            done: false,
            learned_data: false,
            learned_data_height: u64::MAX,
            scans: 0,
            is_bootstrap_peer,
        }
    }

    pub fn is_peer_online(&self) -> bool {
        self.status == NodeStatus::Online
    }

    pub fn reset_pox_scan(&mut self, pox_reward_cycle: u64) {
        self.pox_reward_cycle = pox_reward_cycle;
        self.request = None;
        self.pox_inv = None;
        self.blocks_inv = None;
        self.state = InvWorkState::GetPoxInvBegin;

        debug!(
            "Reset {:?} PoX scan height to {}",
            &self.nk, self.pox_reward_cycle
        );
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn reset_block_scan(&mut self, block_reward_cycle: u64) {
        self.block_reward_cycle = block_reward_cycle;
        self.request = None;
        self.pox_inv = None;
        self.blocks_inv = None;
        self.state = InvWorkState::GetBlocksInvBegin;

        debug!(
            "Reset {:?} block scan height to reward cycle {}",
            &self.nk, self.block_reward_cycle
        );
    }

    /// Determine what to do with a NACK response.
    pub(crate) fn diagnose_nack(
        _nk: &NeighborKey,
        nack_data: NackData,
        chain_view: &BurnchainView,
        preamble_burn_block_height: u64,
        preamble_burn_stable_block_height: u64,
        preamble_burn_block_hash: &BurnchainHeaderHash,
        preamble_burn_stable_block_hash: &BurnchainHeaderHash,
        is_bootstrap_peer: bool,
    ) -> NodeStatus {
        let mut diverged = false;
        let mut unstable = false;
        let mut broken = false;
        let mut stale = false;

        if nack_data.error_code == NackErrorCodes::Throttled
            || nack_data.error_code == NackErrorCodes::HandshakeRequired
        {
            // TODO: do something smarter here, like just back off
            return NodeStatus::Dead;
        } else if nack_data.error_code == NackErrorCodes::NoSuchBurnchainBlock {
            // peer nacked us -- it doesn't know about the block(s) we asked about.
            if preamble_burn_block_height < chain_view.burn_block_height {
                // Because it's stale
                test_debug!("Remote neighbor {:?} is still bootstrapping at block {}, whereas we are at block {}", _nk, preamble_burn_block_height, chain_view.burn_block_height);
                stale = true;
            } else {
                // Because it's diverged?
                diverged = match chain_view
                    .last_burn_block_hashes
                    .get(&preamble_burn_stable_block_height)
                {
                    Some(stable_burn_hash) => stable_burn_hash != preamble_burn_stable_block_hash,
                    None => true,
                };
                // Because its view of the unstable portion of the burn chain is not the same as
                // ours?
                unstable = if chain_view.burn_block_height == preamble_burn_block_height {
                    chain_view.burn_block_hash != *preamble_burn_block_hash
                } else {
                    // peer is ahead of us, so we can't tell
                    true
                };

                if diverged {
                    debug!("Remote neighbor {:?} NACKed us because it diverged", _nk);
                } else if unstable {
                    debug!("Remote neighbor {:?} NACKed us because it's chain tip is different from ours", _nk);
                } else {
                    // if this peer is always allowed, then this isn't a "broken" condition -- it's
                    // a diverged condition.  we trust that it has the correct PoX view.
                    if is_bootstrap_peer {
                        debug!("Remote always-allowed neighbor {:?} NACKed us because it does not recognize our consensus hash.  Treating as Diverged.", _nk);
                        diverged = true;
                    } else {
                        debug!("Remote neighbor {:?} NACKed us because it does not recognize our consensus hash.  Treating as Diverged.", _nk);
                        diverged = true;
                    }
                }
            }
        } else if nack_data.error_code == NackErrorCodes::InvalidPoxFork {
            // peer nacked us -- it's on a different PoX fork
            debug!("Remote neighbor {:?} NACKed us because it is on a different PoX fork than our GetPoxInv/GetBlocksInv query suggested", _nk);
            diverged = true;
        } else {
            // some other error
            debug!(
                "Remote neighbor {:?} NACKed us with error code {}",
                _nk, nack_data.error_code
            );
            broken = true;
        }

        if broken {
            NodeStatus::Broken
        } else if diverged || unstable {
            NodeStatus::Diverged
        } else if stale {
            NodeStatus::Stale
        } else {
            NodeStatus::Dead
        }
    }

    fn handle_nack(
        &mut self,
        chain_view: &BurnchainView,
        preamble: &Preamble,
        nack_data: NackData,
        is_bootstrap_peer: bool,
    ) {
        let preamble_burn_block_height = preamble.burn_block_height;
        let preamble_burn_stable_block_height = preamble.burn_stable_block_height;
        let preamble_burn_block_hash = &preamble.burn_block_hash;
        let preamble_burn_stable_block_hash = &preamble.burn_stable_block_hash;

        self.status = NeighborBlockStats::diagnose_nack(
            &self.nk,
            nack_data,
            chain_view,
            preamble_burn_block_height,
            preamble_burn_stable_block_height,
            preamble_burn_block_hash,
            preamble_burn_stable_block_hash,
            is_bootstrap_peer,
        );
    }

    pub fn getpoxinv_begin(&mut self, request: ReplyHandleP2P, target_pox_reward_cycle: u64) {
        assert!(!self.done);
        assert_eq!(self.state, InvWorkState::GetPoxInvBegin);

        self.request = Some(request);
        self.pox_inv = None;
        self.target_pox_reward_cycle = target_pox_reward_cycle;
        self.learned_data = false;

        self.state = InvWorkState::GetPoxInvFinish;
    }

    /// Determine whether or not a received PoxInv is less certain than the local PoX
    /// inventory.  Return the lowest reward cycle where the remote node is less certain than us.
    pub fn check_remote_pox_inv_uncertainty(
        network: &mut PeerNetwork,
        target_pox_reward_cycle: u64,
        poxinv_data: &PoxInvData,
    ) -> u64 {
        let mut bit = target_pox_reward_cycle;
        while bit < (network.pox_id.len() as u64) - 1
            && (bit - target_pox_reward_cycle) < poxinv_data.bitlen as u64
            && (bit - target_pox_reward_cycle) < u16::MAX as u64
        {
            if network.pox_id.has_ith_anchor_block(bit as usize)
                && !poxinv_data.has_ith_reward_cycle((bit - target_pox_reward_cycle) as u16)
            {
                // the given PoxInvData is less certain than us
                break;
            }
            bit += 1;
        }
        return bit;
    }

    /// Determine whether or not a received PoxInv is more certain as the local PoX
    /// inventory.  Return the loewst reward cycle where the local nodes is less certain than the
    /// remote node.
    pub fn check_local_pox_inv_uncertainty(
        network: &mut PeerNetwork,
        target_pox_reward_cycle: u64,
        poxinv_data: &PoxInvData,
    ) -> u64 {
        let mut bit = target_pox_reward_cycle;
        while bit < (network.pox_id.len() as u64) - 1
            && (bit - target_pox_reward_cycle) < poxinv_data.bitlen as u64
            && (bit - target_pox_reward_cycle) < u16::MAX as u64
        {
            if !network.pox_id.has_ith_anchor_block(bit as usize)
                && poxinv_data.has_ith_reward_cycle((bit - target_pox_reward_cycle) as u16)
            {
                // the given PoxInvData is more certain than us
                break;
            }
            bit += 1;
        }
        return bit;
    }

    /// Try to finish getting all PoxInvData requests.
    /// Return true if this method is done -- i.e. all requests have been handled.
    /// Return false if we're not done.
    /// Return Err(..) on irrecoverable error.
    pub fn getpoxinv_try_finish(&mut self, network: &mut PeerNetwork) -> Result<bool, net_error> {
        assert!(!self.done);
        assert_eq!(self.state, InvWorkState::GetPoxInvFinish);

        let mut request = self.request.take().expect("BUG: no request set");
        if let Err(e) = network.saturate_p2p_socket(request.get_event_id(), &mut request) {
            self.status = NodeStatus::Dead;
            return Err(e);
        }

        let next_request = match request.try_send_recv() {
            Ok(message) => {
                match message.payload {
                    StacksMessageType::PoxInv(poxinv_data) => {
                        debug!(
                            "Got PoxInv response at reward cycle {} from {:?} at ({},{}): {:?}",
                            self.target_pox_reward_cycle,
                            &self.nk,
                            message.preamble.burn_block_height,
                            message.preamble.burn_stable_block_height,
                            &poxinv_data
                        );
                        self.pox_inv = Some(poxinv_data);
                    }
                    StacksMessageType::Nack(nack_data) => {
                        debug!("Remote neighbor {:?} nack'ed our GetPoxInv at reward cycle {}: NACK code {}", &self.nk, self.target_pox_reward_cycle, nack_data.error_code);
                        let is_bootstrap_peer = PeerDB::is_initial_peer(
                            network.peerdb.conn(),
                            self.nk.network_id,
                            &self.nk.addrbytes,
                            self.nk.port,
                        )
                        .unwrap_or(false);
                        self.handle_nack(
                            &network.chain_view,
                            &message.preamble,
                            nack_data,
                            is_bootstrap_peer,
                        );
                    }
                    _ => {
                        // unexpected reply
                        debug!(
                            "Remote neighbor {:?} sent an unexpected reply of '{}'",
                            &self.nk,
                            message.get_message_name()
                        );
                        self.status = NodeStatus::Broken;
                        return Err(net_error::InvalidMessage);
                    }
                }
                None
            }
            Err(req_res) => match req_res {
                Ok(same_req) => Some(same_req),
                Err(e) => {
                    debug!("Failed to get PoX inventory: {:?}", &e);
                    self.status = NodeStatus::Dead;
                    None
                }
            },
        };

        if let Some(next_request) = next_request {
            // still working
            self.request = Some(next_request);
            Ok(false)
        } else {
            // done!
            self.state = InvWorkState::Done;
            Ok(true)
        }
    }

    /// Proceed to get block inventories
    pub fn getblocksinv_begin(
        &mut self,
        request: ReplyHandleP2P,
        target_block_reward_cycle: u64,
        num_blocks_expected: u16,
    ) {
        assert!(!self.done);
        assert_eq!(self.state, InvWorkState::GetBlocksInvBegin);

        self.request = Some(request);
        self.target_block_reward_cycle = target_block_reward_cycle;
        self.num_blocks_expected = num_blocks_expected as u64;

        self.state = InvWorkState::GetBlocksInvFinish;
    }

    /// Try to finish getting all BlocksInvData requests.
    /// Return true if this method is done -- i.e. all requests have been handled.
    /// Return false if we're not done.
    pub fn getblocksinv_try_finish(
        &mut self,
        network: &mut PeerNetwork,
    ) -> Result<bool, net_error> {
        assert!(!self.done);
        assert_eq!(self.state, InvWorkState::GetBlocksInvFinish);

        let mut request = self.request.take().expect("BUG: request not set");
        if let Err(e) = network.saturate_p2p_socket(request.get_event_id(), &mut request) {
            self.status = NodeStatus::Dead;
            return Err(e);
        }

        let next_request = match request.try_send_recv() {
            Ok(message) => {
                match message.payload {
                    StacksMessageType::BlocksInv(blocks_inv_data) => {
                        // got a BlocksInv!
                        // but, did we get all the bits we asked for?
                        if blocks_inv_data.bitlen as u64 != self.num_blocks_expected {
                            info!(
                                "Got invalid BlocksInv response: expected {} bits, got {}",
                                self.num_blocks_expected, blocks_inv_data.bitlen
                            );
                            self.status = NodeStatus::Broken;
                        } else {
                            debug!("Got BlocksInv response from {:?} at reward cycle {} at ({},{}): {:?}", &self.nk, self.target_block_reward_cycle, message.preamble.burn_block_height, message.preamble.burn_stable_block_height, &blocks_inv_data);
                            self.blocks_inv = Some(blocks_inv_data);
                        }
                    }
                    StacksMessageType::Nack(nack_data) => {
                        debug!("Remote neighbor {:?} nack'ed our GetBlocksInv at reward cycle {}: NACK code {}", &self.nk, self.target_block_reward_cycle, nack_data.error_code);
                        let is_bootstrap_peer = PeerDB::is_initial_peer(
                            network.peerdb.conn(),
                            self.nk.network_id,
                            &self.nk.addrbytes,
                            self.nk.port,
                        )
                        .unwrap_or(false);
                        self.handle_nack(
                            &network.chain_view,
                            &message.preamble,
                            nack_data,
                            is_bootstrap_peer,
                        );
                    }
                    _ => {
                        // unexpected reply
                        debug!(
                            "Remote neighbor {:?} sent an unexpected reply of '{}'",
                            &self.nk,
                            message.get_message_name()
                        );
                        self.status = NodeStatus::Broken;
                    }
                }
                None
            }
            Err(req_res) => match req_res {
                Ok(same_req) => Some(same_req),
                Err(e) => {
                    debug!(
                        "Failed to send/receive GetBlocksInv/BlocksInv from {:?}: {:?}",
                        &self.nk, &e
                    );
                    self.status = NodeStatus::Dead;
                    None
                }
            },
        };

        if let Some(next_request) = next_request {
            debug!("Still waiting for BlocksInv reply from {:?}", &self.nk);
            self.request = Some(next_request);
            Ok(false)
        } else {
            debug!("Finished inventory scan for {:?}", &self.nk);
            self.state = InvWorkState::Done;
            self.scans += 1;
            Ok(true)
        }
    }
}

#[derive(Debug)]
pub struct InvState {
    /// Accumulated knowledge of which peers have which blocks.
    /// Kept separately from p2p conversations so they persist
    /// beyond connection resets (since they can be expensive
    /// to build up).
    pub block_stats: HashMap<NeighborKey, NeighborBlockStats>,

    /// How long is a request allowed to take?
    request_timeout: u64,
    /// First burn block height
    first_block_height: u64,

    /// Last time we learned about new blocks
    pub last_change_at: u64,
    /// How often to re-sync
    sync_interval: u64,
    /// Did any neighbor learn any new data?
    pub hint_learned_data: bool,
    pub hint_learned_data_height: u64,
    /// Should we do a re-scan?
    hint_do_rescan: bool,
    /// last time a rescan was completed
    last_rescanned_at: u64,

    /// How many passes -- short and full -- have we done?
    num_inv_syncs: u64,

    /// What's the last reward cycle we _started_ the inv scan at?
    pub block_sortition_start: u64,

    /// event IDs of connections we established, so they don't get pruned
    pinned: HashSet<usize>,
}

impl InvState {
    pub fn new(first_block_height: u64, request_timeout: u64, sync_interval: u64) -> InvState {
        InvState {
            block_stats: HashMap::new(),

            request_timeout,
            first_block_height,

            last_change_at: 0,
            sync_interval,

            hint_learned_data: false,
            hint_learned_data_height: u64::MAX,
            hint_do_rescan: true,
            last_rescanned_at: 0,

            num_inv_syncs: 0,

            block_sortition_start: 0,
            pinned: HashSet::new(),
        }
    }

    fn reset_sync_peers(
        &mut self,
        network: &PeerNetwork,
        peers: HashSet<NeighborKey>,
        bootstrap_peers: &HashSet<NeighborKey>,
        max_neighbors: usize,
    ) {
        for (nk, stats) in self.block_stats.iter_mut() {
            if stats.status != NodeStatus::Online {
                stats.status = NodeStatus::Online;
            }
            stats.done = false;
            stats.learned_data = false;
            stats.learned_data_height = u64::MAX;

            stats.is_bootstrap_peer = bootstrap_peers.contains(nk);
        }

        let mut added = 0;
        for peer in peers.iter() {
            if let Some(stats) = self.block_stats.get_mut(peer) {
                debug!("Already tracking inventories of peer {:?}", &peer);
                stats.reset_pox_scan(0);
                stats.is_bootstrap_peer = bootstrap_peers.contains(peer);
            } else if self.block_stats.len() < max_neighbors {
                debug!("Will track inventories of new peer {:?}", &peer);
                self.block_stats.insert(
                    peer.clone(),
                    NeighborBlockStats::new(
                        peer.clone(),
                        self.first_block_height,
                        bootstrap_peers.contains(peer),
                    ),
                );
                added += 1;
            }
        }

        let mut peers: Vec<_> = self.block_stats.keys().collect();
        peers.sort();
        debug!(
            "Now have {} inv block stats tracked (added {}): {:?}",
            self.block_stats.len(),
            added,
            &peers
        );

        // if we're still connected to these peers, then keep them pinned
        self.pinned.clear();
        for peer in peers.iter() {
            if let Some(event_id) = network.get_event_id(peer) {
                self.pinned.insert(event_id);
            }
        }
    }

    /// Pin a connection
    pub fn pin_connection(&mut self, event_id: usize) {
        self.pinned.insert(event_id);
    }

    /// Get the set of connections this state machine is using
    pub fn get_pinned_connections(&self) -> &HashSet<usize> {
        &self.pinned
    }

    pub fn get_peer_status(&self, nk: &NeighborKey) -> NodeStatus {
        if let Some(stats) = self.block_stats.get(nk) {
            stats.status
        } else {
            NodeStatus::Dead
        }
    }

    /// How many sortitions do we know about from this neighbor?
    /// Ignores broken or diverged peers.
    pub fn get_inv_sortitions(&self, nk: &NeighborKey) -> u64 {
        if self.get_peer_status(nk) != NodeStatus::Online {
            return 0;
        }

        match self.block_stats.get(nk) {
            Some(stats) => stats.inv.num_sortitions,
            _ => 0,
        }
    }

    /// How many blocks do we know about from this neighbor?
    /// Ignores broken or diverged peers
    pub fn get_inv_num_blocks(&self, nk: &NeighborKey) -> u64 {
        if self.get_peer_status(nk) != NodeStatus::Online {
            return 0;
        }

        match self.block_stats.get(nk) {
            Some(stats) => stats.inv.num_blocks(),
            _ => 0,
        }
    }

    /// Cull broken peers and purge their stats
    pub fn cull_bad_peers(&mut self) -> HashSet<NeighborKey> {
        let mut bad_peers = HashSet::new();
        for (nk, stats) in self.block_stats.iter() {
            if stats.status == NodeStatus::Broken {
                debug!(
                    "Peer {:?} has node status {:?}; culling...",
                    nk, &stats.status
                );
                bad_peers.insert(nk.clone());
            }
        }

        for bad_peer in bad_peers.iter() {
            self.block_stats.remove(bad_peer);
        }

        debug!(
            "Now have {} inv block stats tracked",
            self.block_stats.len()
        );
        bad_peers
    }

    /// Get the list of broken peers
    pub fn get_broken_peers(&self) -> Vec<NeighborKey> {
        let mut list = vec![];
        for (nk, stats) in self.block_stats.iter() {
            if stats.status == NodeStatus::Broken {
                list.push(nk.clone());
            }
        }
        list
    }

    /// Get the list of diverged peers
    pub fn get_diverged_peers(&self) -> Vec<NeighborKey> {
        let mut list = vec![];
        for (nk, stats) in self.block_stats.iter() {
            if stats.status == NodeStatus::Diverged {
                list.push(nk.clone());
            }
        }
        list
    }

    /// Get the list of dead
    pub fn get_dead_peers(&self) -> Vec<NeighborKey> {
        let mut list = vec![];
        for (nk, stats) in self.block_stats.iter() {
            if stats.status == NodeStatus::Dead {
                list.push(nk.clone());
            }
        }
        list
    }

    pub fn get_stats(&self, nk: &NeighborKey) -> Option<&NeighborBlockStats> {
        self.block_stats.get(nk)
    }

    pub fn get_stats_mut(&mut self, nk: &NeighborKey) -> Option<&mut NeighborBlockStats> {
        self.block_stats.get_mut(nk)
    }

    #[cfg(test)]
    pub fn add_peer(&mut self, nk: NeighborKey, is_bootstrap_peer: bool) {
        self.block_stats.insert(
            nk.clone(),
            NeighborBlockStats::new(nk, self.first_block_height, is_bootstrap_peer),
        );
    }

    pub fn del_peer(&mut self, nk: &NeighborKey) {
        self.block_stats.remove(nk);
    }

    /// Is there any downloader-actionable data available?
    pub fn has_inv_data_for_downloader(&self, ibd: bool) -> bool {
        let mut ret = false;
        for (nk, stats) in self.block_stats.iter() {
            if stats.scans > 0 && (!ibd || stats.is_bootstrap_peer) {
                debug!("Have inv data for downloader from {:?} (ibd={}, is_bootstrap_peer={}, scans={}))", nk, ibd, stats.is_bootstrap_peer, stats.scans);
                ret = true;
            }
        }
        if !ret {
            debug!(
                "Have {} block_stats, but none represent useful data for the downloader",
                self.block_stats.len()
            );
        }
        ret
    }

    /// Set a block or confirmed microblock stream as available, given the burn header hash and consensus hash.
    /// Used when processing a BlocksAvailable or MicroblocksAvailable message.
    /// Drops if the message refers to a block height
    /// Returns the optional block sortition height at which the block or confirmed microblock stream resides in the blockchain (returns
    /// None if its bit was already set).
    /// Returns NotFoundError if the consensus hash is not recognized, but may be recognized in the
    /// future
    fn set_data_available(
        &mut self,
        burnchain: &Burnchain,
        neighbor_key: &NeighborKey,
        sortdb: &SortitionDB,
        consensus_hash: &ConsensusHash,
        microblocks: bool,
    ) -> Result<Option<u64>, net_error> {
        let sn = match SortitionDB::get_block_snapshot_consensus(sortdb.conn(), consensus_hash)? {
            Some(sn) => {
                if !sn.pox_valid {
                    debug!(
                        "Unknown consensus hash {}: not on valid PoX fork",
                        consensus_hash
                    );
                    // absorb
                    return Ok(None);
                }
                sn
            }
            None => {
                // we don't know about this block -- the sending node is probably too far ahead of
                // us.
                debug!("Unknown consensus hash {}", consensus_hash);
                return Err(net_error::NotFoundError);
            }
        };

        if !sn.sortition || sn.block_height == 0 {
            // No block is available here anyway, even though the peer agrees with us on the
            // consensus hash.
            // This is bad behavior on the peer's part.
            debug!("No sortition for consensus hash {}", consensus_hash);
            return Err(net_error::InvalidMessage);
        }

        match self.block_stats.get_mut(neighbor_key) {
            Some(stats) => {
                // can't set this if we haven't scanned this remote node's PoX inventory this high
                let reward_cycle = match burnchain.block_height_to_reward_cycle(sn.block_height) {
                    Some(rc) => rc,
                    None => {
                        debug!(
                            "Block {} ({}) does not correspond to a reward cycle",
                            sn.block_height, sn.consensus_hash
                        );
                        return Err(net_error::NotFoundError);
                    }
                };

                if reward_cycle > stats.inv.num_reward_cycles {
                    // too far ahead
                    debug!("Cannot set {} for {} available: it comes from reward cycle {}, but we have only scanned up to {}",
                          if microblocks { "confirmed microblock stream" } else { "block" }, sn.consensus_hash, reward_cycle, stats.inv.num_reward_cycles);
                    return Err(net_error::NotFoundError);
                }

                // NOTE: block heights are 1-indexed in the burn DB, since the 0th snapshot block is the
                // genesis snapshot and doesn't correspond to anything (the 1st snapshot is block 0)
                let set = if microblocks {
                    debug!(
                        "Neighbor {:?} now has confirmed microblock stream at {} ({}) (sortition {})",
                        neighbor_key, sn.block_height, consensus_hash, sn.block_height - sortdb.first_block_height
                    );
                    stats.inv.set_microblocks_bit(sn.block_height)
                } else {
                    debug!(
                        "Neighbor {:?} now has block at {} ({}) (sortition {})",
                        neighbor_key,
                        sn.block_height,
                        consensus_hash,
                        sn.block_height - sortdb.first_block_height
                    );
                    stats.inv.set_block_bit(sn.block_height)
                };

                debug!("Neighbor {:?} stats: {:?}", neighbor_key, stats);
                if set {
                    let block_sortition_height = sn.block_height - sortdb.first_block_height;
                    Ok(Some(block_sortition_height))
                } else {
                    Ok(None)
                }
            }
            None => {
                debug!("No inv stats for neighbor {:?}", neighbor_key);
                Ok(None)
            }
        }
    }

    pub fn set_block_available(
        &mut self,
        burnchain: &Burnchain,
        neighbor_key: &NeighborKey,
        sortdb: &SortitionDB,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<u64>, net_error> {
        self.set_data_available(burnchain, neighbor_key, sortdb, consensus_hash, false)
    }

    pub fn set_microblocks_available(
        &mut self,
        burnchain: &Burnchain,
        neighbor_key: &NeighborKey,
        sortdb: &SortitionDB,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<u64>, net_error> {
        self.set_data_available(burnchain, neighbor_key, sortdb, consensus_hash, true)
    }

    /// Invalidate all block inventories at and after a given reward cycle
    pub fn invalidate_block_inventories(&mut self, burnchain: &Burnchain, reward_cycle: u64) {
        for (nk, stats) in self.block_stats.iter_mut() {
            debug!("Truncate PoX inventory for {:?} to {}", nk, reward_cycle);
            let pox_dropped = stats.inv.truncate_pox_inventory(burnchain, reward_cycle);
            let blocks_dropped = stats
                .inv
                .truncate_block_inventories(burnchain, reward_cycle);

            if pox_dropped > 0 || blocks_dropped > 0 {
                // re-start synchronization at this height
                stats.reset_pox_scan(reward_cycle);
            }
        }
    }
}

impl PeerNetwork {
    /// Get our current tip snapshot, accounting for PoX invalidation
    fn get_tip_sortition_snapshot(&self, sortdb: &SortitionDB) -> Result<BlockSnapshot, net_error> {
        match SortitionDB::get_block_snapshot(sortdb.conn(), &self.tip_sort_id)? {
            Some(sn) => {
                if !sn.pox_valid {
                    // our sortition ID tip got invalidated
                    return Err(net_error::StaleView);
                }
                Ok(sn)
            }
            None => Err(net_error::StaleView),
        }
    }

    /// Get an ancestor snapshot, accounting for PoX invalidation
    pub fn get_ancestor_sortition_snapshot(
        &self,
        sortdb: &SortitionDB,
        height: u64,
    ) -> Result<BlockSnapshot, net_error> {
        let sn = self.get_tip_sortition_snapshot(sortdb)?;
        if sn.block_height < height {
            debug!(
                "Tip sortition snapshot is at {} < {}",
                sn.block_height, height
            );
            return Err(net_error::NotFoundError);
        }

        let ic = sortdb.index_conn();
        match SortitionDB::get_ancestor_snapshot(&ic, height, &sn.sortition_id)? {
            Some(sn) => {
                if !sn.pox_valid {
                    // our sortition ID tip got invalidated
                    return Err(net_error::StaleView);
                }
                Ok(sn)
            }
            None => Err(net_error::StaleView),
        }
    }

    /// Get a snapshot that a peer claims to have.
    /// Return Ok(None) if we don't have this snapshot
    fn get_peer_sortition_snapshot(
        &self,
        sortdb: &SortitionDB,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<BlockSnapshot>, net_error> {
        let ic = sortdb.index_conn();
        let sortdb_reader = SortitionHandleConn::open_reader(&ic, &self.tip_sort_id)?;
        match sortdb_reader.get_block_snapshot(burn_header_hash)? {
            Some(sn) => {
                if !sn.pox_valid {
                    // our sortition ID tip got invalidated
                    return Err(net_error::StaleView);
                }
                Ok(Some(sn))
            }
            None => Ok(None),
        }
    }

    /// Try to make a GetPoxInv request for the target reward cycle for this peer.
    /// The resulting GetPoxInv, if Some(..), will request a segment of the remote peer's PoX
    /// bitvector starting from target_pox_reward_cycle, and fetching up to GETPOXINV_MAX_BITLEN bits.
    /// The target_pox_reward_cycle will be the _lowest_ reward cycle requested.
    fn make_getpoxinv(
        &self,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        target_pox_reward_cycle: u64,
    ) -> Result<Option<GetPoxInv>, net_error> {
        if target_pox_reward_cycle >= self.pox_id.num_inventory_reward_cycles() as u64 {
            debug!("{:?}: target reward cycle for neighbor {:?} is {}, which is equal to or higher than our PoX bit vector length {}", &self.local_peer, nk, target_pox_reward_cycle, self.pox_id.num_inventory_reward_cycles());
            return Ok(None);
        }

        let target_block_height = self
            .burnchain
            .reward_cycle_to_block_height(target_pox_reward_cycle);

        let max_reward_cycle = match self.get_neighbor_convo(nk) {
            Some(convo) => {
                // only proceed if the remote neighbor has this reward cycle
                let tip_height = convo.get_burnchain_tip_height();
                let tip_burn_block_hash = convo.get_burnchain_tip_burn_header_hash();

                debug!(
                    "{:?}: chain view of {:?} is ({},{})",
                    &self.local_peer, nk, tip_height, &tip_burn_block_hash
                );

                if target_block_height > tip_height {
                    // this peer is behind us
                    debug!("{:?}: remote neighbor {:?}'s burnchain view tip is {}-{:?}, which is lower than our target reward cycle {} (height {})",
                            &self.local_peer, nk, tip_height, &tip_burn_block_hash, target_pox_reward_cycle, target_block_height);
                    return Ok(None);
                }

                let tip_reward_cycle = match self.burnchain.block_height_to_reward_cycle(tip_height)
                {
                    Some(tip_rc) => tip_rc,
                    None => {
                        // peer is behind the first block, which should never happen if the peer
                        // is behaving correctly
                        debug!(
                            "{:?}: remote neighbor {:?} is behind the first-ever block",
                            &self.local_peer, nk
                        );
                        return Ok(None);
                    }
                };

                let max_reward_cycle = cmp::min(
                    self.pox_id.num_inventory_reward_cycles() as u64,
                    tip_reward_cycle,
                );
                test_debug!(
                    "{:?}: request up to reward cycle min({},{}) = {}",
                    &self.local_peer,
                    self.pox_id.num_inventory_reward_cycles(),
                    tip_reward_cycle,
                    max_reward_cycle
                );
                max_reward_cycle
            }
            None => {
                debug!("{:?}: no conversation open for {}", &self.local_peer, nk);
                return Ok(None);
            }
        };

        // ask for all PoX bits in-between target_reward_cyle and highest_reward_cycle, inclusive
        let num_reward_cycles =
            if target_pox_reward_cycle + GETPOXINV_MAX_BITLEN <= max_reward_cycle {
                GETPOXINV_MAX_BITLEN
            } else {
                cmp::max(1, max_reward_cycle - target_pox_reward_cycle)
            };

        if num_reward_cycles == 0 {
            debug!("{:?}: will not send GetPoxInv to {:?}, since we are sync'ed up to its highest reward cycle (our target was {}, our max len is {})", &self.local_peer, nk, target_pox_reward_cycle, self.pox_id.num_inventory_reward_cycles());
            return Ok(None);
        }
        assert!(num_reward_cycles <= GETPOXINV_MAX_BITLEN);

        // make sure the remote node has the same chain tip view as us
        let ancestor_sn = match self.get_ancestor_sortition_snapshot(sortdb, target_block_height) {
            Ok(s) => s,
            Err(net_error::NotFoundError) => {
                // we're not caught up to target_block_height
                debug!("{:?}: Will not send GetPoxInv to {:?}, since we are not caught up to block height {}", &self.local_peer, nk, target_block_height);
                return Ok(None);
            }
            Err(e) => {
                warn!(
                    "{:?}: failed to get ancestor sortition snapshot: {:?}",
                    &self.local_peer, &e
                );
                return Err(e);
            }
        };

        let getpoxinv = GetPoxInv {
            consensus_hash: ancestor_sn.consensus_hash,
            num_cycles: num_reward_cycles as u16,
        };

        debug!(
            "{:?}: Send GetPoxInv to {:?} for {} reward cycles starting at {} ({})",
            &self.local_peer,
            nk,
            num_reward_cycles,
            target_pox_reward_cycle,
            &getpoxinv.consensus_hash
        );
        Ok(Some(getpoxinv))
    }

    /// Determine how many blocks to ask for in a GetBlocksInv request to a given neighbor.
    /// Possibly ask for no blocks -- for example, the neighbor may not have sync'ed the burnchain,
    /// or may not agree on our PoX view.
    fn get_getblocksinv_num_blocks(
        &self,
        sortdb: &SortitionDB,
        target_block_reward_cycle: u64,
        nk: &NeighborKey,
        stats: &NeighborBlockStats,
        convo: &ConversationP2P,
    ) -> Result<u64, net_error> {
        if target_block_reward_cycle >= (self.pox_id.num_inventory_reward_cycles() as u64) {
            debug!(
                "{:?}: target reward cycle {} >= our max reward cycle {}",
                &self.local_peer,
                target_block_reward_cycle,
                self.pox_id.num_inventory_reward_cycles()
            );
            return Ok(0);
        }

        // does the peer agree with our PoX view up to this reward cycle?
        if let Some((disagreed, _, _)) = stats.inv.pox_inv_cmp(&self.pox_id) {
            if disagreed < target_block_reward_cycle {
                // can't proceed
                debug!("{:?}: remote neighbor {:?} disagrees with our PoX inventory at reward cycle {} (asked for {})", &self.local_peer, nk, disagreed, target_block_reward_cycle);
                return Ok(0);
            }
        }

        let target_block_height = self
            .burnchain
            .reward_cycle_to_block_height(target_block_reward_cycle);
        let tip_height = convo.get_burnchain_tip_height();
        let tip_burn_block_hash = convo.get_burnchain_tip_burn_header_hash();
        let stable_tip_height = convo.get_stable_burnchain_tip_height();
        let stable_tip_burn_block_hash = convo.get_stable_burnchain_tip_burn_header_hash();

        let my_tip = self.get_tip_sortition_snapshot(sortdb)?;

        debug!(
            "{:?}: chain view of {:?} is ({},{})",
            &self.local_peer, nk, tip_height, &tip_burn_block_hash
        );

        if target_block_height > tip_height {
            debug!("{:?}: target block height {} for reward cycle {} is higher than {:?}'s highest block {}", &self.local_peer, target_block_height, target_block_reward_cycle, nk, tip_height);
            return Ok(0);
        }

        // maximum burn block height we can ask this neighbor about
        let max_burn_block_height = {
            if my_tip.block_height >= tip_height
                && self
                    .get_peer_sortition_snapshot(sortdb, &tip_burn_block_hash)?
                    .is_none()
            {
                // we are at least as far along as the remote peer, but we don't know about this remote peer's burnchain tip
                if self
                    .get_peer_sortition_snapshot(sortdb, &stable_tip_burn_block_hash)?
                    .is_none()
                {
                    // we don't know about this remote peer's stable burnchain tip either, so ask
                    // for no blocks.
                    debug!("{:?}: remote neighbor {:?}'s burnchain stable view tip is {}-{:?}, which we do not know", &self.local_peer, nk, stable_tip_height, &stable_tip_burn_block_hash);
                    return Ok(0);
                }

                // go with the remote peer's stable burnchain view as our maximum allowed query
                // height
                debug!("{:?}: remote neighbor {:?}'s burnchain view tip is {}-{:?}, which we do not know. Falling back to stable tip {}-{:?}", &self.local_peer, nk, tip_height, &tip_burn_block_hash, stable_tip_height, &stable_tip_burn_block_hash);
                self.chain_view.burn_stable_block_height
            } else {
                // remote peer is further ahead than us, so max out at our maximum view
                self.chain_view.burn_block_height
            }
        };

        // ask for all blocks in-between target_block_height and max_burn_block_height in this
        // reward cycle, inclusive
        let num_blocks = if target_block_height
            + (self.burnchain.pox_constants.reward_cycle_length as u64)
            <= max_burn_block_height
        {
            self.burnchain.pox_constants.reward_cycle_length as u64
        } else if target_block_height > max_burn_block_height {
            debug!("{:?}: will not send GetBlocksInv to {:?}, since we are sync'ed up to its highest sortition block (target block is {}, max burn block is {})", &self.local_peer, nk, target_block_height, max_burn_block_height);
            0
        } else {
            max_burn_block_height - target_block_height + 1
        };

        if num_blocks == 0 {
            // target_block_height was higher than the highest known height of the remote node
            debug!("{:?}: will not send GetBlocksInv to {:?}, since we are sync'ed up to its highest sortition block (our target reward cycle was {}, height was {})", &self.local_peer, nk, target_block_reward_cycle, target_block_height);
        }

        Ok(num_blocks)
    }

    /// Make a GetBlocksInv request for a given reward cycle.
    /// Returns Ok(None) if we cannot make a request at this reward cycle (either the remote peer
    /// is too far behind the burnchain tip, or their PoX inventory disagrees with us, or we're not
    /// caught up with target_block_reward_cycle).
    fn make_getblocksinv(
        &self,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &NeighborBlockStats,
        target_block_reward_cycle: u64,
    ) -> Result<Option<GetBlocksInv>, net_error> {
        let target_block_height = self
            .burnchain
            .reward_cycle_to_block_height(target_block_reward_cycle);

        let ancestor_sn = match self.get_ancestor_sortition_snapshot(sortdb, target_block_height) {
            Ok(s) => s,
            Err(net_error::NotFoundError) => {
                // we're not caught up
                debug!("{:?}: Will not send GetBlocksInv to {:?}, since we are not caught up to block height {}", &self.local_peer, nk, target_block_height);
                return Ok(None);
            }
            Err(e) => {
                warn!(
                    "{:?}: failed to get ancestor sortition snapshot: {:?}",
                    &self.local_peer, &e
                );
                return Err(e);
            }
        };

        assert!(
            target_block_reward_cycle == 0
                || self.burnchain.is_reward_cycle_start(target_block_height)
        );

        let num_blocks = match self.get_neighbor_convo(nk) {
            Some(convo) => {
                match self.get_getblocksinv_num_blocks(
                    sortdb,
                    target_block_reward_cycle,
                    nk,
                    stats,
                    convo,
                )? {
                    0 => {
                        // cannot ask this peer for any blocks in this reward cycle
                        debug!("{:?}: no blocks available from {} at cycle {} (which starts at height {})", &self.local_peer, nk, target_block_reward_cycle, self.burnchain.reward_cycle_to_block_height(target_block_reward_cycle));
                        return Ok(None);
                    }
                    x => x,
                }
            }
            None => {
                debug!("{:?}: no conversation open for {}", &self.local_peer, nk);
                return Ok(None);
            }
        };

        assert!(num_blocks <= self.burnchain.pox_constants.reward_cycle_length as u64);

        debug!(
            "{:?}: Send GetBlocksInv to {:?} for {} blocks at sortition block {} ({}) out of {}",
            &self.local_peer,
            nk,
            num_blocks,
            target_block_height,
            &ancestor_sn.consensus_hash,
            self.chain_view.burn_block_height
        );
        Ok(Some(GetBlocksInv {
            consensus_hash: ancestor_sn.consensus_hash,
            num_blocks: num_blocks as u16,
        }))
    }

    /// Is a peer worth talking to?
    fn is_peer_target(&self, nk: &NeighborKey) -> bool {
        // don't talk to inbound peers; only outbound (and only ones we have the key for)
        // (we make this check each time we begin a round of requests, since the set of
        // available peers can change during this time).
        match self.events.get(nk) {
            Some(event_id) => match self.peers.get(event_id) {
                Some(convo) => {
                    if !convo.is_outbound() {
                        debug!("{:?}: skip {:?}: not outbound", &self.local_peer, convo);
                        return false;
                    }
                    if !convo.is_authenticated() {
                        debug!(
                            "{:?}: skip {:?}: not authenticated",
                            &self.local_peer, convo
                        );
                        return false;
                    }
                    return true;
                }
                None => {
                    return false;
                }
            },
            None => {
                return false;
            }
        }
    }

    /// Make a possible GetPoxInv request for this neighbor.
    /// Returns Some((target-reward-cycle, getpoxinv-request)) if we are to request a PoX
    /// inventory for this node.
    fn make_next_getpoxinv(
        &self,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &NeighborBlockStats,
    ) -> Result<Option<(u64, GetPoxInv)>, net_error> {
        if stats.inv.num_reward_cycles < self.pox_id.num_inventory_reward_cycles() as u64 {
            // We don't yet know all of the PoX bits for this node
            debug!("{:?}: PoX inventory not sync'ed with {:?} yet (target {} < our tip {}); make GetPoxInv based at {}", &self.local_peer, nk, stats.inv.num_reward_cycles, self.pox_id.num_inventory_reward_cycles(), stats.inv.num_reward_cycles);
            match self.make_getpoxinv(sortdb, nk, stats.inv.num_reward_cycles)? {
                Some(request) => Ok(Some((stats.inv.num_reward_cycles, request))),
                None => {
                    debug!("{:?}: will not fetch PoX inventory from {:?} even though target reward cycle {} < our tip {}", &self.local_peer, nk, stats.inv.num_reward_cycles, self.pox_id.num_inventory_reward_cycles());
                    Ok(None)
                }
            }
        } else {
            // We do know all of this node's PoX bits, but proceed to rescan anyway
            debug!(
                "{:?}: PoX inventory sync'ed with {:?}, but rescan at reward cycle {}",
                &self.local_peer, nk, stats.pox_reward_cycle
            );
            match self.make_getpoxinv(sortdb, nk, stats.pox_reward_cycle)? {
                Some(request) => Ok(Some((stats.pox_reward_cycle, request))),
                None => {
                    debug!("{:?}: will not fetch PoX inventory from {:?} even though rescan reward cycle {} >= our tip {}", &self.local_peer, nk, stats.pox_reward_cycle, self.pox_id.num_inventory_reward_cycles());
                    Ok(None)
                }
            }
        }
    }

    /// Make the next GetBlocksInv for a peer
    fn make_next_getblocksinv(
        &self,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &NeighborBlockStats,
    ) -> Result<Option<(u64, GetBlocksInv)>, net_error> {
        if stats.block_reward_cycle <= stats.inv.num_reward_cycles {
            self.make_getblocksinv(sortdb, nk, stats, stats.block_reward_cycle)
                .map(|getblocksinv_opt| {
                    getblocksinv_opt.map(|getblocksinv| (stats.block_reward_cycle, getblocksinv))
                })
        } else {
            Ok(None)
        }
    }

    /// Determine at which reward cycle to begin scanning inventories
    pub(crate) fn get_block_scan_start(&self, sortdb: &SortitionDB) -> u64 {
        // see if the stacks tip affirmation map and heaviest affirmation map diverge.  If so, then
        // start scaning at the reward cycle just before that.
        let am_rescan_rc = self
            .stacks_tip_affirmation_map
            .find_inv_search(&self.heaviest_affirmation_map);

        // affirmation maps are compatible, so just resume scanning off of wherever we are at the
        // tip.
        // NOTE: This code path only works in Stacks 2.x, but that's okay because this whole state
        // machine is only used in Stacks 2.x
        let (consensus_hash, _) = SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn())
            .unwrap_or((ConsensusHash::empty(), BlockHeaderHash([0u8; 32])));

        let stacks_tip_burn_block_height =
            match SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &consensus_hash) {
                Err(_) => self.burnchain.first_block_height,
                Ok(x) => x
                    .map(|sn| sn.block_height)
                    .unwrap_or(self.burnchain.first_block_height),
            };

        let stacks_tip_rc = self
            .burnchain
            .block_height_to_reward_cycle(stacks_tip_burn_block_height)
            .unwrap_or(0);

        let start_reward_cycle =
            stacks_tip_rc.saturating_sub(self.connection_opts.inv_reward_cycles);

        let rescan_rc = cmp::min(am_rescan_rc, start_reward_cycle);

        test_debug!(
            "begin blocks inv scan at {} = min({},{}) stacks_tip_am={} heaviest_am={}",
            rescan_rc,
            am_rescan_rc,
            start_reward_cycle,
            &self.stacks_tip_affirmation_map,
            &self.heaviest_affirmation_map
        );
        rescan_rc
    }

    /// Start requesting the next batch of PoX inventories
    fn inv_getpoxinv_begin(
        &mut self,
        pins: &mut HashSet<usize>,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &mut NeighborBlockStats,
        request_timeout: u64,
    ) -> Result<(), net_error> {
        let (target_pox_reward_cycle, getpoxinv) = match self
            .make_next_getpoxinv(sortdb, nk, stats)?
        {
            Some(x) => x,
            None => {
                // proceed to block scan
                let scan_start_rc = self.get_block_scan_start(sortdb);

                debug!("{:?}: cannot make any more GetPoxInv requests for {:?}; proceeding to block inventory scan at reward cycle {}", &self.local_peer, nk, scan_start_rc);
                stats.reset_block_scan(scan_start_rc);
                return Ok(());
            }
        };

        let payload = StacksMessageType::GetPoxInv(getpoxinv);
        let event_id_opt = self.get_event_id(nk);

        let message = self.sign_for_neighbor(nk, payload)?;
        let request = self
            .send_neighbor_message(nk, message, request_timeout)
            .inspect_err(|e| debug!("Failed to send GetPoxInv to {nk:?}: {e:?}"))?;

        stats.getpoxinv_begin(request, target_pox_reward_cycle);
        if let Some(event_id) = event_id_opt {
            pins.insert(event_id);
        }

        Ok(())
    }

    /// Finish requesting the next batch of PoX inventories
    /// Return true if done.
    fn inv_getpoxinv_try_finish(
        &mut self,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &mut NeighborBlockStats,
        ibd: bool,
    ) -> Result<bool, net_error> {
        if stats.done {
            return Ok(true);
        }
        if !stats.getpoxinv_try_finish(self)? {
            // try again
            return Ok(false);
        }

        assert_eq!(stats.state, InvWorkState::Done);

        if !stats.is_peer_online() {
            if stats.status == NodeStatus::Diverged {
                // remote node diverged from this node's view of the burnchain.
                // proceed to block download up to the reward cycles up to this one.
                stats.status = NodeStatus::Online;

                debug!("{:?}: Burnchain/PoX view diverged. Truncate inventories down to reward cycle {} for {:?}", &self.local_peer, stats.target_pox_reward_cycle, nk);
                stats
                    .inv
                    .truncate_pox_inventory(&self.burnchain, stats.target_pox_reward_cycle);
                stats
                    .inv
                    .truncate_block_inventories(&self.burnchain, stats.target_pox_reward_cycle);

                // proceed with block scan.
                // If we're in IBD, then this is an always-allowed peer and we should
                // react to divergences by deepening our rescan.
                let scan_start_rc = self.get_block_scan_start(sortdb);
                debug!(
                    "{:?}: proceeding to block inventory scan for {:?} (diverged) at reward cycle {} (ibd={})",
                    &self.local_peer, nk, scan_start_rc, ibd
                );

                stats.learned_data = true;
                stats.learned_data_height =
                    self.burnchain.reward_cycle_to_block_height(scan_start_rc);
                stats.reset_block_scan(scan_start_rc);
            }
            // done with pox inv sync
            return Ok(true);
        }

        let pox_inv = stats
            .pox_inv
            .take()
            .expect("BUG: finished getpoxinv without an error but got no poxinv");

        debug!(
            "{:?}: got PoxInv at reward cycle {} from {:?}: {:?}",
            &self.local_peer, stats.target_pox_reward_cycle, nk, &pox_inv
        );
        let lowest_learned_reward_cycle = stats.inv.merge_pox_inv(
            &self.burnchain,
            stats.target_pox_reward_cycle,
            pox_inv.bitlen as u64,
            pox_inv.pox_bitvec.clone(),
            true,
        );

        if let Some(lowest_learned_reward_cycle) = lowest_learned_reward_cycle.as_ref() {
            debug!(
                "{:?}: {:?} has learned about reward cycle {} (total {} reward cycles): {:?}",
                &self.local_peer,
                &nk,
                lowest_learned_reward_cycle,
                stats.inv.num_reward_cycles,
                &stats.inv
            );

            stats.learned_data = true;
            stats.learned_data_height = cmp::min(
                stats.learned_data_height,
                self.burnchain
                    .reward_cycle_to_block_height(*lowest_learned_reward_cycle),
            );
        } else {
            debug!(
                "{:?}: have {} total reward cycles for {:?}",
                &self.local_peer, stats.inv.num_reward_cycles, nk
            );
        }

        let remote_uncertain = NeighborBlockStats::check_remote_pox_inv_uncertainty(
            self,
            stats.target_pox_reward_cycle,
            &pox_inv,
        );
        let local_uncertain = NeighborBlockStats::check_local_pox_inv_uncertainty(
            self,
            stats.target_pox_reward_cycle,
            &pox_inv,
        );

        test_debug!(
            "{:?}: PoX bitlen = {}, remote-uncertain: {}, local-uncertain: {}",
            &self.local_peer,
            pox_inv.bitlen,
            remote_uncertain,
            local_uncertain
        );

        if stats.target_pox_reward_cycle >= (self.pox_id.num_inventory_reward_cycles() as u64) ||                                   // did full pass?
           remote_uncertain != (pox_inv.bitlen as u64) + stats.target_pox_reward_cycle ||                   // remote node is less certain than we are?
           local_uncertain != (pox_inv.bitlen as u64) + stats.target_pox_reward_cycle
        {
            // we are less certain than the remote node?
            if remote_uncertain != (pox_inv.bitlen as u64) + stats.target_pox_reward_cycle
                || local_uncertain != (pox_inv.bitlen as u64) + stats.target_pox_reward_cycle
            {
                // finished PoX scan -- we have found uncertainty in our neighbor, or we've
                // fully-synced.
                let minimum_certainty = cmp::min(remote_uncertain, local_uncertain);

                debug!(
                    "{:?}: Truncate inventories down to reward cycle {} for {:?}",
                    &self.local_peer, minimum_certainty, nk
                );
                stats
                    .inv
                    .truncate_pox_inventory(&self.burnchain, minimum_certainty);
                stats
                    .inv
                    .truncate_block_inventories(&self.burnchain, minimum_certainty);
            } else {
                debug!("{:?}: Sync'ed PoX inventory with {:?}, and it is equally certain up to reward cycle {}", &self.local_peer, nk, self.pox_id.num_inventory_reward_cycles());
            }

            // proceed to block scan.
            let scan_start = self.get_block_scan_start(sortdb);
            debug!(
                "{:?}: proceeding to block inventory scan for {:?} at reward cycle {}",
                &self.local_peer, nk, scan_start
            );
            stats.reset_block_scan(scan_start);
        } else {
            // continue with PoX scan.
            stats.pox_reward_cycle += pox_inv.bitlen as u64;
            stats.reset_pox_scan(stats.pox_reward_cycle);
        }

        Ok(true)
    }

    /// Start requesting the next batch of block inventories
    fn inv_getblocksinv_begin(
        &mut self,
        pins: &mut HashSet<usize>,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &mut NeighborBlockStats,
        request_timeout: u64,
    ) -> Result<(), net_error> {
        let (target_block_reward_cycle, getblocksinv) =
            match self.make_next_getblocksinv(sortdb, nk, stats)? {
                Some(x) => x,
                None => {
                    debug!(
                        "{:?}: finished inv sync with {}: could not make new GetBlocksInv",
                        &self.local_peer, &nk
                    );
                    stats.done = true;
                    return Ok(());
                }
            };

        let num_blocks_expected = getblocksinv.num_blocks;
        let payload = StacksMessageType::GetBlocksInv(getblocksinv);
        let event_id_opt = self.get_event_id(nk);
        let message = self.sign_for_neighbor(nk, payload)?;
        let request = self
            .send_neighbor_message(nk, message, request_timeout)
            .inspect_err(|e| debug!("Failed to send GetPoxInv to {nk:?}: {e:?}"))?;

        stats.getblocksinv_begin(request, target_block_reward_cycle, num_blocks_expected);
        if let Some(event_id) = event_id_opt {
            pins.insert(event_id);
        }
        Ok(())
    }

    /// Finish receiving the next batch of block inventories.
    /// Indicate whether or not we're done (true=continue, false=stop)
    fn inv_getblocksinv_try_finish(
        &mut self,
        nk: &NeighborKey,
        stats: &mut NeighborBlockStats,
        ibd: bool,
    ) -> Result<bool, net_error> {
        if stats.done {
            return Ok(true);
        }
        if !stats.getblocksinv_try_finish(self)? {
            return Ok(false);
        }
        if !stats.is_peer_online() {
            // done
            if ibd && stats.status == NodeStatus::Diverged {
                // we were in the initial block download, and we diverged.
                // we should try and deepen the scan.
                stats.block_reward_cycle = stats
                    .block_reward_cycle
                    .saturating_sub(self.connection_opts.inv_reward_cycles);
                let learned_data_height = self
                    .burnchain
                    .reward_cycle_to_block_height(stats.block_reward_cycle);

                debug!("{:?}: In initial block download and diverged from always-allowed peer -- schedule an ibd inventory sync for next time, starting at reward cycle {} ({}).", &self.local_peer, stats.block_reward_cycle, learned_data_height);
                stats.reset_block_scan(stats.block_reward_cycle);

                stats.learned_data = true;
                stats.learned_data_height = learned_data_height;
            }
            debug!(
                "{:?}: Node {} is diverged; done with inv sync",
                &self.local_peer, nk
            );
            stats.done = true;
            return Ok(false);
        }

        // if we get a blocksinv, then it means the remote peer still agrees with us on PoX state
        // (otherwise we would have been NACK'ed, and the peer would not be considered online)
        let blocks_inv = stats
            .blocks_inv
            .take()
            .expect("BUG: finished getblocksinv without an error but got no blocksinv");
        let target_block_height = self
            .burnchain
            .reward_cycle_to_block_height(stats.target_block_reward_cycle);

        debug!(
            "{:?}: got blocksinv at reward cycle {} (block height {}) from {:?}: {:?}",
            &self.local_peer, stats.target_block_reward_cycle, target_block_height, nk, &blocks_inv
        );
        let (new_blocks, new_microblocks) = stats.inv.merge_blocks_inv(
            target_block_height,
            blocks_inv.bitlen as u64,
            blocks_inv.block_bitvec,
            blocks_inv.microblocks_bitvec,
            true,
        );

        debug!("{:?}: {:?} has {} new blocks and {} new microblocks (total {} blocks, {} microblocks, {} sortitions): {:?}",
               &self.local_peer, &nk, new_blocks, new_microblocks, stats.inv.num_blocks(), stats.inv.num_microblock_streams(), stats.inv.num_sortitions, &stats.inv);

        if new_blocks > 0 || new_microblocks > 0 {
            stats.learned_data = true;
            stats.learned_data_height = cmp::min(target_block_height, stats.learned_data_height);
        }

        assert_eq!(stats.state, InvWorkState::Done);

        if stats.target_block_reward_cycle < self.pox_id.num_inventory_reward_cycles() as u64
            && stats.block_reward_cycle < self.pox_id.num_inventory_reward_cycles() as u64
        {
            // ask for more blocks
            stats.block_reward_cycle += 1;
            stats.reset_block_scan(stats.block_reward_cycle);
        } else {
            // we're done scanning!  proceed to rescan
            stats.last_rescan_timestamp = get_epoch_time_secs();
            debug!(
                "{:?}: finished inv sync with {}: reached remote chain tip",
                &self.local_peer, &nk
            );
            stats.done = true;
        }

        Ok(true)
    }

    /// Run a single state-machine to completion
    fn inv_sync_run(
        &mut self,
        pins: &mut HashSet<usize>,
        sortdb: &SortitionDB,
        nk: &NeighborKey,
        stats: &mut NeighborBlockStats,
        request_timeout: u64,
        ibd: bool,
    ) -> Result<bool, net_error> {
        while !stats.done {
            if !stats.is_peer_online() {
                debug!("{:?}: {:?} is not online", &self.local_peer, nk);
                stats.done = true;
                break;
            }

            debug!("Inv sync state is {:?}", &stats.state);
            let again = match stats.state {
                InvWorkState::GetPoxInvBegin => self
                    .inv_getpoxinv_begin(pins, sortdb, nk, stats, request_timeout)
                    .map(|_| true)?,
                InvWorkState::GetPoxInvFinish => {
                    self.inv_getpoxinv_try_finish(sortdb, nk, stats, ibd)?
                }
                InvWorkState::GetBlocksInvBegin => self
                    .inv_getblocksinv_begin(pins, sortdb, nk, stats, request_timeout)
                    .map(|_| true)?,
                InvWorkState::GetBlocksInvFinish => {
                    self.inv_getblocksinv_try_finish(nk, stats, ibd)?
                }
                InvWorkState::Done => {
                    stats.done = true;
                    false
                }
            };
            if !again {
                break;
            }
        }
        Ok(stats.done)
    }

    /// Refresh our cached PoX bitvector, and invalidate any PoX state if we have since learned
    /// about a new reward cycle.
    /// Call right after PeerNetwork::refresh_burnchain_view()
    pub fn refresh_sortition_view(&mut self, sortdb: &SortitionDB) -> Result<(), net_error> {
        if self.inv_state.is_none() {
            self.init_inv_sync_epoch2x(sortdb);
        }

        let inv_state = self
            .inv_state
            .as_mut()
            .expect("Unreachable: inv state not initialized");

        let (new_tip_sort_id, new_pox_id, reloaded) = {
            if self.burnchain_tip.sortition_id != self.tip_sort_id {
                // reloaded burnchain tip disagrees with our last-considered sortition tip
                let ic = sortdb.index_conn();
                let sortdb_reader =
                    SortitionHandleConn::open_reader(&ic, &self.burnchain_tip.sortition_id)?;
                (
                    self.burnchain_tip.sortition_id.clone(),
                    sortdb_reader.get_pox_id()?,
                    true,
                )
            } else {
                (self.tip_sort_id.clone(), self.pox_id.clone(), false)
            }
        };

        if reloaded {
            // find the lowest reward cycle whose bit has since changed from a 0 to a 1.
            let num_reward_cycles = cmp::min(
                new_pox_id.num_inventory_reward_cycles(),
                self.pox_id.num_inventory_reward_cycles(),
            );
            for i in 0..num_reward_cycles {
                if !self.pox_id.has_ith_anchor_block(i) && new_pox_id.has_ith_anchor_block(i) {
                    // we learned of a new anchor block intermittently.  Invalidate all cached state at and after this reward cycle.
                    inv_state.invalidate_block_inventories(&self.burnchain, i as u64);

                    // also clear block header cache (TODO: this is pessimistic -- only invalidated
                    // entries need to be cleared)
                    debug!(
                        "{:?}: invalidating block header cache in response to PoX bit flip",
                        &self.local_peer
                    );
                    self.header_cache.clear();
                    break;
                }
            }

            // if the PoX bitvector shrinks, then invalidate block inventories that are no longer represented
            if new_pox_id.num_inventory_reward_cycles() < self.pox_id.num_inventory_reward_cycles()
            {
                inv_state.invalidate_block_inventories(&self.burnchain, new_pox_id.len() as u64);
            }

            self.tip_sort_id = new_tip_sort_id;
            self.pox_id = new_pox_id;
        }

        debug!(
            "{:?}: PoX bit vector is {:?} (reloaded={})",
            &self.local_peer, &self.pox_id, reloaded
        );

        Ok(())
    }

    /// Drive all state machines.
    /// returns (done?, throttled?, peers-to-disconnect, peers-that-are-dead)
    pub fn sync_inventories_epoch2x(
        &mut self,
        sortdb: &SortitionDB,
        ibd: bool,
    ) -> (bool, bool, Vec<NeighborKey>, Vec<NeighborKey>) {
        PeerNetwork::with_inv_state(self, |network, inv_state| {
            debug!(
                "{:?}: Inventory state has {} block stats tracked on connections {:?}",
                &network.local_peer,
                inv_state.block_stats.len(),
                inv_state.pinned,
            );

            let mut all_done = true;
            let mut ibd_diverged_height: Option<u64> = None;

            let bootstrap_peers: HashSet<_> =
                PeerDB::get_bootstrap_peers(network.peerdb.conn(), network.local_peer.network_id)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|neighbor| neighbor.addr)
                    .collect();

            if !ibd
                && !inv_state.hint_do_rescan
                && !inv_state.hint_learned_data
                && inv_state.last_rescanned_at + inv_state.sync_interval >= get_epoch_time_secs()
            {
                // we didn't learn anything on the last sync, and it hasn't been enough time
                // since the last sync for us to do it again
                debug!(
                    "{:?}: Throttle inv sync until {}s",
                    &network.local_peer,
                    inv_state.last_rescanned_at + inv_state.sync_interval
                );
                return (true, true, vec![], vec![]);
            }

            let mut new_pins = HashSet::new();
            for (nk, stats) in inv_state.block_stats.iter_mut() {
                debug!(
                    "{:?}: inv state-machine for {:?} is in state {:?}, at PoX {},target={}; blocks {},target={}; status {:?}, done={}",
                    &network.local_peer,
                    nk,
                    &stats.state,
                    stats.pox_reward_cycle,
                    stats.target_pox_reward_cycle,
                    stats.block_reward_cycle,
                    stats.target_block_reward_cycle,
                    stats.status,
                    stats.done
                );
                if !stats.done {
                    match network.inv_sync_run(&mut new_pins, sortdb, nk, stats, inv_state.request_timeout, ibd) {
                        Ok(_) => {}
                        Err(net_error::StaleView) => {
                            // stop work on this state machine -- it needs to be restarted.
                            // we'll need to keep scanning.
                            debug!("{:?}: stale PoX view; will rescan", &network.local_peer);
                            stats.done = true;
                            inv_state.hint_learned_data = true;
                            inv_state.hint_learned_data_height = u64::MAX;
                        }
                        Err(net_error::PeerNotConnected) | Err(net_error::SendError(..)) => {
                            stats.status = NodeStatus::Dead;
                        }
                        Err(e) => {
                            debug!(
                                "{:?}: remote neighbor inv_sync_run finished with error {e:?}",
                                &network.local_peer
                            );
                            stats.status = NodeStatus::Broken;
                        }
                    };

                    all_done = all_done && stats.done;
                    if stats.learned_data {
                        // if this node diverged from us, and we're in ibd, and this is an
                        // always-allowed peer, then start scanning here (or lower)
                        if ibd
                            && bootstrap_peers.contains(nk)
                            && stats.status == NodeStatus::Diverged
                        {
                            inv_state.last_change_at = get_epoch_time_secs();
                            inv_state.hint_learned_data = true;
                            inv_state.hint_learned_data_height = cmp::min(
                                inv_state.hint_learned_data_height,
                                stats.learned_data_height,
                            );

                            // this will be where sortitions must begin
                            ibd_diverged_height = Some(inv_state.hint_learned_data_height);

                            debug!("{:?}: remote neighbor {:?} diverged (at {}), so try re-scanning at height {}", &network.local_peer, &nk, stats.learned_data_height, inv_state.hint_learned_data_height);
                        } else {
                            debug!(
                                "{:?}: learned to scan from {:?} at height {}",
                                &network.local_peer, &nk, stats.learned_data_height
                            );
                        }
                    }

                    if stats.done
                        && stats.inv.num_reward_cycles
                            >= network.pox_id.num_inventory_reward_cycles() as u64
                    {
                        debug!(
                            "{:?}: synchronized {} >= {} reward cycles for {:?}",
                            &network.local_peer,
                            stats.inv.num_reward_cycles,
                            network.pox_id.num_inventory_reward_cycles(),
                            &nk
                        );
                    }
                }
            }
            let _ = new_pins
                .into_iter()
                .map(|event_id| inv_state.pin_connection(event_id));

            if all_done {
                let mut new_sync_peers = network.get_outbound_sync_peers();
                let broken_peers = inv_state.get_broken_peers();
                let dead_peers = inv_state.get_dead_peers();

                // hint to downloader as to where to begin scanning next time
                inv_state.block_sortition_start = ibd_diverged_height
                    .unwrap_or(network.burnchain.reward_cycle_to_block_height(
                        network.get_block_scan_start(
                            sortdb,
                        ),
                    ))
                    .saturating_sub(sortdb.first_block_height);

                debug!(
                    "{:?}: inventory sync finished; sortition start is {}",
                    &network.local_peer, inv_state.block_sortition_start,
                );

                if !inv_state.hint_learned_data && !inv_state.block_stats.is_empty() {
                    // did a full scan without learning anything new
                    inv_state.last_rescanned_at = get_epoch_time_secs();
                    inv_state.hint_do_rescan = false;
                    inv_state.num_inv_syncs += 1;

                    debug!(
                        "{:?}: inv sync finished, learned nothing new from {:?} neighbors",
                        &network.local_peer,
                        &inv_state.block_stats.len();
                        "ibd" => %ibd,
                        "num_inv_syncs" => %inv_state.num_inv_syncs,
                        "num_sync_neighbors" => &inv_state.block_stats.len()
                    );
                } else {
                    // keep learning
                    inv_state.hint_learned_data = false;
                    inv_state.hint_learned_data_height = u64::MAX;
                    inv_state.hint_do_rescan = true;

                    debug!(
                        "{:?}: inv sync finished, learned something new (have {} inv states)",
                        &network.local_peer,
                        inv_state.block_stats.len();
                        "ibd" => %ibd,
                        "num_inv_syncs" => %inv_state.num_inv_syncs,
                        "num_sync_neighbors" => &inv_state.block_stats.len()
                    );
                }

                let bad_peers = inv_state.cull_bad_peers();
                for bad_peer in bad_peers {
                    info!(
                        "{:?}: will no longer track inventory of bad peer {:?}",
                        &network.local_peer, &bad_peer
                    );
                    new_sync_peers.remove(&bad_peer);
                }
                for dead_peer in dead_peers.iter() {
                    info!(
                        "{:?}: will no longer track inventory of dead peer {:?}",
                        &network.local_peer, &dead_peer
                    );
                    new_sync_peers.remove(dead_peer);
                }

                // pick good candidates at random
                let mut random_neighbor_list: Vec<_> = new_sync_peers.into_iter().collect();
                random_neighbor_list.shuffle(&mut thread_rng());

                // always pick permanently-allowed peers
                let mut good_sync_peers_set = HashSet::new();
                let mut random_sync_peers_list = vec![];
                for nk in random_neighbor_list.into_iter() {
                    if bootstrap_peers.contains(&nk)
                        && good_sync_peers_set.len()
                            < (network.connection_opts.num_neighbors as usize)
                    {
                        debug!("{:?}: good sync peer {:?}", &network.local_peer, &nk);
                        good_sync_peers_set.insert(nk);
                    } else {
                        debug!("{:?}: random sync peer {:?}", &network.local_peer, &nk);
                        random_sync_peers_list.push(nk);
                    }
                }

                if !ibd {
                    // not in initial-block download, so we can add random neighbors as well
                    let num_good_peers = good_sync_peers_set.len();
                    for i in 0..cmp::min(
                        random_sync_peers_list.len(),
                        (network.connection_opts.num_neighbors as usize)
                            .saturating_sub(num_good_peers),
                    ) {
                        good_sync_peers_set.insert(random_sync_peers_list[i].clone());
                    }
                } else {
                    // make *sure* this list isn't empty
                    for bootstrap_peer in bootstrap_peers.iter() {
                        good_sync_peers_set.insert(bootstrap_peer.clone());
                    }
                    debug!(
                        "{:?}: in initial block download; only inv-sync with {} always-allowed peers",
                        &network.local_peer,
                        good_sync_peers_set.len()
                    );
                }

                inv_state.reset_sync_peers(
                    network,
                    good_sync_peers_set,
                    &bootstrap_peers,
                    network.connection_opts.num_neighbors as usize,
                );

                (true, false, broken_peers, dead_peers)
            } else {
                (false, false, vec![], vec![])
            }
        })
        .expect("FATAL: network not connected")
    }

    pub fn with_inv_state<F, R>(network: &mut PeerNetwork, handler: F) -> Result<R, net_error>
    where
        F: FnOnce(&mut PeerNetwork, &mut InvState) -> R,
    {
        let mut inv_state = network.inv_state.take();
        let res = match inv_state {
            None => {
                test_debug!("{:?}: inv state not connected", &network.local_peer);
                Err(net_error::NotConnected)
            }
            Some(ref mut invs) => Ok(handler(network, invs)),
        };
        network.inv_state = inv_state;
        res
    }

    /// Get a list of outbound neighbors we can sync with.
    pub fn get_outbound_sync_peers(&self) -> HashSet<NeighborKey> {
        let mut cur_neighbors = HashSet::new();
        for (nk, event_id) in self.events.iter() {
            // only outbound authenticated peers
            if let Some(convo) = self.peers.get(event_id) {
                if convo.is_outbound() && convo.is_authenticated() {
                    cur_neighbors.insert(nk.clone());
                }
            }
        }

        debug!(
            "{:?}: Sampled {} outbound sync peers",
            &self.local_peer,
            cur_neighbors.len()
        );
        cur_neighbors
    }

    /// Set a hint that we learned something new, and need to sync invs again
    pub fn hint_sync_invs(&mut self, target_height: u64) {
        if let Some(ref mut inv_state) = self.inv_state {
            debug!(
                "Awaken inv sync to re-scan peer block inventories at height {}",
                target_height
            );
            inv_state.hint_learned_data = true;
            inv_state.hint_do_rescan = true;
            inv_state.hint_learned_data_height = target_height;
        }
    }

    /// Initialize inv state
    pub fn init_inv_sync_epoch2x(&mut self, sortdb: &SortitionDB) {
        // find out who we'll be synchronizing with for the duration of this inv sync
        debug!(
            "{:?}: Initializing peer block inventory state",
            &self.local_peer,
        );
        self.inv_state = Some(InvState::new(
            sortdb.first_block_height,
            self.connection_opts.timeout,
            self.connection_opts.inv_sync_interval,
        ));
    }

    /// Run a function over a given neighbor's inventory
    pub fn with_neighbor_blocks_inv<F, R>(
        &mut self,
        nk: &NeighborKey,
        func: F,
    ) -> Result<R, net_error>
    where
        F: FnOnce(&mut PeerNetwork, &mut NeighborBlockStats) -> R,
    {
        match PeerNetwork::with_inv_state(self, |network, inv_state| {
            if let Some(nstats) = inv_state.block_stats.get_mut(nk) {
                Ok(func(network, nstats))
            } else {
                Err(net_error::PeerNotConnected)
            }
        }) {
            Ok(Ok(x)) => Ok(x),
            Ok(Err(x)) => Err(x),
            Err(x) => Err(x),
        }
    }

    /// Get the local block inventory for a reward cycle
    pub fn get_local_blocks_inv(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        reward_cycle: u64,
    ) -> Result<BlocksInvData, net_error> {
        let target_block_height = self.burnchain.reward_cycle_to_block_height(reward_cycle);

        // if this succeeds, then we should be able to make a BlocksInv
        let ancestor_sn = self
            .get_ancestor_sortition_snapshot(sortdb, target_block_height)
            .inspect_err(|e| {
                debug!( "Failed to load ancestor sortition snapshot at height {target_block_height}: {e:?}")
            })?;

        let tip_sn = self
            .get_tip_sortition_snapshot(sortdb)
            .inspect_err(|e| debug!("Failed to load tip sortition snapshot: {e:?}"))?;

        let getblocksinv = GetBlocksInv {
            consensus_hash: ancestor_sn.consensus_hash,
            num_blocks: cmp::min(
                tip_sn.block_height.saturating_sub(ancestor_sn.block_height) + 1,
                self.burnchain.pox_constants.reward_cycle_length as u64,
            ) as u16,
        };

        test_debug!(
            "{:?}: self-requesting {:?}",
            &self.local_peer,
            &getblocksinv
        );

        let blocks_inv =
            ConversationP2P::make_getblocksinv_response(self, sortdb, chainstate, &getblocksinv)
                .inspect_err(|e| {
                    debug!(
                "Failed to load blocks inventory at reward cycle {reward_cycle} ({:?}): {e:?}",
                &ancestor_sn.consensus_hash
            );
                })?;

        match blocks_inv {
            StacksMessageType::BlocksInv(blocks_inv) => {
                return Ok(blocks_inv);
            }
            _ => {
                debug!("Failed to produce blocks inventory; got {:?}", &blocks_inv);
                return Err(net_error::NotFoundError);
            }
        }
    }

    /// Update the state of our neighbors' epoch 2.x block inventories.
    /// Return (finished?, throttled?)
    fn do_network_inv_sync_epoch2x(&mut self, sortdb: &SortitionDB, ibd: bool) -> (bool, bool) {
        if cfg!(test) && self.connection_opts.disable_inv_sync {
            test_debug!("{:?}: inv sync is disabled", &self.local_peer);
            return (true, false);
        }

        debug!(
            "{:?}: network inventory sync for epoch 2.x",
            &self.local_peer
        );

        if self.inv_state.is_none() {
            self.init_inv_sync_epoch2x(sortdb);
        }

        // synchronize peer block inventories
        let (done, throttled, broken_neighbors, dead_neighbors) =
            self.sync_inventories_epoch2x(sortdb, ibd);

        // disconnect and ban broken peers
        for broken in broken_neighbors.into_iter() {
            //substantial changes to the epoch2x sync would be required to get further detail about why the connection was broken. Just use "Unknown" for now.
            self.deregister_and_ban_neighbor(
                &broken,
                DropReason::BrokenConnection("Unknown".into()),
                DropSource::Epoch2xInventorySync,
            );
        }

        // disconnect from dead connections
        for dead in dead_neighbors.into_iter() {
            //substantial changes to the epoch2x sync would be required to get further detail about why the connection is dead. Just use "Unknown" for now.
            self.deregister_neighbor(
                &dead,
                DropReason::DeadConnection("Unknown".into()),
                DropSource::Epoch2xInventorySync,
            );
        }

        (done, throttled)
    }

    /// Check to see if an epcoh2x peer has fully sync'ed.
    /// (has crate visibility for testing)
    pub(crate) fn check_peer_epoch2x_synced(
        &self,
        ibd: bool,
        num_reward_cycles_synced: u64,
    ) -> bool {
        // either not in IBD, and we've sync'ed the highest reward cycle in the PoX vector,
        // OR,
        // in IBD, and we've sync'ed up to the highest sortition's reward cycle.
        //
        // The difference is that in the former case, the PoX inventory vector will be as long as
        // the sortition history, but the number of reward cycles tracked by the inv state machine
        // may be less when the node is booting up.  So, we preface that check by also checking
        // that we're in steady-state mode (i.e. not IBD).
        (!ibd && num_reward_cycles_synced >= self.pox_id.num_inventory_reward_cycles() as u64)
            || (ibd
                && num_reward_cycles_synced
                    >= self
                        .burnchain
                        .block_height_to_reward_cycle(self.burnchain_tip.block_height)
                        .expect("FATAL: sortition has no reward cycle"))
    }

    /// Check to see if an always-allowed peer has performed an epoch 2.x inventory sync
    fn check_always_allowed_peer_inv_sync_epoch2x(&self, ibd: bool) -> bool {
        // only count an inv_sync as passing if there's an always-allowed node
        // in our inv state
        let always_allowed: HashSet<_> =
            PeerDB::get_always_allowed_peers(self.peerdb.conn(), self.local_peer.network_id)
                .unwrap_or_default()
                .into_iter()
                .map(|neighbor| neighbor.addr)
                .collect();

        // have we finished a full pass of the inventory state machine on an
        // always-allowed peer?
        let mut finished_always_allowed_inv_sync = false;

        if always_allowed.is_empty() {
            // vacuously, we are done so we can return
            return true;
        }

        // do we have an always-allowed peer that we have not fully synced
        // with?
        let mut have_unsynced = false;
        let Some(ref inv_state) = self.inv_state else {
            return true;
        };

        for (nk, stats) in inv_state.block_stats.iter() {
            if self.is_bound(nk) {
                // this is the same address we're bound to
                continue;
            }
            if Some((nk.addrbytes.clone(), nk.port)) == self.local_peer.public_ip_address {
                // this is a peer at our address
                continue;
            }
            if !always_allowed.contains(nk) {
                // this peer isn't in the always-allowed set
                continue;
            }

            if self.check_peer_epoch2x_synced(ibd, stats.inv.num_reward_cycles) {
                // we have fully sync'ed with an always-allowed peer
                debug!(
                    "{:?}: Fully-sync'ed PoX inventory from {}",
                    self.get_local_peer(),
                    nk,
                );
                finished_always_allowed_inv_sync = true;
            } else {
                // there exists an always-allowed peer that we have not
                // fully sync'ed with
                debug!(
                    "{:?}: Have not fully sync'ed with {}",
                    self.get_local_peer(),
                    nk,
                );
                have_unsynced = true;
            }
        }

        if !have_unsynced {
            // There exists one or more always-allowed peers in
            // the inv state machine (per the peer DB), but all such peers
            // report either our bind address or our public IP address.
            // If this is the case (i.e. a configuration error, a weird
            // case where nodes share an IP, etc), then we declare this inv
            // sync pass as finished.
            finished_always_allowed_inv_sync = true;
        }

        finished_always_allowed_inv_sync
    }

    /// Do an inventory state machine pass for epoch 2.x.
    /// Returns the new work state  
    pub fn work_inv_sync_epoch2x(
        &mut self,
        sortdb: &SortitionDB,
        download_backpressure: bool,
        ibd: bool,
    ) -> PeerNetworkWorkState {
        // synchronize epcoh 2.x peer block inventories
        let (inv_done, inv_throttled) = self.do_network_inv_sync_epoch2x(sortdb, ibd);
        if !inv_done {
            // inventory sync isn't finished, so don't change work state
            return PeerNetworkWorkState::BlockInvSync;
        }

        let work_state = if !download_backpressure {
            // proceed to get blocks, if we're not backpressured
            PeerNetworkWorkState::BlockDownload
        } else {
            // skip downloads for now
            PeerNetworkWorkState::Prune
        };

        if inv_throttled {
            // nothing to do
            return work_state;
        }

        let finished_always_allowed_inv_sync = self.check_always_allowed_peer_inv_sync_epoch2x(ibd);
        if finished_always_allowed_inv_sync {
            debug!(
                "{:?}: synchronized inventories with at least one always-allowed peer",
                &self.local_peer
            );
            self.num_inv_sync_passes += 1;
        } else {
            debug!(
                "{:?}: did NOT synchronize inventories with at least one always-allowed peer",
                &self.local_peer
            );
        }
        debug!(
            "{:?}: Finished full inventory state-machine pass ({})",
            self.get_local_peer(),
            self.num_inv_sync_passes
        );

        // hint to the downloader to start scanning at the sortition
        // height we just synchronized
        let start_download_sortition = if let Some(ref inv_state) = self.inv_state {
            let (consensus_hash, _) = SortitionDB::get_canonical_stacks_chain_tip_hash(
                sortdb.conn(),
            )
            .expect("FATAL: failed to load canonical stacks chain tip hash from sortition DB");
            let stacks_tip_sortition_height =
                SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &consensus_hash)
                    .expect("FATAL: failed to query sortition DB")
                    .map(|sn| sn.block_height)
                    .unwrap_or(self.burnchain.first_block_height)
                    .saturating_sub(self.burnchain.first_block_height);

            let sortition_height_start =
                cmp::min(stacks_tip_sortition_height, inv_state.block_sortition_start);

            debug!(
                "{:?}: Begin downloader synchronization at sortition height {} min({},{})",
                &self.local_peer,
                sortition_height_start,
                inv_state.block_sortition_start,
                stacks_tip_sortition_height
            );

            sortition_height_start
        } else {
            // really unreachable, but why tempt fate?
            warn!(
                "{:?}: Inventory state machine not yet initialized",
                &self.local_peer
            );
            0
        };

        if let Some(ref mut downloader) = self.block_downloader {
            debug!(
                "{:?}: wake up downloader at sortition height {}",
                &self.local_peer, start_download_sortition
            );
            downloader.hint_block_sortition_height_available(start_download_sortition, ibd, false);
            downloader.hint_microblock_sortition_height_available(
                start_download_sortition,
                ibd,
                false,
            );
        } else {
            warn!(
                "{:?}: Block downloader not yet initialized",
                &self.local_peer
            );
        }
        work_state
    }
}

#[cfg(test)]
mod test {}
