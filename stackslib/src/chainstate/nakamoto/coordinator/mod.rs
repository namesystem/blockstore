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

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use clarity::boot_util::boot_code_id;
use clarity::vm::ast::ASTRules;
use clarity::vm::clarity::ClarityConnection;
use clarity::vm::database::{BurnStateDB, HeadersDB};
use clarity::vm::types::PrincipalData;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, SortitionId, StacksAddress, StacksBlockId,
    StacksPrivateKey, StacksPublicKey,
};
use stacks_common::types::{StacksEpoch, StacksEpochId};

use crate::burnchains::db::{BurnchainBlockData, BurnchainDB, BurnchainHeaderReader};
use crate::burnchains::{self, burnchain, Burnchain, BurnchainBlockHeader};
use crate::chainstate::burn::db::sortdb::{
    get_ancestor_sort_id, SortitionDB, SortitionHandle, SortitionHandleConn,
};
use crate::chainstate::burn::operations::leader_block_commit::RewardSetInfo;
use crate::chainstate::burn::BlockSnapshot;
use crate::chainstate::coordinator::comm::{
    CoordinatorChannels, CoordinatorCommunication, CoordinatorEvents, CoordinatorNotices,
    CoordinatorReceivers,
};
use crate::chainstate::coordinator::{
    calculate_paid_rewards, dispatcher_announce_burn_ops, BlockEventDispatcher, ChainsCoordinator,
    Error, OnChainRewardSetProvider, PaidRewards, PoxAnchorBlockStatus, RewardCycleInfo,
    RewardSetProvider,
};
use crate::chainstate::nakamoto::NakamotoChainState;
use crate::chainstate::stacks::boot::{RewardSet, SIGNERS_NAME};
use crate::chainstate::stacks::db::{
    StacksBlockHeaderTypes, StacksChainState, StacksDBConn, StacksHeaderInfo,
};
use crate::chainstate::stacks::index::marf::MarfConnection;
use crate::chainstate::stacks::miner::{signal_mining_blocked, signal_mining_ready, MinerStatus};
use crate::chainstate::stacks::Error as ChainstateError;
use crate::clarity_vm::database::HeadersDBConn;
use crate::cost_estimates::{CostEstimator, FeeEstimator};
use crate::monitoring::increment_stx_blocks_processed_counter;
use crate::net::Error as NetError;
use crate::util_lib::db::Error as DBError;

#[cfg(any(test, feature = "testing"))]
pub static TEST_COORDINATOR_STALL: std::sync::Mutex<Option<bool>> = std::sync::Mutex::new(None);

#[cfg(test)]
pub mod tests;

macro_rules! err_or_debug {
    ($debug_bool:expr, $($arg:tt)*) => ({
        if $debug_bool {
            debug!($($arg)*)
        } else {
            error!($($arg)*)
        }
    })
}

macro_rules! inf_or_debug {
    ($debug_bool:expr, $($arg:tt)*) => ({
        if $debug_bool {
            debug!($($arg)*)
        } else {
            info!($($arg)*)
        }
    })
}

impl<T: BlockEventDispatcher> OnChainRewardSetProvider<'_, T> {
    /// Read a reward_set written while updating .signers
    /// `debug_log` should be set to true if the reward set loading should
    ///  log messages as `debug!` instead of `error!` or `info!`. This allows
    ///  RPC endpoints to expose this without flooding loggers.
    pub fn read_reward_set_nakamoto(
        &self,
        chainstate: &mut StacksChainState,
        cycle: u64,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
        debug_log: bool,
    ) -> Result<RewardSet, Error> {
        self.read_reward_set_nakamoto_of_cycle(cycle, chainstate, sortdb, block_id, debug_log)
    }

    /// Read a reward_set written while updating .signers at a given cycle_id
    /// `debug_log` should be set to true if the reward set loading should
    ///  log messages as `debug!` instead of `error!` or `info!`. This allows
    ///  RPC endpoints to expose this without flooding loggers.
    pub fn read_reward_set_nakamoto_of_cycle(
        &self,
        cycle: u64,
        chainstate: &mut StacksChainState,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
        debug_log: bool,
    ) -> Result<RewardSet, Error> {
        // figure out the block ID
        let Some(coinbase_height_of_calculation) = chainstate
            .eval_boot_code_read_only(
                sortdb,
                block_id,
                SIGNERS_NAME,
                &format!("(map-get? cycle-set-height u{})", cycle),
            )?
            .expect_optional()
            .map_err(|e| Error::ChainstateError(e.into()))?
            .map(|x| {
                let as_u128 = x.expect_u128()?;
                Ok(u64::try_from(as_u128).expect("FATAL: block height exceeded u64"))
            })
            .transpose()
            .map_err(|e| Error::ChainstateError(ChainstateError::ClarityError(e)))?
        else {
            err_or_debug!(
                debug_log,
                "The reward set was not written to .signers before it was needed by Nakamoto";
                "cycle_number" => cycle,
            );
            return Err(Error::PoXAnchorBlockRequired);
        };

        self.read_reward_set_at_calculated_block(
            coinbase_height_of_calculation,
            chainstate,
            block_id,
            debug_log,
        )
    }

    pub fn get_height_of_pox_calculation(
        &self,
        cycle: u64,
        chainstate: &mut StacksChainState,
        sort_handle: &SortitionHandleConn,
        block_id: &StacksBlockId,
    ) -> Result<u64, Error> {
        let ro_index = chainstate.state_index.reopen_readonly()?;
        let headers_db = HeadersDBConn(StacksDBConn::new(&ro_index, ()));
        let Some(coinbase_height_of_calculation) = chainstate
            .clarity_state
            .eval_read_only(
                block_id,
                &headers_db,
                sort_handle,
                &boot_code_id(SIGNERS_NAME, chainstate.mainnet),
                &format!("(map-get? cycle-set-height u{})", cycle),
                ASTRules::PrecheckSize,
            )
            .map_err(ChainstateError::ClarityError)?
            .expect_optional()
            .map_err(|e| Error::ChainstateError(e.into()))?
            .map(|x| {
                let as_u128 = x.expect_u128()?;
                Ok(u64::try_from(as_u128).expect("FATAL: block height exceeded u64"))
            })
            .transpose()
            .map_err(|e| Error::ChainstateError(ChainstateError::ClarityError(e)))?
        else {
            error!(
                "The reward set was not written to .signers before it was needed by Nakamoto";
                "cycle_number" => cycle,
            );
            return Err(Error::PoXAnchorBlockRequired);
        };
        Ok(coinbase_height_of_calculation)
    }

    pub fn read_reward_set_at_calculated_block(
        &self,
        coinbase_height_of_calculation: u64,
        chainstate: &mut StacksChainState,
        block_id: &StacksBlockId,
        debug_log: bool,
    ) -> Result<RewardSet, Error> {
        let Some(reward_set_block) = NakamotoChainState::get_header_by_coinbase_height(
            &mut chainstate.index_conn(),
            block_id,
            coinbase_height_of_calculation,
        )?
        else {
            err_or_debug!(
                debug_log,
                "Failed to find the block in which .signers was written"
            );
            return Err(Error::PoXAnchorBlockRequired);
        };

        let Some(reward_set) = NakamotoChainState::get_reward_set(
            chainstate.db(),
            &reward_set_block.index_block_hash(),
        )?
        else {
            err_or_debug!(
                debug_log,
                "No reward set stored at the block in which .signers was written";
                "checked_block" => %reward_set_block.index_block_hash(),
                "coinbase_height_of_calculation" => coinbase_height_of_calculation,
            );
            return Err(Error::PoXAnchorBlockRequired);
        };

        // This method should only ever called if the current reward cycle is a nakamoto reward cycle
        //  (i.e., its reward set is fetched for determining signer sets (and therefore agg keys).
        //  Non participation is fatal.
        if reward_set.rewarded_addresses.is_empty() {
            // no one is stacking
            err_or_debug!(debug_log, "No PoX participation");
            return Err(Error::PoXAnchorBlockRequired);
        }

        inf_or_debug!(
            debug_log,
            "PoX reward set loaded from written block state";
            "reward_set_block_id" => %reward_set_block.index_block_hash(),
            "burn_block_hash" => %reward_set_block.burn_header_hash,
            "stacks_block_height" => reward_set_block.stacks_block_height,
            "burn_header_height" => reward_set_block.burn_header_height,
        );

        if reward_set.signers.is_none() {
            err_or_debug!(
                debug_log,
                "FATAL: PoX reward set did not specify signer set in Nakamoto"
            );
            return Err(Error::PoXAnchorBlockRequired);
        }

        Ok(reward_set)
    }
}

/// Find the ordered sequence of sortitions from a given burnchain block back to the start of
/// the burnchain block's reward cycle's prepare phase.  If the burnchain block is not in a prepare
/// phase, then the returned list is empty.  If the burnchain block is in a prepare phase, then all
/// consensus hashes back to the first block in the prepare phase are loaded and returned in
/// ascending height order.
fn find_prepare_phase_sortitions(
    sort_db: &SortitionDB,
    burnchain: &Burnchain,
    sortition_tip: &SortitionId,
) -> Result<Vec<BlockSnapshot>, Error> {
    let mut prepare_phase_sn = SortitionDB::get_block_snapshot(sort_db.conn(), sortition_tip)?
        .ok_or(DBError::NotFoundError)?;

    let mut height = prepare_phase_sn.block_height;
    let mut sns = vec![];

    while burnchain.is_in_prepare_phase(height) && height > 0 {
        let parent_sortition_id = prepare_phase_sn.parent_sortition_id;
        sns.push(prepare_phase_sn);
        let Some(sn) = SortitionDB::get_block_snapshot(sort_db.conn(), &parent_sortition_id)?
        else {
            break;
        };
        prepare_phase_sn = sn;
        height = height.saturating_sub(1);
    }

    sns.reverse();
    Ok(sns)
}

/// Try to get the reward cycle information for a Nakamoto reward cycle, identified by the
/// `reward_cycle` number.
///
/// `sortition_tip` can be any sortition ID that's at a higher height than
/// `reward_cycle`'s start height (the 0 block).
///
/// In Nakamoto, the PoX anchor block for reward cycle _R_ is the _first_ Stacks block mined in the
/// _last_ tenure of _R - 1_'s reward phase (i.e. which takes place toward the end of reward cycle).
/// The reason it must be this way is because its hash will be in the block-commit for the first
/// prepare-phase tenure of cycle _R_ (which is required for the PoX ancestry query in the
/// block-commit validation logic).
///
/// If this method returns None, the caller should try again when there are more Stacks blocks.  In
/// Nakamoto, every reward cycle _must_ have a PoX anchor block; otherwise, the chain halts.
///
/// Returns Ok(Some(reward-cycle-info)) if we found the first sortition in the prepare phase.
/// Returns Ok(None) if we're still waiting for the PoX anchor block sortition
/// Returns Err(Error::NotInPreparePhase) if `burn_height` is not in the prepare phase
pub fn get_nakamoto_reward_cycle_info<U: RewardSetProvider>(
    sortition_tip: &SortitionId,
    reward_cycle: u64,
    burnchain: &Burnchain,
    chain_state: &mut StacksChainState,
    stacks_tip: &StacksBlockId,
    sort_db: &mut SortitionDB,
    provider: &U,
) -> Result<Option<RewardCycleInfo>, Error> {
    let burn_height = burnchain.nakamoto_first_block_of_cycle(reward_cycle);

    let epoch_at_height = SortitionDB::get_stacks_epoch(sort_db.conn(), burn_height)?
        .unwrap_or_else(|| panic!("FATAL: no epoch defined for burn height {}", burn_height))
        .epoch_id;

    assert!(
        epoch_at_height >= StacksEpochId::Epoch25,
        "FATAL: called a nakamoto function outside of epoch 3"
    );

    debug!("Processing reward set for Nakamoto reward cycle";
          "stacks_tip" => %stacks_tip,
          "reward_cycle" => reward_cycle,
          "reward_cycle_length" => burnchain.pox_constants.reward_cycle_length,
          "prepare_phase_length" => burnchain.pox_constants.prepare_length);

    let Some((rc_info, anchor_block_header)) = load_nakamoto_reward_set(
        reward_cycle,
        sortition_tip,
        burnchain,
        chain_state,
        stacks_tip,
        sort_db,
        provider,
    )?
    else {
        return Ok(None);
    };

    let block_id = match anchor_block_header.anchored_header {
        StacksBlockHeaderTypes::Epoch2(..) => anchor_block_header.index_block_hash(),
        StacksBlockHeaderTypes::Nakamoto(ref header) => header.block_id(),
    };

    info!(
        "Anchor block selected";
        "cycle" => reward_cycle,
        "block_id" => %block_id,
        "consensus_hash" => %anchor_block_header.consensus_hash,
        "burn_height" => anchor_block_header.burn_header_height,
        "stacks_block_height" => anchor_block_header.stacks_block_height,
        "burn_block_hash" => %anchor_block_header.burn_header_hash
    );

    return Ok(Some(rc_info));
}

/// Helper to get the Nakamoto reward set for a given reward cycle, identified by `reward_cycle`.
///
/// In all but the first Nakamoto reward cycle, this will load up the stored reward set from the
/// Nakamoto chain state.  In the first Nakamoto reward cycle, where the reward set is computed
/// from epoch2 state, the reward set will be loaded from the sortition DB (which is the only place
/// it will be stored).
///
/// Returns Ok(Some((reward set info, PoX anchor block header))) on success
/// Returns Ok(None) if the reward set is not yet known, but could be known by the time a
/// subsequent call is made.
pub fn load_nakamoto_reward_set<U: RewardSetProvider>(
    reward_cycle: u64,
    sortition_tip: &SortitionId,
    burnchain: &Burnchain,
    chain_state: &mut StacksChainState,
    stacks_tip: &StacksBlockId,
    sort_db: &SortitionDB,
    provider: &U,
) -> Result<Option<(RewardCycleInfo, StacksHeaderInfo)>, Error> {
    let cycle_start_height = burnchain.nakamoto_first_block_of_cycle(reward_cycle);

    let epoch_at_height = SortitionDB::get_stacks_epoch(sort_db.conn(), cycle_start_height)?
        .unwrap_or_else(|| {
            panic!(
                "FATAL: no epoch defined for burn height {}",
                cycle_start_height
            )
        });

    // Find the first Stacks block in this reward cycle's preceding prepare phase.
    // This block will have invoked `.signers.stackerdb-set-signer-slots()` with the reward set.
    // Note that we may not have processed it yet. But, if we do find it, then it's
    // unique (and since Nakamoto Stacks blocks are processed in order, the anchor block
    // cannot change later).
    let first_epoch30_reward_cycle = burnchain
        .block_height_to_reward_cycle(epoch_at_height.start_height)
        .expect("FATAL: no reward cycle for epoch 3.0 start height");

    if !epoch_at_height
        .epoch_id
        .uses_nakamoto_reward_set(reward_cycle, first_epoch30_reward_cycle)
    {
        // in epoch 2.5, and in the first reward cycle of epoch 3.0, the reward set can *only* be found in the sortition DB.
        // The nakamoto chain-processing rules aren't active yet, so we can't look for the reward
        // cycle info in the nakamoto chain state.
        let Some(prepare_end_sortition_id) =
            get_ancestor_sort_id(&sort_db.index_conn(), cycle_start_height, sortition_tip)?
        else {
            // reward cycle is too far in the future
            warn!("Requested reward cycle start ancestor sortition ID for cycle {} prepare-end height {}, but tip is {}", reward_cycle, cycle_start_height, sortition_tip);
            return Ok(None);
        };

        if let Ok(persisted_reward_cycle_info) =
            sort_db.get_preprocessed_reward_set_of(&prepare_end_sortition_id)
        {
            if persisted_reward_cycle_info
                .known_selected_anchor_block()
                .is_none()
            {
                debug!("No reward set known yet for prepare phase";
                       "sortition_tip" => %sortition_tip,
                       "prepare_end_sortition_id" => %prepare_end_sortition_id);
                return Ok(None);
            }

            // find the corresponding Stacks anchor block header
            let Some((anchor_block_hash, _)) = persisted_reward_cycle_info.selected_anchor_block()
            else {
                // should be unreachable
                error!("No anchor block known for persisted reward set";
                       "sortition_tip" => %sortition_tip,
                       "prepare_end_sortition_id" => %prepare_end_sortition_id);
                return Ok(None);
            };

            let ic = sort_db.index_conn();
            let Some(anchor_block_snapshot) =
                SortitionDB::get_block_snapshot_for_winning_stacks_block(
                    &ic,
                    &prepare_end_sortition_id,
                    anchor_block_hash,
                )?
            else {
                // should be unreachable
                error!("No ancestor block snapshot for anchor block";
                       "anchor_block_hash" => %anchor_block_hash,
                       "sortition_tip" => %sortition_tip,
                       "prepare_end_sortition_id" => %prepare_end_sortition_id);

                return Ok(None);
            };

            let Some(anchor_block_header) =
                StacksChainState::get_stacks_block_header_info_by_consensus_hash(
                    chain_state.db(),
                    &anchor_block_snapshot.consensus_hash,
                )?
            else {
                // should be unreachable
                error!("No block header for anchor block";
                       "consensus_hash" => %anchor_block_snapshot.consensus_hash,
                       "anchor_block_hash" => %anchor_block_hash);
                return Ok(None);
            };

            debug!("Loaded reward set calculated in epoch 2.5 for reward cycle {} (which is in epoch {})", reward_cycle, epoch_at_height.epoch_id);
            return Ok(Some((persisted_reward_cycle_info, anchor_block_header)));
        }

        // no reward set known yet.  It's possible that it simply hasn't been processed yet.
        debug!("No pre-processed PoX reward set known for pre-Nakamoto cycle {reward_cycle}");
        return Ok(None);
    }

    // find the reward cycle's prepare-phase sortitions (in the preceding reward cycle)
    let Some(prior_cycle_end) = get_ancestor_sort_id(
        &sort_db.index_conn(),
        cycle_start_height.saturating_sub(1),
        sortition_tip,
    )?
    else {
        // reward cycle is too far in the future
        warn!("Requested reward cycle start ancestor sortition ID for cycle {} prepare-end height {}, but tip is {}", reward_cycle, cycle_start_height.saturating_sub(1), sortition_tip);
        return Ok(None);
    };
    let prepare_phase_sortitions =
        find_prepare_phase_sortitions(sort_db, burnchain, &prior_cycle_end)?;

    // iterate over the prepare_phase_sortitions, finding the first such sortition
    //  with a processed stacks block
    let Some(anchor_block_header) = prepare_phase_sortitions
        .into_iter()
        .find_map(|sn| {
            let shadow_tenure = match chain_state.nakamoto_blocks_db().is_shadow_tenure(&sn.consensus_hash) {
                Ok(x) => x,
                Err(e) => {
                    return Some(Err(e));
                }
            };

            if !sn.sortition && !shadow_tenure {
                return None
            }

            match NakamotoChainState::get_nakamoto_tenure_start_block_header(
                &mut chain_state.index_conn(),
                stacks_tip,
                &sn.consensus_hash,
            ) {
                Ok(Some(x)) => return Some(Ok(x)),
                Err(e) => return Some(Err(e)),
                Ok(None) => {}, // pass: if cannot find nakamoto block, maybe it was a 2.x block?
            }

            match StacksChainState::get_stacks_block_header_info_by_consensus_hash(
                chain_state.db(),
                &sn.consensus_hash,
            ) {
                Ok(Some(x)) => return Some(Ok(x)),
                Err(e) => return Some(Err(e)),
                Ok(None) => {
                    // no header for this snapshot (possibly invalid)
                    debug!("Failed to find Stacks block by consensus hash"; "consensus_hash" => %sn.consensus_hash);
                    return None
                }
            }
        })
        // if there was a chainstate error during the lookup, yield the error
        .transpose()? else {
            // no stacks block known yet
            info!("No PoX anchor block known yet for cycle {reward_cycle}");
            return Ok(None)
        };

    let anchor_block_sn = SortitionDB::get_block_snapshot_consensus(
        sort_db.conn(),
        &anchor_block_header.consensus_hash,
    )?
    .expect("FATAL: no snapshot for winning PoX anchor block");

    // make sure the `anchor_block` field is the same as whatever goes into the block-commit,
    // or PoX ancestry queries won't work.
    let (block_id, stacks_block_hash) = match anchor_block_header.anchored_header {
        StacksBlockHeaderTypes::Epoch2(ref header) => (
            StacksBlockId::new(&anchor_block_header.consensus_hash, &header.block_hash()),
            header.block_hash(),
        ),
        StacksBlockHeaderTypes::Nakamoto(ref header) => {
            (header.block_id(), BlockHeaderHash(header.block_id().0))
        }
    };

    let txid = anchor_block_sn.winning_block_txid;

    test_debug!("Stacks anchor block found";
           "block_id" => %block_id,
           "block_hash" => %stacks_block_hash,
           "consensus_hash" => %anchor_block_sn.consensus_hash,
           "txid" => %txid,
           "cycle_start_height" => %cycle_start_height,
           "burnchain_height" => %anchor_block_sn.block_height);

    let reward_set =
        provider.get_reward_set_nakamoto(chain_state, reward_cycle, sort_db, &block_id)?;
    debug!(
        "Stacks anchor block (ch {}) {} cycle {} is processed",
        &anchor_block_header.consensus_hash, &block_id, reward_cycle;
        "anchor.consensus_hash" => %anchor_block_header.consensus_hash,
        "anchor.burn_header_hash" => %anchor_block_header.burn_header_hash,
        "anchor.burn_block_height" => anchor_block_header.burn_header_height
    );
    let anchor_status = PoxAnchorBlockStatus::SelectedAndKnown(stacks_block_hash, txid, reward_set);

    let rc_info = RewardCycleInfo {
        reward_cycle,
        anchor_status,
    };
    Ok(Some((rc_info, anchor_block_header)))
}

/// Get the next PoX recipients in the Nakamoto epoch.
/// This is a little different than epoch 2.x:
/// * we're guaranteed to have an anchor block
/// * we pre-compute the reward set at the start of the prepare phase, so we only need to load it
/// up here at the start of the reward phase.
/// `stacks_tip` is the tip that the caller is going to build a block on.
pub fn get_nakamoto_next_recipients(
    sortition_tip: &BlockSnapshot,
    sort_db: &mut SortitionDB,
    chain_state: &mut StacksChainState,
    stacks_tip: &StacksBlockId,
    burnchain: &Burnchain,
) -> Result<Option<RewardSetInfo>, Error> {
    let next_burn_height = sortition_tip.block_height.saturating_add(1);
    let Some(reward_cycle) = burnchain.block_height_to_reward_cycle(next_burn_height) else {
        error!("CORRUPTION: evaluating burn block height before starting burn height");
        return Err(Error::BurnchainError(burnchains::Error::NoStacksEpoch));
    };
    let reward_cycle_info = if burnchain.is_reward_cycle_start(next_burn_height) {
        let Some((reward_set, _)) = load_nakamoto_reward_set(
            reward_cycle,
            &sortition_tip.sortition_id,
            burnchain,
            chain_state,
            stacks_tip,
            sort_db,
            &OnChainRewardSetProvider::new(),
        )?
        else {
            return Ok(None);
        };
        Some(reward_set)
    } else {
        None
    };
    sort_db
        .get_next_block_recipients(burnchain, sortition_tip, reward_cycle_info.as_ref())
        .map_err(Error::from)
}

impl<
        T: BlockEventDispatcher,
        N: CoordinatorNotices,
        U: RewardSetProvider,
        CE: CostEstimator + ?Sized,
        FE: FeeEstimator + ?Sized,
        B: BurnchainHeaderReader,
    > ChainsCoordinator<'_, T, N, U, CE, FE, B>
{
    /// Get the first nakamoto reward cycle
    fn get_first_nakamoto_reward_cycle(&self) -> u64 {
        let all_epochs = SortitionDB::get_stacks_epochs(self.sortition_db.conn())
            .unwrap_or_else(|e| panic!("FATAL: failed to query sortition DB for epochs: {:?}", &e));

        let Some(epoch_3_idx) = StacksEpoch::find_epoch_by_id(&all_epochs, StacksEpochId::Epoch30)
        else {
            // this is only reachable in tests
            if cfg!(any(test, feature = "testing")) {
                return u64::MAX;
            } else {
                panic!("FATAL: epoch3 not defined");
            }
        };

        let epoch3 = &all_epochs[epoch_3_idx];
        let first_epoch3_reward_cycle = self
            .burnchain
            .block_height_to_reward_cycle(epoch3.start_height)
            .expect("FATAL: epoch3 block height has no reward cycle");

        first_epoch3_reward_cycle
    }

    /// Get the current reward cycle
    fn get_current_reward_cycle(&self) -> u64 {
        let canonical_sortition_tip = self.canonical_sortition_tip.clone().unwrap_or_else(|| {
            panic!("FAIL: checking epoch status, but we don't have a canonical sortition tip")
        });

        let canonical_sn =
            SortitionDB::get_block_snapshot(self.sortition_db.conn(), &canonical_sortition_tip)
                .unwrap_or_else(|e| panic!("FATAL: failed to query sortition DB: {:?}", &e))
                .unwrap_or_else(|| panic!("FATAL: canonical sortition tip has no sortition"));

        let cur_reward_cycle = self
            .burnchain
            .block_height_to_reward_cycle(canonical_sn.block_height)
            .expect("FATAL: snapshot has no reward cycle");

        cur_reward_cycle
    }

    /// Are we in the first-ever Nakamoto reward cycle?
    pub fn in_first_nakamoto_reward_cycle(&self) -> bool {
        self.get_current_reward_cycle() == self.get_first_nakamoto_reward_cycle()
    }

    /// Are we in the second or later Nakamoto reward cycle?
    pub fn in_subsequent_nakamoto_reward_cycle(&self) -> bool {
        self.get_current_reward_cycle() > self.get_first_nakamoto_reward_cycle()
    }

    /// This is the main loop body for the coordinator in epoch 3.
    /// Returns true if the coordinator is still running.
    /// Returns false otherwise.
    pub fn handle_comms_nakamoto(
        &mut self,
        bits: u8,
        miner_status: Arc<Mutex<MinerStatus>>,
    ) -> bool {
        // timeout so that we handle Ctrl-C a little gracefully
        if (bits & (CoordinatorEvents::NEW_STACKS_BLOCK as u8)) != 0 {
            signal_mining_blocked(miner_status.clone());
            debug!("Received new Nakamoto stacks block notice");

            // we may still be processing epoch 2 blocks after the Nakamoto transition, so be sure
            // to process them so we can get to the Nakamoto blocks!
            if !self.in_nakamoto_epoch {
                debug!("Check to see if the system has entered the Nakamoto epoch");
                if let Ok(Some(canonical_header)) = NakamotoChainState::get_canonical_block_header(
                    self.chain_state_db.db(),
                    &self.sortition_db,
                ) {
                    if canonical_header.is_nakamoto_block() {
                        // great! don't check again
                        debug!(
                            "The canonical Stacks tip ({}/{}) is a Nakamoto block!",
                            &canonical_header.consensus_hash,
                            &canonical_header.anchored_header.block_hash()
                        );
                        self.in_nakamoto_epoch = true;
                    } else {
                        // need to process epoch 2 blocks
                        debug!("Received new epoch 2.x Stacks block notice");
                        match self.handle_new_stacks_block() {
                            Ok(missing_block_opt) => {
                                if missing_block_opt.is_some() {
                                    debug!(
                                        "Missing affirmed anchor block: {:?}",
                                        &missing_block_opt.as_ref().expect("unreachable")
                                    );
                                }
                            }
                            Err(e) => {
                                warn!("Error processing new stacks block: {:?}", e);
                            }
                        }
                    }
                }
            }

            // now we can process the nakamoto block
            match self.handle_new_nakamoto_stacks_block() {
                Ok(new_anchor_block_opt) => {
                    if let Some(bhh) = new_anchor_block_opt {
                        debug!(
                            "Found next PoX anchor block, waiting for reward cycle processing";
                            "pox_anchor_block_hash" => %bhh
                        );
                    }
                }
                Err(e) => {
                    warn!("Error processing new stacks block: {:?}", e);
                }
            }

            signal_mining_ready(miner_status.clone());
        }
        if (bits & (CoordinatorEvents::NEW_BURN_BLOCK as u8)) != 0 {
            signal_mining_blocked(miner_status.clone());
            debug!("Received new burn block notice");
            match self.handle_new_nakamoto_burnchain_block() {
                Ok(can_proceed) => {
                    if !can_proceed {
                        error!("Missing canonical anchor block");
                    }
                }
                Err(e) => {
                    warn!("Error processing new burn block: {:?}", e);
                }
            }
            signal_mining_ready(miner_status.clone());
        }
        if (bits & (CoordinatorEvents::STOP as u8)) != 0 {
            signal_mining_blocked(miner_status);
            debug!("Received stop notice");
            return false;
        }

        true
    }

    #[cfg(any(test, feature = "testing"))]
    fn fault_injection_pause_nakamoto_block_processing() {
        if *TEST_COORDINATOR_STALL.lock().unwrap() == Some(true) {
            // Do an extra check just so we don't log EVERY time.
            warn!("Coordinator is stalled due to testing directive");
            while *TEST_COORDINATOR_STALL.lock().unwrap() == Some(true) {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            warn!("Coordinator is no longer stalled due to testing directive. Continuing...");
        }
    }

    #[cfg(not(any(test, feature = "testing")))]
    fn fault_injection_pause_nakamoto_block_processing() {}

    /// Handle one or more new Nakamoto Stacks blocks.
    /// If we process a PoX anchor block, then return its block hash.  This unblocks processing the
    /// next reward cycle's burnchain blocks.  Subsequent calls to this function will terminate
    /// with Some(pox-anchor-block-hash) until the reward cycle info is processed in the sortition
    /// DB.
    pub fn handle_new_nakamoto_stacks_block(&mut self) -> Result<Option<BlockHeaderHash>, Error> {
        debug!("Handle new Nakamoto block");
        let canonical_sortition_tip = self.canonical_sortition_tip.clone().expect(
            "FAIL: processing a new Stacks block, but don't have a canonical sortition tip",
        );

        loop {
            Self::fault_injection_pause_nakamoto_block_processing();

            // process at most one block per loop pass
            let mut processed_block_receipt = match NakamotoChainState::process_next_nakamoto_block(
                &mut self.chain_state_db,
                &mut self.sortition_db,
                &canonical_sortition_tip,
                self.dispatcher,
                self.config.txindex,
            ) {
                Ok(receipt_opt) => receipt_opt,
                Err(ChainstateError::InvalidStacksBlock(msg)) => {
                    warn!("Encountered invalid block: {}", &msg);

                    // try again
                    self.notifier.notify_stacks_block_processed();
                    increment_stx_blocks_processed_counter();
                    continue;
                }
                Err(ChainstateError::NetError(NetError::DeserializeError(msg))) => {
                    // happens if we load a zero-sized block (i.e. an invalid block)
                    warn!("Encountered invalid block (codec error): {}", &msg);

                    // try again
                    self.notifier.notify_stacks_block_processed();
                    increment_stx_blocks_processed_counter();
                    continue;
                }
                Err(e) => {
                    // something else happened
                    return Err(e.into());
                }
            };

            let Some(block_receipt) = processed_block_receipt.take() else {
                // out of blocks
                debug!("No more blocks to process (no receipts)");
                break;
            };

            if block_receipt.signers_updated {
                // notify p2p thread via globals
                self.refresh_stacker_db
                    .store(true, std::sync::atomic::Ordering::SeqCst);
            }

            let block_hash = block_receipt.header.anchored_header.block_hash();
            let (
                canonical_stacks_block_id,
                canonical_stacks_block_height,
                canonical_stacks_consensus_hash,
            ) = {
                let nakamoto_header = block_receipt
                    .header
                    .anchored_header
                    .as_stacks_nakamoto()
                    .expect("FATAL: unreachable: processed a non-Nakamoto block");

                (
                    nakamoto_header.block_id(),
                    nakamoto_header.chain_length,
                    nakamoto_header.consensus_hash.clone(),
                )
            };

            debug!("Bump blocks processed ({})", &canonical_stacks_block_id);

            self.notifier.notify_stacks_block_processed();
            increment_stx_blocks_processed_counter();

            // process Atlas events
            Self::process_atlas_attachment_events(
                self.atlas_db.as_mut(),
                &self.atlas_config,
                &block_receipt,
                canonical_stacks_block_height,
            );

            // update cost estimator
            if let Some(ref mut estimator) = self.cost_estimator {
                let stacks_epoch = SortitionDB::get_stacks_epoch_by_epoch_id(
                    self.sortition_db.conn(),
                    &block_receipt.evaluated_epoch,
                )?
                .expect("Could not find a stacks epoch.");
                estimator.notify_block(
                    &block_receipt.tx_receipts,
                    &stacks_epoch.block_limit,
                    &stacks_epoch.epoch_id,
                );
            }

            // update fee estimator
            if let Some(ref mut estimator) = self.fee_estimator {
                let stacks_epoch = SortitionDB::get_stacks_epoch_by_epoch_id(
                    self.sortition_db.conn(),
                    &block_receipt.evaluated_epoch,
                )?
                .expect("Could not find a stacks epoch.");
                if let Err(e) = estimator.notify_block(&block_receipt, &stacks_epoch.block_limit) {
                    warn!("FeeEstimator failed to process block receipt";
                        "stacks_block_hash" => %block_hash,
                        "stacks_block_height" => %block_receipt.header.stacks_block_height,
                        "burn_block_hash" => %block_receipt.header.burn_header_hash,
                        "error" => %e
                    );
                }
            }

            let stacks_sn = SortitionDB::get_block_snapshot_consensus(
                self.sortition_db.conn(),
                &canonical_stacks_consensus_hash,
            )?
            .unwrap_or_else(|| {
                panic!(
                    "FATAL: unreachable: consensus hash {} has no snapshot",
                    &canonical_stacks_consensus_hash
                )
            });

            // are we in the prepare phase?
            // TODO: this should *not* include the 0 block!
            if !self
                .burnchain
                .is_in_naka_prepare_phase(stacks_sn.block_height)
            {
                // next ready stacks block
                continue;
            }

            // is the upcoming reward cycle processed yet?
            let current_reward_cycle = self
                .burnchain
                .block_height_to_reward_cycle(stacks_sn.block_height)
                .unwrap_or_else(|| {
                    panic!("FATAL: unreachable: burnchain block height has no reward cycle")
                });

            let last_processed_reward_cycle = {
                let canonical_sn = SortitionDB::get_block_snapshot(
                    self.sortition_db.conn(),
                    &canonical_sortition_tip,
                )?
                .ok_or(DBError::NotFoundError)?;

                // check and see if *this block* or one if its ancestors has processed the reward
                // cycle data
                let Some((rc_info, _)) = load_nakamoto_reward_set(
                    self.burnchain
                        .block_height_to_reward_cycle(canonical_sn.block_height)
                        .expect("FATAL: snapshot has no reward cycle"),
                    &canonical_sn.sortition_id,
                    &self.burnchain,
                    &mut self.chain_state_db,
                    &canonical_stacks_block_id,
                    &self.sortition_db,
                    &OnChainRewardSetProvider::new(),
                )?
                else {
                    // no anchor block yet, so try processing another block
                    continue;
                };
                rc_info.reward_cycle
            };

            if last_processed_reward_cycle > current_reward_cycle {
                // already processed upcoming reward cycle
                continue;
            }

            // This is the first Stacks block in the prepare phase for the next reward cycle,
            // as determined by the history tipped at `canonical_stacks_block_id`.
            // Pause here and process the next sortitions
            debug!("Process next reward cycle's sortitions");
            self.handle_new_nakamoto_burnchain_block()?;
            debug!("Processed next reward cycle's sortitions");
        }

        // no PoX anchor block found
        Ok(None)
    }

    /// Given a burnchain header, find the PoX reward cycle info
    fn get_nakamoto_reward_cycle_info(
        &mut self,
        stacks_tip: &StacksBlockId,
        reward_cycle: u64,
    ) -> Result<Option<RewardCycleInfo>, Error> {
        let sortition_tip_id = self
            .canonical_sortition_tip
            .as_ref()
            .expect("FATAL: Processing anchor block, but no known sortition tip");

        get_nakamoto_reward_cycle_info(
            sortition_tip_id,
            reward_cycle,
            &self.burnchain,
            &mut self.chain_state_db,
            stacks_tip,
            &mut self.sortition_db,
            &self.reward_set_provider,
        )
    }

    /// Find sortitions to process.
    /// Returns the last processed ancestor of `cursor`, and any unprocessed burnchain blocks
    fn find_sortitions_to_process(
        &self,
        mut cursor: BurnchainHeaderHash,
    ) -> Result<(SortitionId, VecDeque<BurnchainBlockData>), Error> {
        let mut sortitions_to_process = VecDeque::new();
        let last_processed_ancestor = loop {
            if let Some(found_sortition) = self.sortition_db.is_sortition_processed(&cursor)? {
                debug!(
                    "Ancestor sortition {} of block {} is processed",
                    &found_sortition, &cursor
                );
                break found_sortition;
            }

            let current_block =
                BurnchainDB::get_burnchain_block(self.burnchain_blocks_db.conn(), &cursor)
                    .map_err(|e| {
                        warn!(
                            "ChainsCoordinator: could not retrieve block burnhash={}",
                            &cursor
                        );
                        Error::NonContiguousBurnchainBlock(e)
                    })?;

            debug!(
                "Unprocessed block: ({}, {})",
                &current_block.header.block_hash.to_string(),
                current_block.header.block_height
            );

            let parent = current_block.header.parent_block_hash.clone();
            sortitions_to_process.push_front(current_block);
            cursor = parent;
        };
        Ok((last_processed_ancestor, sortitions_to_process))
    }

    /// Process the next-available burnchain block, if possible.
    /// Burnchain blocks can only be processed for the last-known PoX reward set, which is to say,
    /// burnchain block processing can be blocked on the unavailability of the next PoX anchor
    /// block.  If the next PoX anchor block is not available, then no burnchain block processing
    /// happens, and this function returns false.  It returns true otherwise.
    ///
    /// Returns Err(..) if an error occurred while processing (i.e. a DB error).
    pub fn handle_new_nakamoto_burnchain_block(&mut self) -> Result<bool, Error> {
        // highest burnchain block we've downloaded
        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;

        debug!("Handle new canonical burnchain tip";
               "height" => %canonical_burnchain_tip.block_height,
               "block_hash" => %canonical_burnchain_tip.block_hash.to_string());

        // Retrieve all the direct ancestors of this block with an unprocessed sortition
        let (mut last_processed_ancestor, sortitions_to_process) =
            self.find_sortitions_to_process(canonical_burnchain_tip.block_hash.clone())?;
        let dbg_burn_header_hashes: Vec<_> = sortitions_to_process
            .iter()
            .map(|block| {
                format!(
                    "({}, {})",
                    &block.header.block_hash.to_string(),
                    block.header.block_height
                )
            })
            .collect();

        debug!(
            "Unprocessed burn chain blocks: {:?}",
            &dbg_burn_header_hashes
        );

        // Unlike in Stacks 2.x, there can be neither chain reorgs nor PoX reorgs unless Bitcoin itself
        // reorgs.  But if this happens, then we will have already found the set of
        // (newly-canonical) burnchain blocks which lack sortitions -- they'll be in
        // `sortitions_to_process`.  So, we can proceed to process all outstanding sortitions until
        // we come across a PoX anchor block that we don't have yet.
        for unprocessed_block in sortitions_to_process.into_iter() {
            let BurnchainBlockData { header, ops } = unprocessed_block;
            let reward_cycle = self
                .burnchain
                .block_height_to_reward_cycle(header.block_height)
                .unwrap_or(u64::MAX);

            info!(
                "Process burn block {} reward cycle {} in {}",
                header.block_height, reward_cycle, &self.burnchain.working_dir;
                "in_prepare_phase" => self.burnchain.is_in_prepare_phase(header.block_height),
                "is_rc_start" => self.burnchain.is_reward_cycle_start(header.block_height),
                "is_prior_in_prepare_phase" => self.burnchain.is_in_prepare_phase(header.block_height.saturating_sub(2)),
                "burn_block_hash" => %header.block_hash,
            );

            // calculate paid rewards during this burnchain block if we announce
            //  to an events dispatcher
            let paid_rewards = if self.dispatcher.is_some() {
                calculate_paid_rewards(&ops)
            } else {
                PaidRewards {
                    pox: vec![],
                    burns: 0,
                }
            };

            let reward_cycle_info = if self.burnchain.is_reward_cycle_start(header.block_height) {
                // we're at the end of the prepare phase, so we'd better have obtained the reward
                // cycle info of we must block.
                // NOTE(safety): the reason it's safe to use the local best stacks tip here is
                // because as long as at least 30% of the signers are honest, there's no way there
                // can be two or more distinct reward sets calculated for a reward cycle.  Due to
                // signature malleability, there can be multiple unconfirmed siblings at a given
                // height H, but at height H+1, exactly one of those siblings will be canonical,
                // and will remain canonical with respect to its tenure's Bitcoin fork forever.
                // Here, we're loading a reward set calculated between H and H+99 from H+100, where
                // H is the start of the prepare phase.  So if we get any reward set from our
                // canonical tip, it's guaranteed to be the canonical one.
                let canonical_sortition_tip = self.canonical_sortition_tip.clone().unwrap_or(
                    // should be unreachable
                    SortitionDB::get_canonical_burn_chain_tip(self.sortition_db.conn())?
                        .sortition_id,
                );

                let Some(local_best_nakamoto_tip) = self
                    .sortition_db
                    .index_handle(&canonical_sortition_tip)
                    .get_nakamoto_tip_block_id()?
                else {
                    debug!("No Nakamoto blocks processed yet, so no reward cycle known for this next reward cycle");
                    return Ok(false);
                };

                let Some(reward_cycle) = self
                    .burnchain
                    .block_height_to_reward_cycle(header.block_height)
                else {
                    error!("CORRUPTION: Evaluating burn block before start burn height"; "burn_height" => header.block_height);
                    return Ok(false);
                };
                let reward_cycle_info =
                    self.get_nakamoto_reward_cycle_info(&local_best_nakamoto_tip, reward_cycle)?;
                if let Some(rc_info) = reward_cycle_info.as_ref() {
                    // in nakamoto, if we have any reward cycle info at all, it will be known.
                    // otherwise, we may have to process some more Stacks blocks
                    if rc_info.known_selected_anchor_block().is_none() {
                        warn!("Unknown PoX anchor block in Nakamoto (at height {}). Refusing to process more burnchain blocks until that changes.", header.block_height);
                        return Ok(false);
                    }
                } else {
                    // have to block -- we don't have the reward cycle information
                    debug!("Do not yet have PoX anchor block for next reward cycle -- no anchor block found";
                           "local_best_nakamoto_tip" => %local_best_nakamoto_tip,
                           "next_reward_cycle" => self.burnchain.block_height_to_reward_cycle(header.block_height),
                           "block_height" => header.block_height);
                    return Ok(false);
                }
                reward_cycle_info
            } else {
                // not starting a reward cycle anyway
                None
            };

            // process next sortition
            let dispatcher_ref = &self.dispatcher;
            let (next_snapshot, _) = self
                .sortition_db
                .evaluate_sortition(
                    self.chain_state_db.mainnet,
                    &header,
                    ops,
                    &self.burnchain,
                    &last_processed_ancestor,
                    reward_cycle_info,
                    |reward_set_info, consensus_hash| {
                        if let Some(dispatcher) = dispatcher_ref {
                            dispatcher_announce_burn_ops(
                                *dispatcher,
                                &header,
                                paid_rewards,
                                reward_set_info,
                                &consensus_hash,
                            );
                        }
                    },
                )
                .map_err(|e| {
                    error!("ChainsCoordinator: unable to evaluate sortition: {:?}", e);
                    Error::FailedToProcessSortition(e)
                })?;

            // mark this burn block as processed in the nakamoto chainstate
            let tx = self.chain_state_db.staging_db_tx_begin()?;
            tx.set_burn_block_processed(&next_snapshot.consensus_hash)?;
            tx.commit().map_err(DBError::SqliteError)?;

            let sortition_id = next_snapshot.sortition_id;

            self.notifier.notify_sortition_processed();

            debug!(
                "Sortition processed";
                "sortition_id" => &sortition_id.to_string(),
                "burn_header_hash" => &next_snapshot.burn_header_hash.to_string(),
                "burn_height" => next_snapshot.block_height
            );

            // always bump canonical sortition tip:
            //   if this code path is invoked, the canonical burnchain tip
            //   has moved, so we should move our canonical sortition tip as well.
            self.canonical_sortition_tip = Some(sortition_id.clone());
            last_processed_ancestor = sortition_id;
        }

        Ok(true)
    }
}
