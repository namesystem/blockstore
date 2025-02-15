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

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::mpsc::SyncSender;
use std::sync::{Arc, Mutex};
use std::time::Duration;
use std::{cmp, fs};

use clarity::vm::costs::ExecutionCost;
use clarity::vm::database::BurnStateDB;
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier};
use clarity::vm::Value;
use stacks_common::bitvec::BitVec;
use stacks_common::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, StacksBlockId,
};
use stacks_common::util::get_epoch_time_secs;

pub use self::comm::CoordinatorCommunication;
use super::stacks::boot::{RewardSet, RewardSetData};
use super::stacks::db::blocks::DummyEventDispatcher;
use crate::burnchains::affirmation::{AffirmationMap, AffirmationMapEntry};
use crate::burnchains::bitcoin::indexer::BitcoinIndexer;
use crate::burnchains::db::{
    BlockCommitMetadata, BurnchainBlockData, BurnchainDB, BurnchainDBTransaction,
    BurnchainHeaderReader,
};
use crate::burnchains::{
    Address, Burnchain, BurnchainBlockHeader, Error as BurnchainError, PoxConstants, Txid,
};
use crate::chainstate::burn::db::sortdb::{
    SortitionDB, SortitionDBConn, SortitionDBTx, SortitionHandleTx,
};
use crate::chainstate::burn::operations::leader_block_commit::{
    RewardSetInfo, BURN_BLOCK_MINED_AT_MODULUS,
};
use crate::chainstate::burn::operations::{BlockstackOperationType, LeaderBlockCommitOp};
use crate::chainstate::burn::{BlockSnapshot, ConsensusHash};
use crate::chainstate::coordinator::comm::{
    ArcCounterCoordinatorNotices, CoordinatorEvents, CoordinatorNotices, CoordinatorReceivers,
};
use crate::chainstate::stacks::address::PoxAddress;
use crate::chainstate::stacks::boot::{POX_3_NAME, POX_4_NAME};
use crate::chainstate::stacks::db::accounts::MinerReward;
use crate::chainstate::stacks::db::{
    ChainStateBootData, ClarityTx, MinerRewardInfo, StacksChainState, StacksEpochReceipt,
    StacksHeaderInfo,
};
use crate::chainstate::stacks::events::{
    StacksBlockEventData, StacksTransactionEvent, StacksTransactionReceipt, TransactionOrigin,
};
use crate::chainstate::stacks::index::marf::MARFOpenOpts;
use crate::chainstate::stacks::index::{Error as IndexError, MarfTrieId};
use crate::chainstate::stacks::miner::{signal_mining_blocked, signal_mining_ready, MinerStatus};
use crate::chainstate::stacks::{
    Error as ChainstateError, StacksBlock, StacksBlockHeader, TransactionPayload,
};
use crate::core::{
    StacksEpoch, StacksEpochId, FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH,
};
use crate::cost_estimates::{CostEstimator, FeeEstimator, PessimisticEstimator};
use crate::monitoring::{
    increment_contract_calls_processed, increment_stx_blocks_processed_counter,
};
use crate::net::atlas::{AtlasConfig, AtlasDB, AttachmentInstance};
use crate::util_lib::db::{DBConn, DBTx, Error as DBError};

pub mod comm;
#[cfg(test)]
pub mod tests;

/// The 3 different states for the current
///  reward cycle's relationship to its PoX anchor
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PoxAnchorBlockStatus {
    SelectedAndKnown(BlockHeaderHash, Txid, RewardSet),
    SelectedAndUnknown(BlockHeaderHash, Txid),
    NotSelected,
}

/// The possible outcomes of processing a burnchain block.
/// Indicates whether or not we're ready to process Stacks blocks, or if not, whether or not we're
/// blocked on a Stacks 2.x anchor block or a Nakamoto anchor block
pub enum NewBurnchainBlockStatus {
    /// Ready to process Stacks blocks
    Ready,
    /// Missing 2.x PoX anchor block
    WaitForPox2x(BlockHeaderHash),
    /// Missing Nakamoto anchor block. Unlike 2.x, we won't know its hash.
    WaitForPoxNakamoto,
}

impl NewBurnchainBlockStatus {
    /// Test helper to convert this status into the optional hash of the missing PoX anchor block.
    /// Because there are unit tests that expect a Some(..) result if PoX cannot proceed, the
    /// missing Nakamoto anchor block case is converted into a placeholder Some(..) value
    #[cfg(test)]
    pub fn into_missing_block_hash(self) -> Option<BlockHeaderHash> {
        match self {
            Self::Ready => None,
            Self::WaitForPox2x(block_hash) => Some(block_hash),
            Self::WaitForPoxNakamoto => Some(BlockHeaderHash([0x00; 32])),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct RewardCycleInfo {
    pub reward_cycle: u64,
    pub anchor_status: PoxAnchorBlockStatus,
}

impl RewardCycleInfo {
    pub fn selected_anchor_block(&self) -> Option<(&BlockHeaderHash, &Txid)> {
        use self::PoxAnchorBlockStatus::*;
        match self.anchor_status {
            SelectedAndUnknown(ref block, ref txid) | SelectedAndKnown(ref block, ref txid, _) => {
                Some((block, txid))
            }
            NotSelected => None,
        }
    }
    pub fn is_reward_info_known(&self) -> bool {
        use self::PoxAnchorBlockStatus::*;
        match self.anchor_status {
            SelectedAndUnknown(..) => false,
            SelectedAndKnown(..) | NotSelected => true,
        }
    }
    pub fn known_selected_anchor_block(&self) -> Option<&RewardSet> {
        use self::PoxAnchorBlockStatus::*;
        match self.anchor_status {
            SelectedAndUnknown(..) => None,
            SelectedAndKnown(_, _, ref reward_set) => Some(reward_set),
            NotSelected => None,
        }
    }
    pub fn known_selected_anchor_block_owned(self) -> Option<RewardSet> {
        use self::PoxAnchorBlockStatus::*;
        match self.anchor_status {
            SelectedAndUnknown(..) => None,
            SelectedAndKnown(_, _, reward_set) => Some(reward_set),
            NotSelected => None,
        }
    }
}

pub trait BlockEventDispatcher {
    fn announce_block(
        &self,
        block: &StacksBlockEventData,
        metadata: &StacksHeaderInfo,
        receipts: &[StacksTransactionReceipt],
        parent: &StacksBlockId,
        winner_txid: Txid,
        matured_rewards: &[MinerReward],
        matured_rewards_info: Option<&MinerRewardInfo>,
        parent_burn_block_hash: BurnchainHeaderHash,
        parent_burn_block_height: u32,
        parent_burn_block_timestamp: u64,
        anchored_consumed: &ExecutionCost,
        mblock_confirmed_consumed: &ExecutionCost,
        pox_constants: &PoxConstants,
        reward_set_data: &Option<RewardSetData>,
        signer_bitvec: &Option<BitVec<4000>>,
        block_timestamp: Option<u64>,
        coinbase_height: u64,
    );

    /// called whenever a burn block is about to be
    ///  processed for sortition. note, in the event
    ///  of PoX forks, this will be called _multiple_
    ///  times for the same burnchain header hash.
    fn announce_burn_block(
        &self,
        burn_block: &BurnchainHeaderHash,
        burn_block_height: u64,
        rewards: Vec<(PoxAddress, u64)>,
        burns: u64,
        reward_recipients: Vec<PoxAddress>,
        consensus_hash: &ConsensusHash,
    );
}

pub struct ChainsCoordinatorConfig {
    /// true: assume all anchor blocks are present, and block chain sync until they arrive
    /// false: process sortitions in reward cycles without anchor blocks
    pub assume_present_anchor_blocks: bool,
    /// true: use affirmation maps before 2.1
    /// false: only use affirmation maps in 2.1 or later
    pub always_use_affirmation_maps: bool,
    /// true: always wait for canonical anchor blocks, even if it stalls the chain
    /// false: proceed to process new chain history even if we're missing an anchor block.
    pub require_affirmed_anchor_blocks: bool,
    /// true: enable transactions indexing
    /// false: no transactions indexing
    pub txindex: bool,
}

impl ChainsCoordinatorConfig {
    pub fn new() -> ChainsCoordinatorConfig {
        ChainsCoordinatorConfig {
            always_use_affirmation_maps: true,
            require_affirmed_anchor_blocks: true,
            assume_present_anchor_blocks: true,
            txindex: false,
        }
    }

    pub fn test_new() -> ChainsCoordinatorConfig {
        ChainsCoordinatorConfig {
            always_use_affirmation_maps: false,
            require_affirmed_anchor_blocks: false,
            assume_present_anchor_blocks: false,
            txindex: false,
        }
    }
}

pub struct ChainsCoordinator<
    'a,
    T: BlockEventDispatcher,
    N: CoordinatorNotices,
    R: RewardSetProvider,
    CE: CostEstimator + ?Sized,
    FE: FeeEstimator + ?Sized,
    B: BurnchainHeaderReader,
> {
    pub canonical_sortition_tip: Option<SortitionId>,
    pub burnchain_blocks_db: BurnchainDB,
    pub chain_state_db: StacksChainState,
    pub sortition_db: SortitionDB,
    pub burnchain: Burnchain,
    pub atlas_db: Option<AtlasDB>,
    pub dispatcher: Option<&'a T>,
    pub cost_estimator: Option<&'a mut CE>,
    pub fee_estimator: Option<&'a mut FE>,
    pub reward_set_provider: R,
    pub notifier: N,
    pub atlas_config: AtlasConfig,
    pub config: ChainsCoordinatorConfig,
    burnchain_indexer: B,
    /// Used to tell the P2P thread that the stackerdb
    ///  needs to be refreshed.
    pub refresh_stacker_db: Arc<AtomicBool>,
    /// whether or not the canonical tip is now a Nakamoto header
    pub in_nakamoto_epoch: bool,
}

#[derive(Debug)]
pub enum Error {
    BurnchainBlockAlreadyProcessed,
    BurnchainError(BurnchainError),
    ChainstateError(ChainstateError),
    NonContiguousBurnchainBlock(BurnchainError),
    NoSortitions,
    FailedToProcessSortition(BurnchainError),
    DBError(DBError),
    IndexError(IndexError),
    NotPrepareEndBlock,
    NotPoXAnchorBlock,
    NotInPreparePhase,
    RewardSetAlreadyProcessed,
    PoXAnchorBlockRequired,
    PoXNotProcessedYet,
}

impl From<BurnchainError> for Error {
    fn from(o: BurnchainError) -> Error {
        Error::BurnchainError(o)
    }
}

impl From<ChainstateError> for Error {
    fn from(o: ChainstateError) -> Error {
        Error::ChainstateError(o)
    }
}

impl From<DBError> for Error {
    fn from(o: DBError) -> Error {
        Error::DBError(o)
    }
}

impl From<IndexError> for Error {
    fn from(o: IndexError) -> Error {
        Error::IndexError(o)
    }
}

pub trait RewardSetProvider {
    fn get_reward_set(
        &self,
        cycle_start_burn_height: u64,
        chainstate: &mut StacksChainState,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<RewardSet, Error>;

    fn get_reward_set_nakamoto(
        &self,
        chainstate: &mut StacksChainState,
        cycle: u64,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<RewardSet, Error>;
}

pub struct OnChainRewardSetProvider<'a, T: BlockEventDispatcher>(pub Option<&'a T>);

impl OnChainRewardSetProvider<'static, DummyEventDispatcher> {
    pub fn new() -> Self {
        Self(None)
    }
}

impl<T: BlockEventDispatcher> RewardSetProvider for OnChainRewardSetProvider<'_, T> {
    fn get_reward_set(
        &self,
        cycle_start_burn_height: u64,
        chainstate: &mut StacksChainState,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<RewardSet, Error> {
        let cur_epoch = SortitionDB::get_stacks_epoch(sortdb.conn(), cycle_start_burn_height)?
            .unwrap_or_else(|| panic!("FATAL: no epoch for burn height {cycle_start_burn_height}"));
        let cycle = burnchain
            .block_height_to_reward_cycle(cycle_start_burn_height)
            .expect("FATAL: no reward cycle for burn height");
        // `self.get_reward_set_nakamoto` reads the reward set from data written during
        //   updates to .signers
        // `self.get_reward_set_epoch2` reads the reward set from the `.pox-*` contract
        //
        //  Data **cannot** be read from `.signers` in epoch 2.5 because the write occurs
        //   in the first block of the prepare phase, but the PoX anchor block is *before*
        //   the prepare phase. Therefore, we fetch the reward set in the 2.x style, and then
        //   apply the necessary nakamoto assertions if the reward set is going to be
        //   active in Nakamoto (i.e., check for signer set existence).

        let is_nakamoto_reward_set = match SortitionDB::get_stacks_epoch_by_epoch_id(
            sortdb.conn(),
            &StacksEpochId::Epoch30,
        )? {
            Some(epoch_30) => {
                let first_nakamoto_cycle = burnchain
                    .block_height_to_reward_cycle(epoch_30.start_height)
                    .expect("FATAL: no reward cycle for burn height");
                first_nakamoto_cycle <= cycle
            }
            // if epoch-3.0 isn't defined, then never use a nakamoto reward set.
            None => false,
        };

        let reward_set = self.get_reward_set_epoch2(
            cycle_start_burn_height,
            chainstate,
            burnchain,
            sortdb,
            block_id,
            cur_epoch,
        )?;

        if is_nakamoto_reward_set
            && (reward_set.signers.is_none() || reward_set.signers == Some(vec![]))
        {
            error!("FATAL: Signer sets are empty in a reward set that will be used in nakamoto"; "reward_set" => ?reward_set);
            return Err(Error::PoXAnchorBlockRequired);
        }

        Ok(reward_set)
    }

    fn get_reward_set_nakamoto(
        &self,
        chainstate: &mut StacksChainState,
        reward_cycle: u64,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<RewardSet, Error> {
        self.read_reward_set_nakamoto(chainstate, reward_cycle, sortdb, block_id, false)
    }
}

impl<T: BlockEventDispatcher> OnChainRewardSetProvider<'_, T> {
    fn get_reward_set_epoch2(
        &self,
        // Todo: `current_burn_height` is a misleading name: should be the `cycle_start_burn_height`
        current_burn_height: u64,
        chainstate: &mut StacksChainState,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
        cur_epoch: StacksEpoch,
    ) -> Result<RewardSet, Error> {
        match cur_epoch.epoch_id {
            StacksEpochId::Epoch10
            | StacksEpochId::Epoch20
            | StacksEpochId::Epoch2_05
            | StacksEpochId::Epoch21 => {
                // Epochs 1.0 - 2.1 compute reward sets
            }
            StacksEpochId::Epoch22 | StacksEpochId::Epoch23 => {
                info!("PoX reward cycle defaulting to burn in Epochs 2.2 and 2.3");
                return Ok(RewardSet::empty());
            }
            StacksEpochId::Epoch24 => {
                // Epoch 2.4 computes reward sets, but *only* if PoX-3 is active
                if burnchain
                    .pox_constants
                    .active_pox_contract(current_burn_height)
                    != POX_3_NAME
                {
                    // Note: this should not happen in mainnet or testnet, because the no reward cycle start height
                    //        exists between Epoch 2.4's instantiation height and the pox-3 activation height.
                    //  However, this *will* happen in testing if Epoch 2.4's instantiation height is set == a reward cycle
                    //   start height
                    info!("PoX reward cycle defaulting to burn in Epoch 2.4 because cycle start is before PoX-3 activation");
                    return Ok(RewardSet::empty());
                }
            }
            StacksEpochId::Epoch25 | StacksEpochId::Epoch30 | StacksEpochId::Epoch31 => {
                // Epoch 2.5, 3.0, and 3.1 compute reward sets, but *only* if PoX-4 is active
                if burnchain
                    .pox_constants
                    .active_pox_contract(current_burn_height)
                    != POX_4_NAME
                {
                    // Note: this should not happen in mainnet or testnet, because the no reward cycle start height
                    //        exists between Epoch 2.5's instantiation height and the pox-4 activation height.
                    //  However, this *will* happen in testing if Epoch 2.5's instantiation height is set == a reward cycle
                    //   start height
                    info!("PoX reward cycle defaulting to burn in Epoch 2.5 because cycle start is before PoX-4 activation");
                    return Ok(RewardSet::empty());
                }
            }
        };

        let registered_addrs =
            chainstate.get_reward_addresses(burnchain, sortdb, current_burn_height, block_id)?;

        let liquid_ustx = chainstate.get_liquid_ustx(block_id);

        let (threshold, participation) = StacksChainState::get_reward_threshold_and_participation(
            &burnchain.pox_constants,
            &registered_addrs[..],
            liquid_ustx,
        );

        if !burnchain
            .pox_constants
            .enough_participation(participation, liquid_ustx)
        {
            info!("PoX reward cycle did not have enough participation. Defaulting to burn";
                  "burn_height" => current_burn_height,
                  "participation" => participation,
                  "liquid_ustx" => liquid_ustx,
                  "registered_addrs" => registered_addrs.len());
            return Ok(RewardSet::empty());
        } else {
            info!("PoX reward cycle threshold computed";
                  "burn_height" => current_burn_height,
                  "threshold" => threshold,
                  "participation" => participation,
                  "liquid_ustx" => liquid_ustx,
                  "registered_addrs" => registered_addrs.len());
        }

        Ok(StacksChainState::make_reward_set(
            threshold,
            registered_addrs,
            cur_epoch.epoch_id,
        ))
    }
}

impl<
        'a,
        T: BlockEventDispatcher,
        CE: CostEstimator + ?Sized,
        FE: FeeEstimator + ?Sized,
        B: BurnchainHeaderReader,
    >
    ChainsCoordinator<
        'a,
        T,
        ArcCounterCoordinatorNotices,
        OnChainRewardSetProvider<'a, T>,
        CE,
        FE,
        B,
    >
{
    pub fn run(
        config: ChainsCoordinatorConfig,
        chain_state_db: StacksChainState,
        burnchain: Burnchain,
        dispatcher: &'a T,
        comms: CoordinatorReceivers,
        atlas_config: AtlasConfig,
        cost_estimator: Option<&'a mut CE>,
        fee_estimator: Option<&'a mut FE>,
        miner_status: Arc<Mutex<MinerStatus>>,
        burnchain_indexer: B,
        atlas_db: AtlasDB,
    ) where
        T: BlockEventDispatcher,
    {
        let stacks_blocks_processed = comms.stacks_blocks_processed.clone();
        let sortitions_processed = comms.sortitions_processed.clone();

        let sortition_db = SortitionDB::open(
            &burnchain.get_db_path(),
            true,
            burnchain.pox_constants.clone(),
        )
        .unwrap();
        let burnchain_blocks_db =
            BurnchainDB::open(&burnchain.get_burnchaindb_path(), false).unwrap();

        let canonical_sortition_tip =
            SortitionDB::get_canonical_sortition_tip(sortition_db.conn()).unwrap();

        let arc_notices = ArcCounterCoordinatorNotices {
            stacks_blocks_processed,
            sortitions_processed,
        };

        let mut inst = ChainsCoordinator {
            canonical_sortition_tip: Some(canonical_sortition_tip),
            burnchain_blocks_db,
            chain_state_db,
            sortition_db,
            burnchain,
            dispatcher: Some(dispatcher),
            notifier: arc_notices,
            reward_set_provider: OnChainRewardSetProvider(Some(dispatcher)),
            cost_estimator,
            fee_estimator,
            atlas_config,
            atlas_db: Some(atlas_db),
            config,
            burnchain_indexer,
            refresh_stacker_db: comms.refresh_stacker_db.clone(),
            in_nakamoto_epoch: false,
        };

        loop {
            let bits = comms.wait_on();
            if inst.in_subsequent_nakamoto_reward_cycle() {
                debug!("Coordinator: in subsequent Nakamoto reward cycle");
                if !inst.handle_comms_nakamoto(bits, miner_status.clone()) {
                    return;
                }
            } else if inst.in_first_nakamoto_reward_cycle() {
                debug!("Coordinator: in first Nakamoto reward cycle");
                if !inst.handle_comms_nakamoto(bits, miner_status.clone()) {
                    return;
                }
                if !inst.handle_comms_epoch2(bits, miner_status.clone()) {
                    return;
                }
            } else {
                debug!("Coordinator: in epoch2 reward cycle");
                if !inst.handle_comms_epoch2(bits, miner_status.clone()) {
                    return;
                }
            }
        }
    }

    /// This is the Stacks 2.x coordinator loop body, which handles communications
    /// from the given `comms`.  It returns `true` if the coordinator is still running, and `false`
    /// if not.
    pub fn handle_comms_epoch2(&mut self, bits: u8, miner_status: Arc<Mutex<MinerStatus>>) -> bool {
        // timeout so that we handle Ctrl-C a little gracefully
        if (bits & (CoordinatorEvents::NEW_STACKS_BLOCK as u8)) != 0 {
            signal_mining_blocked(miner_status.clone());
            debug!("Received new stacks block notice");
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

            signal_mining_ready(miner_status.clone());
        }
        if (bits & (CoordinatorEvents::NEW_BURN_BLOCK as u8)) != 0 {
            signal_mining_blocked(miner_status.clone());
            debug!("Received new burn block notice");
            match self.handle_new_burnchain_block() {
                Ok(burn_block_status) => match burn_block_status {
                    NewBurnchainBlockStatus::Ready => {}
                    NewBurnchainBlockStatus::WaitForPox2x(block_hash) => {
                        debug!("Missing canonical Stacks 2.x anchor block {}", &block_hash,);
                    }
                    NewBurnchainBlockStatus::WaitForPoxNakamoto => {
                        debug!("Missing canonical Nakamoto anchor block");
                    }
                },
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

        return true;
    }
}

impl<T: BlockEventDispatcher, U: RewardSetProvider, B: BurnchainHeaderReader>
    ChainsCoordinator<'_, T, (), U, (), (), B>
{
    /// Create a coordinator for testing, with some parameters defaulted to None
    #[cfg(test)]
    pub fn test_new<'a>(
        burnchain: &Burnchain,
        chain_id: u32,
        path: &str,
        reward_set_provider: U,
        indexer: B,
    ) -> ChainsCoordinator<'a, T, (), U, (), (), B> {
        ChainsCoordinator::test_new_full(
            burnchain,
            chain_id,
            path,
            reward_set_provider,
            None,
            indexer,
            None,
        )
    }

    /// Create a coordinator for testing allowing for all configurable params
    #[cfg(test)]
    pub fn test_new_full<'a>(
        burnchain: &Burnchain,
        chain_id: u32,
        path: &str,
        reward_set_provider: U,
        dispatcher: Option<&'a T>,
        burnchain_indexer: B,
        atlas_config: Option<AtlasConfig>,
    ) -> ChainsCoordinator<'a, T, (), U, (), (), B> {
        let burnchain = burnchain.clone();

        let mut boot_data = ChainStateBootData::new(&burnchain, vec![], None);

        let sortition_db = SortitionDB::open(
            &burnchain.get_db_path(),
            true,
            burnchain.pox_constants.clone(),
        )
        .unwrap();
        let burnchain_blocks_db =
            BurnchainDB::open(&burnchain.get_burnchaindb_path(), false).unwrap();
        let (chain_state_db, _) = StacksChainState::open_and_exec(
            false,
            chain_id,
            &format!("{}/chainstate/", path),
            Some(&mut boot_data),
            None,
        )
        .unwrap();
        let canonical_sortition_tip =
            SortitionDB::get_canonical_sortition_tip(sortition_db.conn()).unwrap();

        let atlas_config = atlas_config.unwrap_or(AtlasConfig::new(false));
        let atlas_db = AtlasDB::connect(
            atlas_config.clone(),
            &format!("{}/atlas.sqlite", path),
            true,
        )
        .unwrap();

        ChainsCoordinator {
            canonical_sortition_tip: Some(canonical_sortition_tip),
            burnchain_blocks_db,
            chain_state_db,
            sortition_db,
            burnchain,
            dispatcher,
            cost_estimator: None,
            fee_estimator: None,
            reward_set_provider,
            notifier: (),
            atlas_config,
            atlas_db: Some(atlas_db),
            config: ChainsCoordinatorConfig::test_new(),
            burnchain_indexer,
            refresh_stacker_db: Arc::new(AtomicBool::new(false)),
            in_nakamoto_epoch: false,
        }
    }
}

pub fn get_next_recipients<U: RewardSetProvider>(
    sortition_tip: &BlockSnapshot,
    chain_state: &mut StacksChainState,
    sort_db: &mut SortitionDB,
    burnchain: &Burnchain,
    provider: &U,
    always_use_affirmation_maps: bool,
) -> Result<Option<RewardSetInfo>, Error> {
    let burnchain_db = BurnchainDB::open(&burnchain.get_burnchaindb_path(), false)?;
    let reward_cycle_info = get_reward_cycle_info(
        sortition_tip.block_height + 1,
        &sortition_tip.burn_header_hash,
        &sortition_tip.sortition_id,
        burnchain,
        &burnchain_db,
        chain_state,
        sort_db,
        provider,
        always_use_affirmation_maps,
    )?;
    sort_db
        .get_next_block_recipients(burnchain, sortition_tip, reward_cycle_info.as_ref())
        .map_err(Error::from)
}

/// returns None if this burnchain block is _not_ the start of a reward cycle
///         otherwise, returns the required reward cycle info for this burnchain block
///                     in our current sortition view:
///           * PoX anchor block
///           * Was PoX anchor block known?
pub fn get_reward_cycle_info<U: RewardSetProvider>(
    burn_height: u64,
    parent_bhh: &BurnchainHeaderHash,
    sortition_tip: &SortitionId,
    burnchain: &Burnchain,
    burnchain_db: &BurnchainDB,
    chain_state: &mut StacksChainState,
    sort_db: &mut SortitionDB,
    provider: &U,
    always_use_affirmation_maps: bool,
) -> Result<Option<RewardCycleInfo>, Error> {
    let epoch_at_height = SortitionDB::get_stacks_epoch(sort_db.conn(), burn_height)?
        .unwrap_or_else(|| panic!("FATAL: no epoch defined for burn height {}", burn_height));

    if !burnchain.is_reward_cycle_start(burn_height) {
        return Ok(None);
    }

    let reward_cycle = burnchain
        .block_height_to_reward_cycle(burn_height)
        .expect("FATAL: no reward cycle for burn height");

    if burnchain
        .pox_constants
        .is_after_pox_sunset_end(burn_height, epoch_at_height.epoch_id)
    {
        return Ok(Some(RewardCycleInfo {
            reward_cycle,
            anchor_status: PoxAnchorBlockStatus::NotSelected,
        }));
    }

    debug!("Beginning reward cycle";
           "burn_height" => burn_height,
           "reward_cycle" => reward_cycle,
           "reward_cycle_length" => burnchain.pox_constants.reward_cycle_length,
           "prepare_phase_length" => burnchain.pox_constants.prepare_length);

    let reward_cycle_info = {
        let ic = sort_db.index_handle(sortition_tip);
        let burnchain_db_conn_opt =
            if epoch_at_height.epoch_id >= StacksEpochId::Epoch21 || always_use_affirmation_maps {
                // use the new block-commit-based PoX anchor block selection rules
                Some(burnchain_db.conn())
            } else {
                None
            };

        ic.get_chosen_pox_anchor(burnchain_db_conn_opt, parent_bhh, &burnchain.pox_constants)
    }?;
    let reward_cycle_info =
        if let Some((consensus_hash, stacks_block_hash, txid)) = reward_cycle_info {
            let anchor_block_known = StacksChainState::is_stacks_block_processed(
                chain_state.db(),
                &consensus_hash,
                &stacks_block_hash,
            )?;
            let stacks_block_id = StacksBlockId::new(&consensus_hash, &stacks_block_hash);
            info!(
                "PoX Anchor block selected";
                "cycle" => reward_cycle,
                "consensus_hash" => %consensus_hash,
                "stacks_block_hash" => %stacks_block_hash,
                "stacks_block_id" => %stacks_block_id,
                "is_known" => anchor_block_known,
                "commit_txid" => %txid,
                "cycle_burn_height" => burn_height
            );
            let anchor_status = if anchor_block_known {
                let reward_set = provider.get_reward_set(
                    burn_height,
                    chain_state,
                    burnchain,
                    sort_db,
                    &stacks_block_id,
                )?;
                PoxAnchorBlockStatus::SelectedAndKnown(stacks_block_hash, txid, reward_set)
            } else {
                PoxAnchorBlockStatus::SelectedAndUnknown(stacks_block_hash, txid)
            };
            RewardCycleInfo {
                reward_cycle,
                anchor_status,
            }
        } else {
            info!(
                "PoX anchor block NOT chosen for reward cycle {} at burn height {}",
                reward_cycle, burn_height
            );
            RewardCycleInfo {
                reward_cycle,
                anchor_status: PoxAnchorBlockStatus::NotSelected,
            }
        };

    // cache the reward cycle info as of the first sortition in the prepare phase, so that
    // the first Nakamoto epoch can go find it later.  Subsequent Nakamoto epochs will use the
    // reward set stored to the Nakamoto chain state.
    let ic = sort_db.index_handle(sortition_tip);
    let prev_reward_cycle = burnchain
        .block_height_to_reward_cycle(burn_height)
        .expect("FATAL: no reward cycle for burn height");

    if prev_reward_cycle > 1 {
        let prepare_phase_start = burnchain
            .pox_constants
            .prepare_phase_start(burnchain.first_block_height, prev_reward_cycle - 1);
        let first_prepare_sn =
            SortitionDB::get_ancestor_snapshot(&ic, prepare_phase_start, sortition_tip)?
                .expect("FATAL: no start-of-prepare-phase sortition");

        let mut tx = sort_db.tx_begin()?;
        let preprocessed_reward_set =
            SortitionDB::get_preprocessed_reward_set(&tx, &first_prepare_sn.sortition_id)?;

        // It's possible that we haven't processed the PoX anchor block at the time we have
        // processed the burnchain block which commits to it.  In this case, the PoX anchor block
        // status would be SelectedAndUnknown.  However, it's overwhelmingly likely (and in
        // Nakamoto, _required_) that the PoX anchor block will be processed shortly thereafter.
        // When this happens, we need to _update_ the sortition DB with the newly-processed reward
        // set.  This code performs this check to determine whether or not we need to store this
        // calculated reward set.
        let need_to_store = if let Some(reward_cycle_info) = preprocessed_reward_set {
            // overwrite if we have an unknown anchor block
            !reward_cycle_info.is_reward_info_known()
        } else {
            true
        };
        if need_to_store {
            debug!(
                "Store preprocessed reward set for cycle";
                "reward_cycle" => prev_reward_cycle,
                "prepare-start sortition" => %first_prepare_sn.sortition_id,
                "reward_cycle_info" => format!("{:?}", &reward_cycle_info)
            );
            SortitionDB::store_preprocessed_reward_set(
                &mut tx,
                &first_prepare_sn.sortition_id,
                &reward_cycle_info,
            )?;
        }
        tx.commit()?;
    }

    Ok(Some(reward_cycle_info))
}

/// PoX payout event to be sent to connected event observers
pub struct PaidRewards {
    pub pox: Vec<(PoxAddress, u64)>,
    pub burns: u64,
}

/// Determine the rewards paid for a given set of burnchain operations.  All of these operations
/// ought to be from the same burnchain block.
pub fn calculate_paid_rewards(ops: &[BlockstackOperationType]) -> PaidRewards {
    let mut reward_recipients: HashMap<_, u64> = HashMap::new();
    let mut burn_amt = 0;
    for op in ops.iter() {
        if let BlockstackOperationType::LeaderBlockCommit(commit) = op {
            if commit.commit_outs.is_empty() {
                continue;
            }
            let amt_per_address = commit.burn_fee / (commit.commit_outs.len() as u64);
            for addr in commit.commit_outs.iter() {
                if addr.is_burn() {
                    burn_amt += amt_per_address;
                } else if let Some(prior_amt) = reward_recipients.get_mut(addr) {
                    *prior_amt += amt_per_address;
                } else {
                    reward_recipients.insert(addr.clone(), amt_per_address);
                }
            }
        }
    }
    PaidRewards {
        pox: reward_recipients.into_iter().collect(),
        burns: burn_amt,
    }
}

pub fn dispatcher_announce_burn_ops<T: BlockEventDispatcher>(
    dispatcher: &T,
    burn_header: &BurnchainBlockHeader,
    paid_rewards: PaidRewards,
    reward_recipient_info: Option<RewardSetInfo>,
    consensus_hash: &ConsensusHash,
) {
    let recipients = if let Some(recip_info) = reward_recipient_info {
        recip_info
            .recipients
            .into_iter()
            .map(|(addr, ..)| addr)
            .collect()
    } else {
        vec![]
    };

    dispatcher.announce_burn_block(
        &burn_header.block_hash,
        burn_header.block_height,
        paid_rewards.pox,
        paid_rewards.burns,
        recipients,
        consensus_hash,
    );
}

/// Forget that all Stacks blocks that were mined on descendants of `burn_header` are orphaned.
/// They may be valid again, after a PoX reorg.
fn forget_orphan_stacks_blocks(
    sort_conn: &DBConn,
    chainstate_db_tx: &mut DBTx,
    burn_header: &BurnchainHeaderHash,
    invalidation_height: u64,
) -> Result<(), Error> {
    if let Ok(sns) = SortitionDB::get_all_snapshots_for_burn_block(sort_conn, burn_header) {
        for sn in sns.into_iter() {
            // only retry blocks that are truly in descendant
            // sortitions.
            if sn.sortition && sn.block_height > invalidation_height {
                StacksChainState::forget_orphaned_epoch_data(
                    chainstate_db_tx,
                    &sn.consensus_hash,
                    &sn.winning_stacks_block_hash,
                )?;
            }
        }
    }
    Ok(())
}

/// Consolidate affirmation maps.
/// `sort_am` will be the prefix of the resulting AM.
/// If `given_am` represents more reward cycles than `last_2_05_rc`, then its affirmations will be
/// appended to `sort_am` to compute the consolidated affirmation map.
///
/// This way, the affirmation map reflects affirmations made under the 2.05 rules during epoch 2.05
/// reward cycles, and affirmations made under the 2.1 rules during epoch 2.1.
fn consolidate_affirmation_maps(
    given_am: AffirmationMap,
    sort_am: &AffirmationMap,
    last_2_05_rc: usize,
) -> AffirmationMap {
    let mut am_entries = vec![];
    for i in 0..last_2_05_rc {
        if i < sort_am.affirmations.len() {
            am_entries.push(sort_am.affirmations[i]);
        } else {
            return AffirmationMap::new(am_entries);
        }
    }
    for i in last_2_05_rc..given_am.len() {
        am_entries.push(given_am.affirmations[i]);
    }

    AffirmationMap::new(am_entries)
}

/// Get the heaviest affirmation map, when considering epochs.
/// * In epoch 2.05 and prior, the heaviest AM was the sortition AM.
/// * In epoch 2.1, the reward cycles prior to the 2.1 boundary remain the sortition AM.
pub fn static_get_heaviest_affirmation_map<B: BurnchainHeaderReader>(
    burnchain: &Burnchain,
    indexer: &B,
    burnchain_blocks_db: &BurnchainDB,
    sortition_db: &SortitionDB,
    sortition_tip: &SortitionId,
) -> Result<AffirmationMap, Error> {
    let last_2_05_rc = sortition_db.get_last_epoch_2_05_reward_cycle()? as usize;

    let sort_am = sortition_db.find_sortition_tip_affirmation_map(sortition_tip)?;

    let heaviest_am = BurnchainDB::get_heaviest_anchor_block_affirmation_map(
        burnchain_blocks_db.conn(),
        burnchain,
        indexer,
    )?;

    Ok(consolidate_affirmation_maps(
        heaviest_am,
        &sort_am,
        last_2_05_rc,
    ))
}

/// Get the canonical affirmation map, when considering epochs.
/// * In epoch 2.05 and prior, the heaviest AM was the sortition AM.
/// * In epoch 2.1, the reward cycles prior to the 2.1 boundary remain the sortition AM.
pub fn static_get_canonical_affirmation_map<B: BurnchainHeaderReader>(
    burnchain: &Burnchain,
    indexer: &B,
    burnchain_blocks_db: &BurnchainDB,
    sortition_db: &SortitionDB,
    chain_state_db: &StacksChainState,
    sortition_tip: &SortitionId,
) -> Result<AffirmationMap, Error> {
    let last_2_05_rc = sortition_db.get_last_epoch_2_05_reward_cycle()? as usize;

    let sort_am = sortition_db.find_sortition_tip_affirmation_map(sortition_tip)?;

    let canonical_am = StacksChainState::find_canonical_affirmation_map(
        burnchain,
        indexer,
        burnchain_blocks_db,
        chain_state_db,
    )?;

    Ok(consolidate_affirmation_maps(
        canonical_am,
        &sort_am,
        last_2_05_rc,
    ))
}

fn inner_static_get_stacks_tip_affirmation_map(
    burnchain_blocks_db: &BurnchainDB,
    last_2_05_rc: u64,
    sort_am: &AffirmationMap,
    sortdb_conn: &DBConn,
    canonical_ch: &ConsensusHash,
    canonical_bhh: &BlockHeaderHash,
) -> Result<AffirmationMap, Error> {
    let last_2_05_rc = last_2_05_rc as usize;

    let stacks_am = StacksChainState::find_stacks_tip_affirmation_map(
        burnchain_blocks_db,
        sortdb_conn,
        canonical_ch,
        canonical_bhh,
    )?;

    Ok(consolidate_affirmation_maps(
        stacks_am,
        sort_am,
        last_2_05_rc,
    ))
}

/// Get the canonical Stacks tip affirmation map, when considering epochs.
/// * In epoch 2.05 and prior, the heaviest AM was the sortition AM.
/// * In epoch 2.1, the reward cycles prior to the 2.1 boundary remain the sortition AM
pub fn static_get_stacks_tip_affirmation_map(
    burnchain_blocks_db: &BurnchainDB,
    sortition_db: &SortitionDB,
    sortition_tip: &SortitionId,
    canonical_ch: &ConsensusHash,
    canonical_bhh: &BlockHeaderHash,
) -> Result<AffirmationMap, Error> {
    let last_2_05_rc = sortition_db.get_last_epoch_2_05_reward_cycle()?;
    let sort_am = sortition_db.find_sortition_tip_affirmation_map(sortition_tip)?;
    inner_static_get_stacks_tip_affirmation_map(
        burnchain_blocks_db,
        last_2_05_rc,
        &sort_am,
        sortition_db.conn(),
        canonical_ch,
        canonical_bhh,
    )
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
    /// Process new Stacks blocks.  If we get stuck for want of a missing PoX anchor block, return
    /// its hash.
    pub fn handle_new_stacks_block(&mut self) -> Result<Option<BlockHeaderHash>, Error> {
        debug!("Handle new Stacks block");
        if let Some(pox_anchor) = self.process_ready_blocks()? {
            self.process_new_pox_anchor(pox_anchor, &mut HashSet::new())
        } else {
            Ok(None)
        }
    }

    /// Get all block snapshots and their affirmation maps at a given burnchain block height.
    fn get_snapshots_and_affirmation_maps_at_height(
        &self,
        height: u64,
    ) -> Result<Vec<(BlockSnapshot, AffirmationMap)>, Error> {
        let sort_ids = SortitionDB::get_sortition_ids_at_height(self.sortition_db.conn(), height)?;
        let mut ret = Vec::with_capacity(sort_ids.len());

        for sort_id in sort_ids.iter() {
            let sn = SortitionDB::get_block_snapshot(self.sortition_db.conn(), sort_id)?
                .expect("FATAL: have sortition ID without snapshot");

            let sort_am = self
                .sortition_db
                .find_sortition_tip_affirmation_map(sort_id)?;
            ret.push((sn, sort_am));
        }

        Ok(ret)
    }

    fn get_heaviest_affirmation_map(
        &self,
        sortition_tip: &SortitionId,
    ) -> Result<AffirmationMap, Error> {
        static_get_heaviest_affirmation_map(
            &self.burnchain,
            &self.burnchain_indexer,
            &self.burnchain_blocks_db,
            &self.sortition_db,
            sortition_tip,
        )
    }

    fn get_canonical_affirmation_map(
        &self,
        sortition_tip: &SortitionId,
    ) -> Result<AffirmationMap, Error> {
        static_get_canonical_affirmation_map(
            &self.burnchain,
            &self.burnchain_indexer,
            &self.burnchain_blocks_db,
            &self.sortition_db,
            &self.chain_state_db,
            sortition_tip,
        )
    }

    /// Find the canonical Stacks tip at a given sortition, whose affirmation map is compatible
    /// with the heaviest affirmation map.
    fn find_highest_stacks_block_with_compatible_affirmation_map(
        heaviest_am: &AffirmationMap,
        sort_tip: &SortitionId,
        burnchain_db: &BurnchainDB,
        sort_tx: &mut SortitionDBTx,
        chainstate_conn: &DBConn,
    ) -> Result<(ConsensusHash, BlockHeaderHash, u64), Error> {
        let mut search_height = StacksChainState::get_max_header_height(chainstate_conn)?;
        let last_2_05_rc = SortitionDB::static_get_last_epoch_2_05_reward_cycle(
            sort_tx,
            sort_tx.context.first_block_height,
            &sort_tx.context.pox_constants,
        )?;
        let sort_am = sort_tx.find_sortition_tip_affirmation_map(sort_tip)?;
        loop {
            let mut search_weight = StacksChainState::get_max_affirmation_weight_at_height(
                chainstate_conn,
                search_height,
            )? as i64;
            while search_weight >= 0 {
                let all_headers = StacksChainState::get_all_headers_at_height_and_weight(
                    chainstate_conn,
                    search_height,
                    search_weight as u64,
                )?;
                debug!(
                    "Headers with weight {} height {}: {}",
                    search_weight,
                    search_height,
                    all_headers.len()
                );

                search_weight -= 1;

                for hdr in all_headers {
                    // load this block's affirmation map
                    let am = match inner_static_get_stacks_tip_affirmation_map(
                        burnchain_db,
                        last_2_05_rc,
                        &sort_am,
                        sort_tx,
                        &hdr.consensus_hash,
                        &hdr.anchored_header.block_hash(),
                    ) {
                        Ok(am) => am,
                        Err(Error::ChainstateError(ChainstateError::DBError(
                            DBError::InvalidPoxSortition,
                        ))) => {
                            debug!(
                                "Stacks tip {}/{} is not on a valid sortition",
                                &hdr.consensus_hash,
                                &hdr.anchored_header.block_hash()
                            );
                            continue;
                        }
                        Err(e) => {
                            error!("Failed to query affirmation map: {e:?}");
                            return Err(e);
                        }
                    };

                    // must be compatible with the heaviest AM
                    match StacksChainState::is_block_compatible_with_affirmation_map(
                        &am,
                        heaviest_am,
                    ) {
                        Ok(compat) => {
                            if !compat {
                                debug!("Stacks tip {}/{} affirmation map {} is incompatible with heaviest affirmation map {}",
                                       &hdr.consensus_hash, &hdr.anchored_header.block_hash(), &am, &heaviest_am);
                                continue;
                            }
                        }
                        Err(ChainstateError::DBError(DBError::InvalidPoxSortition)) => {
                            debug!(
                                "Stacks tip {}/{} affirmation map {} is not on a valid sortition",
                                &hdr.consensus_hash,
                                &hdr.anchored_header.block_hash(),
                                &am
                            );
                            continue;
                        }
                        Err(e) => {
                            error!("Failed to query affirmation compatibility: {:?}", &e);
                            return Err(e.into());
                        }
                    }

                    // must reside on this sortition fork
                    let ancestor_sn = match SortitionDB::get_ancestor_snapshot_tx(
                        sort_tx,
                        hdr.burn_header_height.into(),
                        sort_tip,
                    ) {
                        Ok(Some(sn)) => sn,
                        Ok(None) | Err(DBError::InvalidPoxSortition) => {
                            debug!("Stacks tip {}/{} affirmation map {} is not on a chain tipped by sortition {}",
                                   &hdr.consensus_hash, &hdr.anchored_header.block_hash(), &am, sort_tip);
                            continue;
                        }
                        Err(e) => {
                            error!(
                                "Failed to query snapshot ancestor at height {} from {}: {:?}",
                                hdr.burn_header_height, sort_tip, &e
                            );
                            return Err(e.into());
                        }
                    };
                    if !ancestor_sn.sortition
                        || ancestor_sn.winning_stacks_block_hash != hdr.anchored_header.block_hash()
                        || ancestor_sn.consensus_hash != hdr.consensus_hash
                    {
                        debug!(
                            "Stacks tip {}/{} affirmation map {} is not attched to {},{}",
                            &hdr.consensus_hash,
                            &hdr.anchored_header.block_hash(),
                            &am,
                            &ancestor_sn.burn_header_hash,
                            ancestor_sn.block_height
                        );
                        continue;
                    }

                    // found it!
                    debug!(
                        "Canonical Stacks tip of {} is now {}/{} height {} burn height {} AM `{}` weight {}",
                        sort_tip,
                        &hdr.consensus_hash,
                        &hdr.anchored_header.block_hash(),
                        hdr.stacks_block_height,
                        hdr.burn_header_height,
                        &am,
                        am.weight()
                    );
                    return Ok((
                        hdr.consensus_hash,
                        hdr.anchored_header.block_hash(),
                        hdr.stacks_block_height,
                    ));
                }
            }
            if search_height == 0 {
                break;
            } else {
                search_height -= 1;
            }
        }

        // empty chainstate
        return Ok((FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH, 0));
    }

    /// Did the network affirm a different history of sortitions than what our sortition DB and
    /// stacks DB indicate?  This checks both the affirmation map represented by the Stacks chain
    /// tip and the affirmation map represented by the sortition tip against the heaviest
    /// affirmation map.  Both checks are necessary, because both Stacks and sortition state may
    /// need to be invalidated in order to process the new set of sortitions and Stacks blocks that
    /// are consistent with the heaviest affirmation map.
    ///
    /// If so, then return the reward cycle at which they diverged.
    /// If not, return None.
    fn check_chainstate_against_burnchain_affirmations(&self) -> Result<Option<u64>, Error> {
        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;
        let (canonical_ch, canonical_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(self.sortition_db.conn())?;

        let sortition_tip = match &self.canonical_sortition_tip {
            Some(tip) => tip.clone(),
            None => {
                let sn =
                    SortitionDB::get_canonical_burn_chain_tip(self.burnchain_blocks_db.conn())?;
                sn.sortition_id
            }
        };
        let stacks_tip_affirmation_map = static_get_stacks_tip_affirmation_map(
            &self.burnchain_blocks_db,
            &self.sortition_db,
            &sortition_tip,
            &canonical_ch,
            &canonical_bhh,
        )?;

        let sortition_tip_affirmation_map = self
            .sortition_db
            .find_sortition_tip_affirmation_map(&sortition_tip)?;

        let heaviest_am = self.get_heaviest_affirmation_map(&sortition_tip)?;

        let canonical_affirmation_map = self.get_canonical_affirmation_map(&sortition_tip)?;

        debug!(
            "Heaviest anchor block affirmation map is `{}` at height {}, Stacks tip is `{}`, sortition tip is `{}`, canonical is `{}`",
            &heaviest_am,
            canonical_burnchain_tip.block_height,
            &stacks_tip_affirmation_map,
            &sortition_tip_affirmation_map,
            &canonical_affirmation_map,
        );

        // NOTE: a.find_divergence(b) will be `Some(..)` even if a and b have the same prefix,
        // but b happens to be longer.  So, we need to check both `stacks_tip_affirmation_map`
        // and `heaviest_am` against each other depending on their lengths.
        let stacks_changed_reward_cycle_opt = {
            if heaviest_am.len() <= stacks_tip_affirmation_map.len() {
                stacks_tip_affirmation_map.find_divergence(&heaviest_am)
            } else {
                heaviest_am.find_divergence(&stacks_tip_affirmation_map)
            }
        };

        let mut sortition_changed_reward_cycle_opt = {
            if heaviest_am.len() <= sortition_tip_affirmation_map.len() {
                sortition_tip_affirmation_map.find_divergence(&heaviest_am)
            } else {
                heaviest_am.find_divergence(&sortition_tip_affirmation_map)
            }
        };

        if sortition_changed_reward_cycle_opt.is_none()
            && sortition_tip_affirmation_map.len() >= heaviest_am.len()
            && sortition_tip_affirmation_map.len() <= canonical_affirmation_map.len()
        {
            if let Some(divergence_rc) =
                canonical_affirmation_map.find_divergence(&sortition_tip_affirmation_map)
            {
                if divergence_rc + 1 >= (heaviest_am.len() as u64) {
                    // this can arise if there are unaffirmed PoX anchor blocks that are not
                    // reflected in the sortiiton affirmation map
                    debug!("Update sortition-changed reward cycle to {} from canonical affirmation map `{}` (sortition AM is `{}`)",
                        divergence_rc, &canonical_affirmation_map, &sortition_tip_affirmation_map);

                    sortition_changed_reward_cycle_opt = Some(divergence_rc);
                }
            }
        }

        // find the lowest of the two
        let lowest_changed_reward_cycle_opt = match (
            stacks_changed_reward_cycle_opt,
            sortition_changed_reward_cycle_opt,
        ) {
            (Some(a), Some(b)) => {
                if a < b {
                    Some(a)
                } else {
                    Some(b)
                }
            }
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };

        // did the canonical affirmation map change?
        if let Some(changed_reward_cycle) = lowest_changed_reward_cycle_opt {
            let current_reward_cycle = self
                .burnchain
                .block_height_to_reward_cycle(canonical_burnchain_tip.block_height)
                .unwrap_or(0);
            if changed_reward_cycle < current_reward_cycle {
                info!("Sortition anchor block affirmation map `{}` and/or Stacks affirmation map `{}` is no longer compatible with heaviest affirmation map {} in reward cycles {}-{}",
                      &sortition_tip_affirmation_map, &stacks_tip_affirmation_map, &heaviest_am, changed_reward_cycle, current_reward_cycle);

                return Ok(Some(changed_reward_cycle));
            }
        }

        // no reorog
        Ok(None)
    }

    /// Find valid sortitions between two given heights, and given the correct affirmation map.
    /// Returns a height-sorted list of block snapshots whose affirmation maps are cosnistent with
    /// the correct affirmation map.
    fn find_valid_sortitions(
        &self,
        compare_am: &AffirmationMap,
        start_height: u64,
        end_height: u64,
    ) -> Result<(u64, Vec<BlockSnapshot>), Error> {
        // careful -- we might have already procesed sortitions in this
        // reward cycle with this PoX ID, but that were never confirmed
        // by a subsequent prepare phase.
        let mut last_invalidate_start_block = start_height;
        let mut valid_sortitions = vec![];
        for height in start_height..(end_height + 1) {
            let snapshots_and_ams = self.get_snapshots_and_affirmation_maps_at_height(height)?;
            let num_sns = snapshots_and_ams.len();
            debug!("{} snapshots at {}", num_sns, height);

            let mut found = false;
            for (sn, sn_am) in snapshots_and_ams.into_iter() {
                debug!(
                    "Snapshot {} height {} has AM `{sn_am}` (is prefix of `{compare_am}`?: {})",
                    &sn.sortition_id,
                    sn.block_height,
                    &compare_am.has_prefix(&sn_am),
                );
                if compare_am.has_prefix(&sn_am) {
                    // have already processed this sortitoin
                    debug!("Already processed sortition {} at height {} with AM `{sn_am}` on comparative affirmation map {compare_am}", &sn.sortition_id, sn.block_height);
                    found = true;
                    last_invalidate_start_block = height;
                    debug!(
                        "last_invalidate_start_block = {}",
                        last_invalidate_start_block
                    );
                    valid_sortitions.push(sn);
                    break;
                }
            }
            if !found && num_sns > 0 {
                // there are snapshots, and they're all diverged
                debug!(
                    "No snapshot at height {} has an affirmation map that is a prefix of `{}`",
                    height, &compare_am
                );
                break;
            }
        }
        Ok((last_invalidate_start_block, valid_sortitions))
    }

    /// Find out which sortitions will need to be invalidated as part of a PoX reorg, and which
    /// ones will need to be re-validated.
    ///
    /// Returns (first-invalidation-height, last-invalidation-height, revalidation-sort-ids).
    /// * All sortitions in the range [first-invalidation-height, last-invalidation-height) must be
    /// invalidated, since they are no longer consistent with the heaviest affirmation map.  These
    /// heights fall into the reward cycles identified by `changed_reward_cycle` and
    /// `current_reward_cycle`.
    /// * The sortitions identified by `revalidate-sort-ids` are sortitions whose heights come
    /// at or after `last-invalidation-height` but are now valid again (i.e. because they are
    /// consistent with the heaviest affirmation map).
    fn find_invalid_and_revalidated_sortitions(
        &self,
        compare_am: &AffirmationMap,
        changed_reward_cycle: u64,
        current_reward_cycle: u64,
    ) -> Result<Option<(u64, u64, Vec<BlockSnapshot>)>, Error> {
        // find the lowest reward cycle we have to reprocess (which starts at burn
        // block rc_start_block).

        // burn chain height at which we'll invalidate *all* sortitions
        let mut last_invalidate_start_block = 0;

        // burn chain height at which we'll re-try orphaned Stacks blocks, and
        // revalidate the sortitions that were previously invalid but have now been
        // made valid.
        let mut first_invalidate_start_block = 0;

        // set of sortitions that are currently invalid, but could need to be reset
        // as valid.
        let mut valid_sortitions = vec![];

        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;
        let mut diverged = false;
        for rc in changed_reward_cycle..current_reward_cycle {
            debug!(
                "Find invalidated and revalidated sortitions at reward cycle {}",
                rc
            );

            last_invalidate_start_block = self.burnchain.reward_cycle_to_block_height(rc);
            first_invalidate_start_block = last_invalidate_start_block;

            // + 1 because the first sortition of a reward cycle is congruent to 1 mod
            // reward_cycle_length.
            let sort_ids = SortitionDB::get_sortition_ids_at_height(
                self.sortition_db.conn(),
                last_invalidate_start_block + 1,
            )?;

            // find the sortition ID with the shortest affirmation map that is NOT a prefix
            // of the heaviest affirmation map
            let mut found_diverged = false;
            for sort_id in sort_ids.iter() {
                let sort_am = self
                    .sortition_db
                    .find_sortition_tip_affirmation_map(sort_id)?;

                debug!(
                    "Compare {compare_am} as prefix of {sort_am}? {}",
                    compare_am.has_prefix(&sort_am)
                );
                if compare_am.has_prefix(&sort_am) {
                    continue;
                }

                let mut prior_compare_am = compare_am.clone();
                prior_compare_am.pop();

                let mut prior_sort_am = sort_am.clone();
                prior_sort_am.pop();

                debug!(
                    "Compare {} as a prior prefix of {}? {}",
                    &prior_compare_am,
                    &prior_sort_am,
                    prior_compare_am.has_prefix(&prior_sort_am)
                );
                if prior_compare_am.has_prefix(&prior_sort_am) {
                    // this is the first reward cycle where history diverged.
                    found_diverged = true;
                    debug!("{sort_am} diverges from {compare_am}");

                    // careful -- we might have already procesed sortitions in this
                    // reward cycle with this PoX ID, but that were never confirmed
                    // by a subsequent prepare phase.
                    let (new_last_invalidate_start_block, mut next_valid_sortitions) = self
                        .find_valid_sortitions(
                            compare_am,
                            last_invalidate_start_block,
                            canonical_burnchain_tip.block_height,
                        )?;
                    last_invalidate_start_block = new_last_invalidate_start_block;
                    valid_sortitions.append(&mut next_valid_sortitions);
                    break;
                }
            }

            if !found_diverged {
                continue;
            }

            // we may have processed some sortitions correctly within this reward
            // cycle. Advance forward until we find one that we haven't.
            info!(
                "Re-playing sortitions starting within reward cycle {} burn height {}",
                rc, last_invalidate_start_block
            );

            diverged = true;
            break;
        }

        if diverged {
            Ok(Some((
                first_invalidate_start_block,
                last_invalidate_start_block,
                valid_sortitions,
            )))
        } else {
            Ok(None)
        }
    }

    /// Forget that stacks blocks for now-invalidated sortitions are orphaned, because they might
    /// now be valid.  In particular, this applies to a Stacks block that got mined in two PoX
    /// forks.  This can happen at most once between the two forks, but we need to ensure that the
    /// block can be re-processed in that event.
    fn undo_stacks_block_orphaning(
        burnchain_conn: &DBConn,
        burnchain_indexer: &B,
        ic: &SortitionDBConn,
        chainstate_db_tx: &mut DBTx,
        first_invalidate_start_block: u64,
        last_invalidate_start_block: u64,
    ) -> Result<(), Error> {
        debug!(
            "Clear all orphans in burn range {} - {}",
            first_invalidate_start_block, last_invalidate_start_block
        );
        for burn_height in first_invalidate_start_block..(last_invalidate_start_block + 1) {
            let burn_header = match BurnchainDB::get_burnchain_header(
                burnchain_conn,
                burnchain_indexer,
                burn_height,
            )? {
                Some(hdr) => hdr,
                None => {
                    continue;
                }
            };

            debug!(
                "Clear all orphans at {},{}",
                &burn_header.block_hash, burn_header.block_height
            );
            forget_orphan_stacks_blocks(
                ic,
                chainstate_db_tx,
                &burn_header.block_hash,
                burn_height.saturating_sub(1),
            )?;
        }
        Ok(())
    }

    /// Compare the coordinator's heaviest affirmation map to the heaviest affirmation map in the
    /// burnchain DB.  If they are different, then invalidate all sortitions not represented on
    /// the coordinator's heaviest affirmation map that are now represented by the burnchain DB's
    /// heaviest affirmation map.
    ///
    /// Care must be taken to ensure that a sortition that was already created, but invalidated, is
    /// not re-created.  This can happen if the affirmation map flaps, causing a sortition that was
    /// created and invalidated to become valid again.  The code here addresses this by considering
    /// three ranges of sortitions (grouped by reward cycle) when processing a new heaviest
    /// affirmation map:
    ///
    /// * The range of sortitions that are valid in both affirmation maps. These sortitions
    /// correspond to the affirmation maps' common prefix.
    /// * The range of sortitions that exists and are invalid on the coordinator's current
    /// affirmation map, but are valid on the new heaviest affirmation map.  These sortitions
    /// come strictly after the common prefix, and are identified by the variables
    /// `first_invalid_start_block` and `last_invalid_start_block` (which identifies their lowest
    /// and highest block heights).
    /// * The range of sortitions that are currently valid, and need to be invalidated.  This range
    /// comes strictly after the aforementioned previously-invalid-but-now-valid sortition range.
    ///
    /// The code does not modify any sortition state for the common prefix of sortitions.
    ///
    /// The code identifies the second range of previously-invalid-but-now-valid sortitions and marks them
    /// as valid once again.  In addition, it updates the Stacks chainstate DB such that any Stacks
    /// blocks that were orphaned and never processed can be retried with the now-revalidated
    /// sortition.
    ///
    /// The code identifies the third range of now-invalid sortitions and marks them as invalid in
    /// the sortition DB.
    ///
    /// Note that regardless of the affirmation map status, a Stacks block will remain processed
    /// once it gets accepted.  Its underlying sortition may become invalidated, in which case, the
    /// Stacks block would no longer be considered as part of the canonical Stacks fork (since the
    /// canonical Stacks chain tip must reside on a valid sortition).  However, a Stacks block that
    /// should be processed at the end of the day may temporarily be considered orphaned if there
    /// is a "deep" affirmation map reorg that causes at least one reward cycle's sortitions to
    /// be treated as invalid.  This is what necessitates retrying Stacks blocks that have been
    /// downloaded and considered orphaned because they were never processed -- they may in fact be
    /// valid and processable once the node has identified the canonical sortition history!
    ///
    /// The only kinds of errors returned here are database query errors.
    fn handle_affirmation_reorg(&mut self) -> Result<(), Error> {
        // find the stacks chain's affirmation map
        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;

        let sortition_tip = self.canonical_sortition_tip.as_ref().expect(
            "FAIL: processing an affirmation reorg, but don't have a canonical sortition tip",
        );

        let last_2_05_rc = self.sortition_db.get_last_epoch_2_05_reward_cycle()?;

        let sortition_height =
            SortitionDB::get_block_snapshot(self.sortition_db.conn(), sortition_tip)?
                .unwrap_or_else(|| panic!("FATAL: no sortition {sortition_tip}"))
                .block_height;

        let sortition_reward_cycle = self
            .burnchain
            .block_height_to_reward_cycle(sortition_height)
            .unwrap_or(0);

        let heaviest_am = self.get_heaviest_affirmation_map(sortition_tip)?;

        if let Some(changed_reward_cycle) =
            self.check_chainstate_against_burnchain_affirmations()?
        {
            debug!(
                "Canonical sortition tip is {sortition_tip} height {sortition_height} (rc {sortition_reward_cycle}); changed reward cycle is {changed_reward_cycle}"
            );

            if changed_reward_cycle >= sortition_reward_cycle {
                // nothing we can do
                debug!("Changed reward cycle is {changed_reward_cycle} but canonical sortition is in {sortition_reward_cycle}, so no affirmation reorg is possible");
                return Ok(());
            }

            let current_reward_cycle = self
                .burnchain
                .block_height_to_reward_cycle(canonical_burnchain_tip.block_height)
                .unwrap_or(0);

            // sortitions between [first_invalidate_start_block, last_invalidate_start_block) will
            // be invalidated.  Any orphaned Stacks blocks in this range will be forgotten, so they
            // can be retried later with the new sortitions in this burnchain block range.
            //
            // valid_sortitions include all sortitions in this range that are now valid (i.e.
            // they were invalidated before, but will be valid again as a result of this reorg).
            let (first_invalidate_start_block, last_invalidate_start_block, valid_sortitions) =
                match self.find_invalid_and_revalidated_sortitions(
                    &heaviest_am,
                    changed_reward_cycle,
                    current_reward_cycle,
                )? {
                    Some(x) => x,
                    None => {
                        // the sortition AM is consistent with the heaviest AM.
                        // If the sortition AM is not consistent with the canonical AM, then it
                        // means that we have new anchor blocks to consider
                        let canonical_affirmation_map =
                            self.get_canonical_affirmation_map(sortition_tip)?;
                        let sort_am = self
                            .sortition_db
                            .find_sortition_tip_affirmation_map(sortition_tip)?;
                        let revalidation_params = if canonical_affirmation_map.len()
                            == sort_am.len()
                            && canonical_affirmation_map != sort_am
                        {
                            if let Some(diverged_rc) =
                                canonical_affirmation_map.find_divergence(&sort_am)
                            {
                                debug!(
                                    "Sortition AM `{sort_am}` diverges from canonical AM `{canonical_affirmation_map}` at cycle {diverged_rc}"
                                );
                                let (last_invalid_sortition_height, valid_sortitions) = self
                                    .find_valid_sortitions(
                                        &canonical_affirmation_map,
                                        self.burnchain.reward_cycle_to_block_height(diverged_rc),
                                        canonical_burnchain_tip.block_height,
                                    )?;
                                Some((
                                    last_invalid_sortition_height,
                                    self.burnchain
                                        .reward_cycle_to_block_height(sort_am.len() as u64),
                                    valid_sortitions,
                                ))
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        if let Some(x) = revalidation_params {
                            debug!(
                                "Sortition AM `{sort_am}` is not consistent with canonical AM `{canonical_affirmation_map}`"
                            );
                            x
                        } else {
                            // everything is consistent.
                            // Just update the canonical stacks block pointer on the highest valid
                            // sortition.
                            let last_2_05_rc =
                                self.sortition_db.get_last_epoch_2_05_reward_cycle()?;

                            let mut sort_tx = self.sortition_db.tx_begin()?;
                            let (canonical_ch, canonical_bhh, canonical_height) =
                                Self::find_highest_stacks_block_with_compatible_affirmation_map(
                                    &heaviest_am,
                                    sortition_tip,
                                    &self.burnchain_blocks_db,
                                    &mut sort_tx,
                                    self.chain_state_db.db(),
                                )?;

                            let stacks_am = inner_static_get_stacks_tip_affirmation_map(
                                &self.burnchain_blocks_db,
                                last_2_05_rc,
                                &sort_tx.find_sortition_tip_affirmation_map(sortition_tip)?,
                                &sort_tx,
                                &canonical_ch,
                                &canonical_bhh,
                            )?;

                            debug!("Canonical Stacks tip for highest valid sortition {} ({}) is {}/{} height {} am `{}`", &sortition_tip, sortition_height, &canonical_ch, &canonical_bhh, canonical_height, &stacks_am);

                            SortitionDB::revalidate_snapshot_with_block(
                                &sort_tx,
                                sortition_tip,
                                &canonical_ch,
                                &canonical_bhh,
                                canonical_height,
                                Some(true),
                            )?;
                            sort_tx.commit()?;
                            return Ok(());
                        }
                    }
                };

            // check valid_sortitions -- it may correspond to a range of sortitions beyond our
            // current highest-valid sortition (in which case, *do not* revalidate them)
            let valid_sortitions = if let Some(first_sn) = valid_sortitions.first() {
                if first_sn.block_height > sortition_height {
                    debug!("No sortitions to revalidate: highest is {},{}, first candidate is {},{}. Will not revalidate.", sortition_height, &sortition_tip, first_sn.block_height, &first_sn.sortition_id);
                    vec![]
                } else {
                    valid_sortitions
                }
            } else {
                valid_sortitions
            };

            // find our ancestral sortition ID that's the end of the last reward cycle
            // the new affirmation map would have in common with the old affirmation
            // map, and invalidate its descendants
            let ic = self.sortition_db.index_conn();

            // find the burnchain block hash and height of the first burnchain block in which we'll
            // invalidate all descendant sortitions, but retain some previously-invalidated
            // sortitions
            let revalidated_burn_header = BurnchainDB::get_burnchain_header(
                self.burnchain_blocks_db.conn(),
                &self.burnchain_indexer,
                first_invalidate_start_block - 1,
            )
            .expect("FATAL: failed to read burnchain DB")
            .unwrap_or_else(|| {
                panic!(
                    "FATAL: no burnchain block {}",
                    first_invalidate_start_block - 1
                )
            });

            // find the burnchain block hash and height of the first burnchain block in which we'll
            // invalidate all descendant sortitions, no matter what.
            let invalidated_burn_header = BurnchainDB::get_burnchain_header(
                self.burnchain_blocks_db.conn(),
                &self.burnchain_indexer,
                last_invalidate_start_block - 1,
            )
            .expect("FATAL: failed to read burnchain DB")
            .unwrap_or_else(|| {
                panic!(
                    "FATAL: no burnchain block {}",
                    last_invalidate_start_block - 1
                )
            });

            // let invalidation_height = revalidate_sn.block_height;
            let invalidation_height = revalidated_burn_header.block_height;

            debug!("Invalidate all descendants of {} (after height {}), revalidate some sortitions at and after height {}, and retry all orphaned Stacks blocks at or after height {}",
                   &revalidated_burn_header.block_hash, revalidated_burn_header.block_height, invalidated_burn_header.block_height, first_invalidate_start_block);

            let mut highest_valid_sortition_id =
                if sortition_height > last_invalidate_start_block - 1 {
                    let invalidate_sn = SortitionDB::get_ancestor_snapshot(
                        &ic,
                        last_invalidate_start_block - 1,
                        sortition_tip,
                    )?
                    .unwrap_or_else(|| {
                        panic!(
                            "BUG: no ancestral sortition at height {}",
                            last_invalidate_start_block - 1
                        )
                    });

                    valid_sortitions
                        .last()
                        .unwrap_or(&invalidate_sn)
                        .sortition_id
                        .clone()
                } else {
                    sortition_tip.clone()
                };

            let mut stacks_blocks_to_unorphan = vec![];
            let chainstate_db_conn = self.chain_state_db.db();

            self.sortition_db.invalidate_descendants_with_closures(
                &revalidated_burn_header.block_hash,
                |_sort_tx, burn_header, _invalidate_queue| {
                    // do this once in the transaction, after we've invalidated all other
                    // sibling blocks to these now-valid sortitions
                    test_debug!(
                        "Invalidate all sortitions descending from {} ({} remaining)",
                        &burn_header,
                        _invalidate_queue.len()
                    );
                    stacks_blocks_to_unorphan.push((burn_header.clone(), invalidation_height));
                },
                |sort_tx| {
                    // no more sortitions to invalidate -- all now-incompatible
                    // sortitions have been invalidated.
                    let (canonical_ch, canonical_bhh, canonical_height) = Self::find_highest_stacks_block_with_compatible_affirmation_map(&heaviest_am, &highest_valid_sortition_id, &self.burnchain_blocks_db, sort_tx, chainstate_db_conn)
                        .expect("FATAL: could not find a valid parent Stacks block");

                    let stacks_am = inner_static_get_stacks_tip_affirmation_map(
                        &self.burnchain_blocks_db,
                        last_2_05_rc,
                        &sort_tx.find_sortition_tip_affirmation_map(&highest_valid_sortition_id).expect("FATAL: failed to query stacks DB"),
                        sort_tx,
                        &canonical_ch,
                        &canonical_bhh
                    )
                    .expect("FATAL: failed to query stacks DB");

                    debug!("Canonical Stacks tip after invalidations is {}/{} height {} am `{}`", &canonical_ch, &canonical_bhh, canonical_height, &stacks_am);

                    // Revalidate sortitions, and declare that we have their Stacks blocks.
                    for valid_sn in valid_sortitions.iter() {
                        test_debug!("Revalidate snapshot {},{}", valid_sn.block_height, &valid_sn.sortition_id);
                        let block_known = StacksChainState::is_stacks_block_processed(
                            chainstate_db_conn,
                            &valid_sn.consensus_hash,
                            &valid_sn.winning_stacks_block_hash,
                        ).expect("FATAL: failed to query chainstate DB");

                        SortitionDB::revalidate_snapshot_with_block(sort_tx, &valid_sn.sortition_id, &canonical_ch, &canonical_bhh, canonical_height, Some(block_known)).unwrap_or_else(|_| panic!("FATAL: failed to revalidate sortition {}",
                                valid_sn.sortition_id));
                    }

                    // recalculate highest valid sortition with revalidated snapshots
                    highest_valid_sortition_id = if sortition_height > last_invalidate_start_block - 1 {
                        let invalidate_sn = SortitionDB::get_ancestor_snapshot_tx(
                            sort_tx,
                            last_invalidate_start_block - 1,
                            sortition_tip,
                        )
                        .expect("FATAL: failed to query the sortition DB")
                        .unwrap_or_else(|| panic!("BUG: no ancestral sortition at height {}",
                            last_invalidate_start_block - 1));

                        valid_sortitions
                            .last()
                            .unwrap_or(&invalidate_sn)
                            .sortition_id
                            .clone()
                    }
                    else {
                        sortition_tip.clone()
                    };

                    // recalculate highest valid stacks tip
                    let (canonical_ch, canonical_bhh, canonical_height) = Self::find_highest_stacks_block_with_compatible_affirmation_map(&heaviest_am, &highest_valid_sortition_id, &self.burnchain_blocks_db, sort_tx, chainstate_db_conn)
                        .expect("FATAL: could not find a valid parent Stacks block");

                    let stacks_am = inner_static_get_stacks_tip_affirmation_map(
                        &self.burnchain_blocks_db,
                        last_2_05_rc,
                        &sort_tx.find_sortition_tip_affirmation_map(&highest_valid_sortition_id).expect("FATAL: failed to query stacks DB"),
                        sort_tx,
                        &canonical_ch,
                        &canonical_bhh
                    )
                    .expect("FATAL: failed to query stacks DB");

                    debug!("Canonical Stacks tip after invalidations and revalidations is {}/{} height {} am `{}`", &canonical_ch, &canonical_bhh, canonical_height, &stacks_am);

                    // update dirty canonical block pointers.
                    let dirty_snapshots = SortitionDB::find_snapshots_with_dirty_canonical_block_pointers(sort_tx, canonical_height)
                        .expect("FATAL: failed to find dirty snapshots");

                    for dirty_sort_id in dirty_snapshots.iter() {
                        test_debug!("Revalidate dirty snapshot {}", dirty_sort_id);

                        let dirty_sort_sn = SortitionDB::get_block_snapshot(sort_tx, dirty_sort_id)
                            .expect("FATAL: failed to query sortition DB")
                            .expect("FATAL: no such dirty sortition");

                        let block_known = StacksChainState::is_stacks_block_processed(
                            chainstate_db_conn,
                            &dirty_sort_sn.consensus_hash,
                            &dirty_sort_sn.winning_stacks_block_hash,
                        ).expect("FATAL: failed to query chainstate DB");

                        SortitionDB::revalidate_snapshot_with_block(sort_tx, dirty_sort_id, &canonical_ch, &canonical_bhh, canonical_height, Some(block_known)).unwrap_or_else(|_| panic!("FATAL: failed to revalidate dirty sortition {}",
                                dirty_sort_id));
                    }

                    // recalculate highest valid stacks tip once more
                    let (canonical_ch, canonical_bhh, canonical_height) = Self::find_highest_stacks_block_with_compatible_affirmation_map(&heaviest_am, &highest_valid_sortition_id, &self.burnchain_blocks_db, sort_tx, chainstate_db_conn)
                        .expect("FATAL: could not find a valid parent Stacks block");

                    let stacks_am = inner_static_get_stacks_tip_affirmation_map(
                        &self.burnchain_blocks_db,
                        last_2_05_rc,
                        &sort_tx.find_sortition_tip_affirmation_map(&highest_valid_sortition_id).expect("FATAL: failed to query stacks DB"),
                        sort_tx,
                        &canonical_ch,
                        &canonical_bhh
                    )
                    .expect("FATAL: failed to query stacks DB");

                    debug!("Canonical Stacks tip after invalidations, revalidations, and processed dirty snapshots is {}/{} height {} am `{}`", &canonical_ch, &canonical_bhh, canonical_height, &stacks_am);

                    let highest_valid_sn = SortitionDB::get_block_snapshot(sort_tx, &highest_valid_sortition_id)
                        .expect("FATAL: failed to query sortition ID")
                        .expect("FATAL: highest valid sortition ID does not have a snapshot");

                    let block_known = StacksChainState::is_stacks_block_processed(
                        chainstate_db_conn,
                        &highest_valid_sn.consensus_hash,
                        &highest_valid_sn.winning_stacks_block_hash,
                    ).expect("FATAL: failed to query chainstate DB");

                    SortitionDB::revalidate_snapshot_with_block(sort_tx, &highest_valid_sortition_id, &canonical_ch, &canonical_bhh, canonical_height, Some(block_known)).unwrap_or_else(|_| panic!("FATAL: failed to revalidate highest valid sortition {}",
                            &highest_valid_sortition_id));
                },
            )?;

            let ic = self.sortition_db.index_conn();

            let mut chainstate_db_tx = self.chain_state_db.db_tx_begin()?;
            for (burn_header, invalidation_height) in stacks_blocks_to_unorphan {
                // permit re-processing of any associated stacks blocks if they're
                // orphaned
                forget_orphan_stacks_blocks(
                    &ic,
                    &mut chainstate_db_tx,
                    &burn_header,
                    invalidation_height,
                )?;
            }

            // un-orphan blocks that had been orphaned but were tied to this now-revalidated sortition history
            Self::undo_stacks_block_orphaning(
                self.burnchain_blocks_db.conn(),
                &self.burnchain_indexer,
                &ic,
                &mut chainstate_db_tx,
                first_invalidate_start_block,
                last_invalidate_start_block,
            )?;

            // by holding this lock as long as we do, we ensure that the sortition DB's
            // view of the canonical stacks chain tip can't get changed (since no
            // Stacks blocks can be processed).
            chainstate_db_tx.commit().map_err(DBError::SqliteError)?;

            let highest_valid_snapshot = SortitionDB::get_block_snapshot(
                self.sortition_db.conn(),
                &highest_valid_sortition_id,
            )?
            .expect("FATAL: highest valid sortition doesn't exist");

            let stacks_tip_affirmation_map = static_get_stacks_tip_affirmation_map(
                &self.burnchain_blocks_db,
                &self.sortition_db,
                &highest_valid_snapshot.sortition_id,
                &highest_valid_snapshot.canonical_stacks_tip_consensus_hash,
                &highest_valid_snapshot.canonical_stacks_tip_hash,
            )?;

            debug!(
                "Highest valid sortition (changed) is {} ({} in height {}, affirmation map {}); Stacks tip is {}/{} height {} (affirmation map {}); heaviest AM is {}",
                &highest_valid_snapshot.sortition_id,
                &highest_valid_snapshot.burn_header_hash,
                highest_valid_snapshot.block_height,
                &self.sortition_db.find_sortition_tip_affirmation_map(&highest_valid_snapshot.sortition_id)?,
                &highest_valid_snapshot.canonical_stacks_tip_consensus_hash,
                &highest_valid_snapshot.canonical_stacks_tip_hash,
                highest_valid_snapshot.canonical_stacks_tip_height,
                &stacks_tip_affirmation_map,
                &heaviest_am
            );

            self.canonical_sortition_tip = Some(highest_valid_snapshot.sortition_id);
        } else {
            let highest_valid_snapshot =
                SortitionDB::get_block_snapshot(self.sortition_db.conn(), sortition_tip)?
                    .expect("FATAL: highest valid sortition doesn't exist");

            let stacks_tip_affirmation_map = static_get_stacks_tip_affirmation_map(
                &self.burnchain_blocks_db,
                &self.sortition_db,
                &highest_valid_snapshot.sortition_id,
                &highest_valid_snapshot.canonical_stacks_tip_consensus_hash,
                &highest_valid_snapshot.canonical_stacks_tip_hash,
            )?;

            debug!(
                "Highest valid sortition (not changed) is {} ({} in height {}, affirmation map {}); Stacks tip is {}/{} height {} (affirmation map {}); heaviest AM is {}",
                &highest_valid_snapshot.sortition_id,
                &highest_valid_snapshot.burn_header_hash,
                highest_valid_snapshot.block_height,
                &self.sortition_db.find_sortition_tip_affirmation_map(&highest_valid_snapshot.sortition_id)?,
                &highest_valid_snapshot.canonical_stacks_tip_consensus_hash,
                &highest_valid_snapshot.canonical_stacks_tip_hash,
                highest_valid_snapshot.canonical_stacks_tip_height,
                &stacks_tip_affirmation_map,
                &heaviest_am
            );
        }

        Ok(())
    }

    /// Use the network's affirmations to re-interpret our local PoX anchor block status into what
    /// the network affirmed was their PoX anchor block statuses.
    /// If we're blocked on receiving a new anchor block that we don't have (i.e. the network
    /// affirmed that it exists), then indicate so by returning its hash.
    fn reinterpret_affirmed_pox_anchor_block_status(
        &self,
        canonical_affirmation_map: &AffirmationMap,
        header: &BurnchainBlockHeader,
        rc_info: &mut RewardCycleInfo,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        // re-calculate the reward cycle info's anchor block status, based on what
        // the network has affirmed in each prepare phase.

        // is this anchor block affirmed?  Only process it if so!
        let new_reward_cycle = self
            .burnchain
            .block_height_to_reward_cycle(header.block_height)
            .expect("BUG: processed block before start of epoch 2.1");

        test_debug!(
            "Verify affirmation against PoX info in reward cycle {} canonical affirmation map {}",
            new_reward_cycle,
            canonical_affirmation_map
        );

        let new_status = if new_reward_cycle > 0
            && new_reward_cycle <= (canonical_affirmation_map.len() as u64)
        {
            let affirmed_rc = new_reward_cycle - 1;

            // we're processing an anchor block from an earlier reward cycle,
            // meaning that we're in the middle of an affirmation reorg.
            let affirmation = canonical_affirmation_map
                .at(affirmed_rc)
                .expect("BUG: checked index overflow")
                .to_owned();
            test_debug!("Affirmation '{affirmation}' for anchor block of previous reward cycle {affirmed_rc} canonical affirmation map {canonical_affirmation_map}");

            // switch reward cycle info assessment based on what the network
            // affirmed.
            match &rc_info.anchor_status {
                PoxAnchorBlockStatus::SelectedAndKnown(block_hash, txid, reward_set) => {
                    match affirmation {
                        AffirmationMapEntry::PoxAnchorBlockPresent => {
                            // matches affirmation
                            PoxAnchorBlockStatus::SelectedAndKnown(
                                block_hash.clone(),
                                txid.clone(),
                                reward_set.clone(),
                            )
                        }
                        AffirmationMapEntry::PoxAnchorBlockAbsent => {
                            // network actually affirms that this anchor block
                            // is absent.
                            warn!("Chose PoX anchor block for reward cycle {affirmed_rc}, but it is affirmed absent by the network"; "affirmation map" => %&canonical_affirmation_map);
                            PoxAnchorBlockStatus::SelectedAndUnknown(
                                block_hash.clone(),
                                txid.clone(),
                            )
                        }
                        AffirmationMapEntry::Nothing => {
                            // no anchor block selected either way
                            PoxAnchorBlockStatus::NotSelected
                        }
                    }
                }
                PoxAnchorBlockStatus::SelectedAndUnknown(ref block_hash, ref txid) => {
                    match affirmation {
                        AffirmationMapEntry::PoxAnchorBlockPresent => {
                            // the network affirms that this anchor block
                            // exists, but we don't have it locally.  Stop
                            // processing here and wait for it to arrive, via
                            // the downloader.
                            info!("Anchor block {block_hash} (txid {txid}) for reward cycle {affirmed_rc} is affirmed by the network ({canonical_affirmation_map}), but must be downloaded");
                            return Ok(Some(block_hash.clone()));
                        }
                        AffirmationMapEntry::PoxAnchorBlockAbsent => {
                            // matches affirmation
                            PoxAnchorBlockStatus::SelectedAndUnknown(
                                block_hash.clone(),
                                txid.clone(),
                            )
                        }
                        AffirmationMapEntry::Nothing => {
                            // no anchor block selected either way
                            PoxAnchorBlockStatus::NotSelected
                        }
                    }
                }
                PoxAnchorBlockStatus::NotSelected => {
                    // no anchor block selected either way
                    PoxAnchorBlockStatus::NotSelected
                }
            }
        } else {
            // no-op: our view of the set of anchor blocks is consistent with
            // the canonical affirmation map, so the status of this new anchor
            // block is whatever it was calculated to be.
            rc_info.anchor_status.clone()
        };

        // update new status
        debug!(
            "Update anchor block status for reward cycle {} from {:?} to {:?}",
            new_reward_cycle, &rc_info.anchor_status, &new_status
        );
        rc_info.anchor_status = new_status;
        Ok(None)
    }

    /// Try to revalidate a sortition if it exists already.  This can happen if the node flip/flops
    /// between two PoX forks.
    ///
    /// If it succeeds, then return the revalidated snapshot.  Otherwise, return None
    fn try_revalidate_sortition(
        &mut self,
        canonical_snapshot: &BlockSnapshot,
        header: &BurnchainBlockHeader,
        last_processed_ancestor: &SortitionId,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<BlockSnapshot>, Error> {
        let parent_sort_id = self
            .sortition_db
            .get_sortition_id(&header.parent_block_hash, last_processed_ancestor)?
            .ok_or_else(|| {
                warn!("Unknown block {:?}", header.parent_block_hash);
                BurnchainError::MissingParentBlock
            })?;

        let parent_pox = {
            let mut sortition_db_handle =
                SortitionHandleTx::begin(&mut self.sortition_db, &parent_sort_id)?;
            let parent_pox = sortition_db_handle.get_pox_id()?;
            parent_pox
        };

        let new_sortition_id =
            SortitionDB::make_next_sortition_id(parent_pox, &header.block_hash, next_pox_info);
        let sortition_opt =
            SortitionDB::get_block_snapshot(self.sortition_db.conn(), &new_sortition_id)?;

        if let Some(sortition) = sortition_opt {
            // existing sortition -- go revalidate it
            info!(
                "Revalidate already-processed snapshot {} height {} to have canonical tip {}/{} height {}",
                &new_sortition_id, sortition.block_height,
                &canonical_snapshot.canonical_stacks_tip_consensus_hash,
                &canonical_snapshot.canonical_stacks_tip_hash,
                canonical_snapshot.canonical_stacks_tip_height,
            );

            let tx = self.sortition_db.tx_begin()?;
            SortitionDB::revalidate_snapshot_with_block(
                &tx,
                &new_sortition_id,
                &canonical_snapshot.canonical_stacks_tip_consensus_hash,
                &canonical_snapshot.canonical_stacks_tip_hash,
                canonical_snapshot.canonical_stacks_tip_height,
                Some(false), // we'll mark it processed after this call, if it's still valid.
            )?;
            tx.commit()?;

            Ok(Some(sortition))
        } else {
            Ok(None)
        }
    }

    /// Check to see if the discovery of a PoX anchor block means it's time to process a new reward
    /// cycle.  Based on the canonical affirmation map, this may not always be the case.
    ///
    /// This mutates `rc_info` to be the affirmed anchor block status.
    ///
    /// Returns Ok(Some(...)) if we have a _missing_ PoX anchor block that _must be_ downloaded
    /// before burnchain processing can continue.
    /// Returns Ok(None) if not
    fn check_missing_anchor_block(
        &self,
        header: &BurnchainBlockHeader,
        canonical_affirmation_map: &AffirmationMap,
        rc_info: &mut RewardCycleInfo,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        let cur_epoch =
            SortitionDB::get_stacks_epoch(self.sortition_db.conn(), header.block_height)?
                .unwrap_or_else(|| {
                    panic!("BUG: no epoch defined at height {}", header.block_height)
                });

        if self.config.assume_present_anchor_blocks {
            // anchor blocks are always assumed to be present in the chain history,
            // so report its absence if we don't have it.
            if let PoxAnchorBlockStatus::SelectedAndUnknown(missing_anchor_block, _) =
                &rc_info.anchor_status
            {
                info!(
                    "Currently missing PoX anchor block {}, which is assumed to be present",
                    &missing_anchor_block
                );
                return Ok(Some(missing_anchor_block.clone()));
            }
        }

        if cur_epoch.epoch_id >= StacksEpochId::Epoch21 || self.config.always_use_affirmation_maps {
            // potentially have an anchor block, but only process the next reward cycle (and
            // subsequent reward cycles) with it if the prepare-phase block-commits affirm its
            // presence.  This only gets checked in Stacks 2.1 or later (unless overridden
            // in the config)

            // NOTE: this mutates rc_info if it returns None
            if let Some(missing_anchor_block) = self.reinterpret_affirmed_pox_anchor_block_status(
                canonical_affirmation_map,
                header,
                rc_info,
            )? {
                if self.config.require_affirmed_anchor_blocks {
                    // missing this anchor block -- cannot proceed until we have it
                    info!(
                        "Burnchain block processing stops due to missing affirmed anchor stacks block hash {missing_anchor_block}"
                    );
                    return Ok(Some(missing_anchor_block));
                } else {
                    // this and descendant sortitions might already exist
                    info!("Burnchain block processing will continue in spite of missing affirmed anchor stacks block hash {missing_anchor_block}");
                }
            }
        }

        test_debug!(
            "Reward cycle info at height {}: {:?}",
            &header.block_height,
            &rc_info
        );
        Ok(None)
    }

    /// Outermost call to process a burnchain block.
    /// Will call the Stacks 2.x or Nakamoto handler, depending on whether or not
    /// Not called internally.
    pub fn handle_new_burnchain_block(&mut self) -> Result<NewBurnchainBlockStatus, Error> {
        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;
        let epochs = SortitionDB::get_stacks_epochs(self.sortition_db.conn())?;
        let target_epoch_index =
            StacksEpoch::find_epoch(&epochs, canonical_burnchain_tip.block_height)
                .expect("FATAL: epoch not defined for burnchain height");
        let target_epoch = epochs
            .get(target_epoch_index)
            .expect("FATAL: StacksEpoch::find_epoch() returned an invalid index");
        if target_epoch.epoch_id < StacksEpochId::Epoch30 {
            // burnchain has not yet advanced to epoch 3.0
            return self
                .handle_new_epoch2_burnchain_block(&mut HashSet::new())
                .map(|block_hash_opt| {
                    if let Some(block_hash) = block_hash_opt {
                        NewBurnchainBlockStatus::WaitForPox2x(block_hash)
                    } else {
                        NewBurnchainBlockStatus::Ready
                    }
                });
        }

        // burnchain has advanced to epoch 3.0, but has our sortition DB?
        let canonical_snapshot = match self.canonical_sortition_tip.as_ref() {
            Some(sn_tip) => SortitionDB::get_block_snapshot(self.sortition_db.conn(), sn_tip)?
                .unwrap_or_else(|| {
                    panic!(
                        "FATAL: do not have previously-calculated highest valid sortition tip {}",
                        sn_tip
                    )
                }),
            None => SortitionDB::get_canonical_burn_chain_tip(self.sortition_db.conn())?,
        };
        let target_epoch_index = StacksEpoch::find_epoch(&epochs, canonical_snapshot.block_height)
            .expect("FATAL: epoch not defined for BlockSnapshot height");
        let target_epoch = epochs
            .get(target_epoch_index)
            .expect("FATAL: StacksEpoch::find_epoch() returned an invalid index");

        if target_epoch.epoch_id < StacksEpochId::Epoch30 {
            // need to catch the sortition DB up
            self.handle_new_epoch2_burnchain_block(&mut HashSet::new())?;
        }

        // proceed to process sortitions in epoch 3.0
        self.handle_new_nakamoto_burnchain_block()
            .map(|can_proceed| {
                if can_proceed {
                    NewBurnchainBlockStatus::Ready
                } else {
                    // missing PoX anchor block, but unlike in 2.x, we don't know what it is!
                    NewBurnchainBlockStatus::WaitForPoxNakamoto
                }
            })
    }

    /// Are affirmation maps active during the epoch?
    fn affirmation_maps_active(&self, epoch: &StacksEpochId) -> bool {
        if *epoch >= StacksEpochId::Epoch21 {
            return true;
        } else if self.config.always_use_affirmation_maps {
            return true;
        }
        return false;
    }

    // TODO: add tests from mutation testing results #4852
    #[cfg_attr(test, mutants::skip)]
    /// Handle a new burnchain block, optionally rolling back the canonical PoX sortition history
    /// and setting it up to be replayed in the event the network affirms a different history.  If
    /// this happens, *and* if re-processing the new affirmed history is *blocked on* the
    /// unavailability of a PoX anchor block that *must now* exist, then return the hash of this
    /// anchor block.
    pub fn handle_new_epoch2_burnchain_block(
        &mut self,
        already_processed_burn_blocks: &mut HashSet<BurnchainHeaderHash>,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        debug!("Handle new burnchain block");

        let last_2_05_rc = self.sortition_db.get_last_epoch_2_05_reward_cycle()?;

        // first, see if the canonical affirmation map has changed.  If so, this will wind back the
        // canonical sortition tip.
        //
        // only do this if affirmation maps are supported in this epoch.
        let before_canonical_snapshot = match self.canonical_sortition_tip.as_ref() {
            Some(sn_tip) => SortitionDB::get_block_snapshot(self.sortition_db.conn(), sn_tip)?
                .unwrap_or_else(|| {
                    panic!(
                        "FATAL: do not have previously-calculated highest valid sortition tip {}",
                        sn_tip
                    )
                }),
            None => SortitionDB::get_canonical_burn_chain_tip(self.sortition_db.conn())?,
        };
        let cur_epoch = SortitionDB::get_stacks_epoch(
            self.sortition_db.conn(),
            before_canonical_snapshot.block_height,
        )?
        .unwrap_or_else(|| {
            panic!(
                "BUG: no epoch defined at height {}",
                before_canonical_snapshot.block_height
            )
        });

        if self.affirmation_maps_active(&cur_epoch.epoch_id) {
            self.handle_affirmation_reorg()?;
        }

        // Retrieve canonical burnchain chain tip from the BurnchainBlocksDB
        let canonical_snapshot = match self.canonical_sortition_tip.as_ref() {
            Some(sn_tip) => SortitionDB::get_block_snapshot(self.sortition_db.conn(), sn_tip)?
                .unwrap_or_else(|| {
                    panic!(
                        "FATAL: do not have previously-calculated highest valid sortition tip {}",
                        sn_tip
                    )
                }),
            None => SortitionDB::get_canonical_burn_chain_tip(self.sortition_db.conn())?,
        };

        let canonical_burnchain_tip = self.burnchain_blocks_db.get_canonical_chain_tip()?;
        let canonical_affirmation_map =
            self.get_canonical_affirmation_map(&canonical_snapshot.sortition_id)?;

        let heaviest_am = self.get_heaviest_affirmation_map(&canonical_snapshot.sortition_id)?;

        debug!("Handle new canonical burnchain tip";
               "height" => %canonical_burnchain_tip.block_height,
               "block_hash" => %canonical_burnchain_tip.block_hash.to_string());

        // Retrieve all the direct ancestors of this block with an unprocessed sortition
        let mut cursor = canonical_burnchain_tip.block_hash.clone();
        let mut sortitions_to_process = VecDeque::new();

        // We halt the ancestry research as soon as we find a processed parent
        let mut last_processed_ancestor = loop {
            if let Some(found_sortition) = self.sortition_db.is_sortition_processed(&cursor)? {
                debug!("Ancestor sortition {found_sortition} of block {cursor} is processed");
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

        let burn_header_hashes: Vec<_> = sortitions_to_process
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
            "Unprocessed burn chain blocks [{}]",
            burn_header_hashes.join(", ")
        );

        // if this is set to true, the notify that a stacks block has been processed.
        // this wakes up anyone waiting for their block to have been processed.
        let mut revalidated_stacks_block = false;

        for unprocessed_block in sortitions_to_process.into_iter() {
            let BurnchainBlockData { header, ops } = unprocessed_block;

            // only evaluate epoch 2.x.
            // NOTE: epoch 3 starts _right after_ the first block in the first epoch3 reward cycle,
            // so we use the 2.x rules to process the PoX reward set.
            let sortition_epoch =
                SortitionDB::get_stacks_epoch(self.sortition_db.conn(), header.block_height)?
                    .expect("FATAL: no epoch defined for a valid block height");

            if sortition_epoch.epoch_id >= StacksEpochId::Epoch30 {
                // stop processing
                break;
            }

            if already_processed_burn_blocks.contains(&header.block_hash) {
                // don't re-process something we recursively processed already, by means of finding
                // a heretofore missing anchor block
                continue;
            }

            let reward_cycle = self
                .burnchain
                .block_height_to_reward_cycle(header.block_height)
                .unwrap_or(u64::MAX);

            debug!(
                "Process burn block {} reward cycle {} in {}",
                header.block_height, reward_cycle, &self.burnchain.working_dir,
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

            // at this point, we need to figure out if the sortition we are
            //  about to process is the first block in reward cycle, and if so,
            //  whether or not there ought to be an anchor block.
            let mut reward_cycle_info = self.get_reward_cycle_info(&header)?;

            if let Some(rc_info) = reward_cycle_info.as_mut() {
                if let Some(missing_anchor_block) =
                    self.check_missing_anchor_block(&header, &canonical_affirmation_map, rc_info)?
                {
                    info!(
                        "Burnchain block processing stops due to missing affirmed anchor stacks block hash {}",
                        &missing_anchor_block
                    );
                    return Ok(Some(missing_anchor_block));
                }
            }

            // track a list of (consensus hash, parent block hash, block hash, height) pairs of revalidated sortitions whose
            // blocks will need to be re-marked as accepted.
            let mut stacks_blocks_to_reaccept = vec![];

            // track a list of (burn header, burn block height) pairs for revalidated sortitions whose
            // blocks we need to un-orphan
            let mut unorphan_blocks = vec![];

            let next_snapshot = {
                // if this sortition exists already, then revalidate it with the canonical Stacks
                // tip.  Otherwise, process it.  This can be necessary if we're trying to mine
                // while not having all canonical PoX anchor blocks.
                if let Some(sortition) = self.try_revalidate_sortition(
                    &canonical_snapshot,
                    &header,
                    &last_processed_ancestor,
                    reward_cycle_info.as_ref(),
                )? {
                    if sortition.sortition {
                        if let Some(stacks_block_header) =
                            StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                                self.chain_state_db.db(),
                                &StacksBlockId::new(
                                    &sortition.consensus_hash,
                                    &sortition.winning_stacks_block_hash,
                                ),
                            )?
                        {
                            // we accepted this block
                            debug!(
                                "Will re-accept Stacks block {}/{} height {}",
                                &sortition.consensus_hash,
                                &sortition.winning_stacks_block_hash,
                                stacks_block_header.anchored_header.height(),
                            );
                            stacks_blocks_to_reaccept.push((
                                sortition.consensus_hash.clone(),
                                sortition.winning_stacks_block_hash.clone(),
                                stacks_block_header.anchored_header.height(),
                            ));
                        } else {
                            debug!(
                                "Will un-orphan Stacks block {}/{} if it is orphaned",
                                &sortition.consensus_hash, &sortition.winning_stacks_block_hash
                            );
                            unorphan_blocks.push((sortition.burn_header_hash, 0));
                        }
                    }
                    sortition
                } else {
                    // bind a reference here to avoid tripping up the borrow-checker
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

                    next_snapshot
                }
            };

            // don't process this burnchain block again in this recursive call.
            already_processed_burn_blocks.insert(next_snapshot.burn_header_hash);

            let mut compatible_stacks_blocks = vec![];
            {
                // get borrow checker to drop sort_tx
                let mut sort_tx = self.sortition_db.tx_begin()?;
                for (ch, bhh, height) in stacks_blocks_to_reaccept.into_iter() {
                    debug!(
                        "Check if Stacks block {}/{} height {} is compatible with `{}`",
                        &ch, &bhh, height, &heaviest_am
                    );

                    let am = inner_static_get_stacks_tip_affirmation_map(
                        &self.burnchain_blocks_db,
                        last_2_05_rc,
                        &sort_tx.find_sortition_tip_affirmation_map(&next_snapshot.sortition_id)?,
                        &sort_tx,
                        &ch,
                        &bhh,
                    )?;
                    if StacksChainState::is_block_compatible_with_affirmation_map(
                        &am,
                        &heaviest_am,
                    )? {
                        debug!(
                            "Stacks block {}/{} height {} is compatible with `{}`; will reaccept",
                            &ch, &bhh, height, &heaviest_am
                        );
                        compatible_stacks_blocks.push((ch, bhh, height));
                    } else {
                        debug!("Stacks block {}/{} height {} is NOT compatible with `{}`; will NOT reaccept", &ch, &bhh, height, &heaviest_am);
                    }
                }
            }

            // reaccept any stacks blocks
            let mut sortition_db_handle =
                SortitionHandleTx::begin(&mut self.sortition_db, &next_snapshot.sortition_id)?;

            for (ch, bhh, height) in compatible_stacks_blocks.into_iter() {
                debug!("Re-accept Stacks block {}/{} height {}", &ch, &bhh, height);
                revalidated_stacks_block = true;
                sortition_db_handle.set_stacks_block_accepted(&ch, &bhh, height)?;
            }
            sortition_db_handle.commit()?;

            if !unorphan_blocks.is_empty() {
                revalidated_stacks_block = true;
                let ic = self.sortition_db.index_conn();
                let mut chainstate_db_tx = self.chain_state_db.db_tx_begin()?;
                for (burn_header, invalidation_height) in unorphan_blocks {
                    // permit re-processing of any associated stacks blocks if they're
                    // orphaned
                    forget_orphan_stacks_blocks(
                        &ic,
                        &mut chainstate_db_tx,
                        &burn_header,
                        invalidation_height,
                    )?;
                }
                chainstate_db_tx.commit().map_err(DBError::SqliteError)?;
            }

            let sortition_id = next_snapshot.sortition_id;

            self.notifier.notify_sortition_processed();
            if revalidated_stacks_block {
                debug!("Bump Stacks block(s) reprocessed");
                self.notifier.notify_stacks_block_processed();
            }

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

            // we may already have the associated Stacks block, but linked to a different sortition
            // history.  For example, if an anchor block was selected but PoX was voted disabled or
            // not voted to activate, then the same Stacks blocks could be chosen but with
            // different consensus hashes.  So, check here if we happen to already have the block
            // stored, and proceed to put it into staging again.
            if next_snapshot.sortition {
                self.try_replay_stacks_block(&canonical_snapshot, &next_snapshot)?;
            }

            if let Some(pox_anchor) = self.process_ready_blocks()? {
                if let Some(expected_anchor_block_hash) =
                    self.process_new_pox_anchor(pox_anchor, already_processed_burn_blocks)?
                {
                    info!(
                        "Burnchain block processing stops due to missing affirmed anchor stacks block hash {}",
                        &expected_anchor_block_hash
                    );
                    return Ok(Some(expected_anchor_block_hash));
                }
            }
        }

        // make sure our memoized canonical stacks tip is correct
        let chainstate_db_conn = self.chain_state_db.db();
        let mut sort_tx = self.sortition_db.tx_begin()?;

        // Retrieve canonical burnchain chain tip from the BurnchainBlocksDB
        let canonical_snapshot = match self.canonical_sortition_tip.as_ref() {
            Some(sn_tip) => {
                SortitionDB::get_block_snapshot(&sort_tx, sn_tip)?.unwrap_or_else(|| {
                    panic!(
                        "FATAL: do not have previously-calculated highest valid sortition tip {}",
                        sn_tip
                    )
                })
            }
            None => SortitionDB::get_canonical_burn_chain_tip(&sort_tx)?,
        };
        let highest_valid_sortition_id = canonical_snapshot.sortition_id;

        let (canonical_ch, canonical_bhh, canonical_height) =
            Self::find_highest_stacks_block_with_compatible_affirmation_map(
                &heaviest_am,
                &highest_valid_sortition_id,
                &self.burnchain_blocks_db,
                &mut sort_tx,
                chainstate_db_conn,
            )
            .expect("FATAL: could not find a valid parent Stacks block");

        let stacks_am = inner_static_get_stacks_tip_affirmation_map(
            &self.burnchain_blocks_db,
            last_2_05_rc,
            &sort_tx.find_sortition_tip_affirmation_map(&highest_valid_sortition_id)?,
            &sort_tx,
            &canonical_ch,
            &canonical_bhh,
        )
        .expect("FATAL: failed to query stacks DB");

        debug!(
            "Canonical Stacks tip after burnchain processing is {}/{} height {} am `{}`",
            &canonical_ch, &canonical_bhh, canonical_height, &stacks_am
        );
        debug!(
            "Canonical sortition tip after burnchain processing is {},{}",
            &highest_valid_sortition_id, canonical_snapshot.block_height
        );

        let highest_valid_sn =
            SortitionDB::get_block_snapshot(&sort_tx, &highest_valid_sortition_id)?
                .expect("FATAL: no snapshot for highest valid sortition ID");

        let block_known = StacksChainState::is_stacks_block_processed(
            chainstate_db_conn,
            &highest_valid_sn.consensus_hash,
            &highest_valid_sn.winning_stacks_block_hash,
        )
        .expect("FATAL: failed to query chainstate DB");

        SortitionDB::revalidate_snapshot_with_block(
            &sort_tx,
            &highest_valid_sortition_id,
            &canonical_ch,
            &canonical_bhh,
            canonical_height,
            Some(block_known),
        )
        .unwrap_or_else(|_| {
            panic!(
                "FATAL: failed to revalidate highest valid sortition {}",
                &highest_valid_sortition_id
            )
        });

        sort_tx.commit()?;

        debug!("Done handling new burnchain blocks");

        Ok(None)
    }

    /// returns None if this burnchain block is _not_ the start of a reward cycle
    ///         otherwise, returns the required reward cycle info for this burnchain block
    ///                     in our current sortition view:
    ///           * PoX anchor block
    ///           * Was PoX anchor block known?
    pub fn get_reward_cycle_info(
        &mut self,
        burn_header: &BurnchainBlockHeader,
    ) -> Result<Option<RewardCycleInfo>, Error> {
        let sortition_tip_id = self
            .canonical_sortition_tip
            .as_ref()
            .expect("FATAL: Processing anchor block, but no known sortition tip");

        get_reward_cycle_info(
            burn_header.block_height,
            &burn_header.parent_block_hash,
            sortition_tip_id,
            &self.burnchain,
            &self.burnchain_blocks_db,
            &mut self.chain_state_db,
            &mut self.sortition_db,
            &self.reward_set_provider,
            self.config.always_use_affirmation_maps,
        )
    }

    /// Process any Atlas attachment events and forward them to the Atlas subsystem
    pub fn process_atlas_attachment_events(
        atlas_db: Option<&mut AtlasDB>,
        atlas_config: &AtlasConfig,
        block_receipt: &StacksEpochReceipt,
        canonical_stacks_tip_height: u64,
    ) {
        let mut attachments_instances = HashSet::new();
        for receipt in block_receipt.tx_receipts.iter() {
            if let TransactionOrigin::Stacks(ref transaction) = receipt.transaction {
                if let TransactionPayload::ContractCall(ref contract_call) = transaction.payload {
                    let contract_id = contract_call.to_clarity_contract_id();
                    increment_contract_calls_processed();
                    if atlas_config.contracts.contains(&contract_id) {
                        for event in receipt.events.iter() {
                            if let StacksTransactionEvent::SmartContractEvent(ref event_data) =
                                event
                            {
                                let res = AttachmentInstance::try_new_from_value(
                                    &event_data.value,
                                    &contract_id,
                                    block_receipt.header.index_block_hash(),
                                    block_receipt.header.stacks_block_height,
                                    receipt.transaction.txid(),
                                    Some(canonical_stacks_tip_height),
                                );
                                if let Some(attachment_instance) = res {
                                    attachments_instances.insert(attachment_instance);
                                }
                            }
                        }
                    }
                }
            }
        }
        if !attachments_instances.is_empty() {
            info!(
                "Atlas: New attachment instances emitted by block";
                "attachments_count" => attachments_instances.len(),
                "index_block_hash" => %block_receipt.header.index_block_hash(),
                "stacks_height" => block_receipt.header.stacks_block_height,
                "burn_height" => block_receipt.header.burn_header_height,
                "burn_block_hash" => %block_receipt.header.burn_header_hash,
                "consensus_hash" => %block_receipt.header.consensus_hash,
            );
            if let Some(atlas_db) = atlas_db {
                for new_attachment in attachments_instances.into_iter() {
                    if let Err(e) = atlas_db.queue_attachment_instance(&new_attachment) {
                        warn!(
                            "Atlas: Error writing attachment instance to DB";
                            "err" => ?e,
                            "index_block_hash" => %new_attachment.index_block_hash,
                            "contract_id" => %new_attachment.contract_id,
                            "attachment_index" => %new_attachment.attachment_index,
                        );
                    }
                }
            } else {
                warn!("Atlas: attempted to write attachments, but stacks-node not configured with Atlas DB");
            }
        }
    }

    /// Replay any existing Stacks blocks we have that arose on a different PoX fork.
    /// This is best-effort -- if a block isn't found or can't be loaded, it's skipped.
    fn replay_stacks_blocks(
        &mut self,
        tip: &BlockSnapshot,
        blocks: Vec<BlockHeaderHash>,
    ) -> Result<(), Error> {
        for bhh in blocks.into_iter() {
            let staging_block_chs = StacksChainState::get_staging_block_consensus_hashes(
                self.chain_state_db.db(),
                &bhh,
            )?;
            let mut processed = false;

            debug!("Consider replaying {} from {:?}", &bhh, &staging_block_chs);

            for alt_ch in staging_block_chs.into_iter() {
                let alt_id = StacksBlockHeader::make_index_block_hash(&alt_ch, &bhh);
                if !StacksChainState::has_block_indexed(&self.chain_state_db.blocks_path, &alt_id)
                    .unwrap_or(false)
                {
                    continue;
                }

                // does this consensus hash exist somewhere? Doesn't have to be on the canonical
                // PoX fork.
                let ch_height_opt = self.sortition_db.get_consensus_hash_height(&alt_ch)?;
                let ch_height = if let Some(ch_height) = ch_height_opt {
                    ch_height
                } else {
                    continue;
                };

                // Find the corresponding snapshot on the canonical PoX fork.
                let ancestor_sn = if let Some(sn) = SortitionDB::get_ancestor_snapshot(
                    &self.sortition_db.index_conn(),
                    ch_height,
                    &tip.sortition_id,
                )? {
                    sn
                } else {
                    continue;
                };

                // the new consensus hash
                let ch = ancestor_sn.consensus_hash;

                if let Ok(Some(block)) =
                    StacksChainState::load_block(&self.chain_state_db.blocks_path, &alt_ch, &bhh)
                {
                    let ic = self.sortition_db.index_conn();
                    if let Some(parent_snapshot) = ic
                        .find_parent_snapshot_for_stacks_block(&ch, &bhh)
                        .unwrap_or(None)
                    {
                        // replay in this consensus hash history
                        debug!("Replay Stacks block from {} to {}/{}", &alt_ch, &ch, &bhh);
                        let ic = self.sortition_db.index_conn();
                        let _ = self.chain_state_db.preprocess_anchored_block(
                            &ic,
                            &ch,
                            &block,
                            &parent_snapshot.consensus_hash,
                            get_epoch_time_secs(),
                        );
                        processed = true;
                        break;
                    }
                }
            }

            if !processed {
                test_debug!("Did NOT replay {}", &bhh);
            }
        }
        Ok(())
    }

    /// Try and replay a newly-discovered (or re-affirmed) sortition's associated Stacks block, if
    /// we have it.
    #[cfg_attr(test, mutants::skip)]
    fn try_replay_stacks_block(
        &mut self,
        canonical_snapshot: &BlockSnapshot,
        next_snapshot: &BlockSnapshot,
    ) -> Result<(), Error> {
        let staging_block_chs = StacksChainState::get_staging_block_consensus_hashes(
            self.chain_state_db.db(),
            &next_snapshot.winning_stacks_block_hash,
        )?;

        let mut found = false;
        for ch in staging_block_chs.iter() {
            if *ch == next_snapshot.consensus_hash {
                found = true;
                break;
            }
        }

        if !found && !staging_block_chs.is_empty() {
            // we have seen this block before, but in a different consensus fork.
            // queue it for re-processing -- it might still be valid if it's in a reward
            // cycle that exists on the new PoX fork.
            debug!(
                "Sortition re-processes Stacks block {}, which is present on a different PoX fork",
                &next_snapshot.winning_stacks_block_hash
            );

            self.replay_stacks_blocks(
                canonical_snapshot,
                vec![next_snapshot.winning_stacks_block_hash.clone()],
            )?;
        }
        Ok(())
    }

    /// Verify that a PoX anchor block candidate is affirmed by the network.
    /// Returns Ok(Some(pox_anchor)) if so.
    /// Returns Ok(None) if not.
    /// Returns Err(Error::NotPoXAnchorBlock) if this block got F*w confirmations but is not the
    /// heaviest-confirmed burnchain block.
    fn check_pox_anchor_affirmation(
        &self,
        pox_anchor: &BlockHeaderHash,
        winner_snapshot: &BlockSnapshot,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        if BurnchainDB::is_anchor_block(
            self.burnchain_blocks_db.conn(),
            &winner_snapshot.burn_header_hash,
            &winner_snapshot.winning_block_txid,
        )? {
            // affirmed?
            let canonical_sortition_tip = self.canonical_sortition_tip.clone().expect(
                "FAIL: processing a new Stacks block, but don't have a canonical sortition tip",
            );
            let heaviest_am = self.get_heaviest_affirmation_map(&canonical_sortition_tip)?;

            let commit = BurnchainDB::get_block_commit(
                self.burnchain_blocks_db.conn(),
                &winner_snapshot.burn_header_hash,
                &winner_snapshot.winning_block_txid,
            )?
            .expect("BUG: no commit metadata in DB for existing commit");

            let commit_md = BurnchainDB::get_commit_metadata(
                self.burnchain_blocks_db.conn(),
                &winner_snapshot.burn_header_hash,
                &winner_snapshot.winning_block_txid,
            )?
            .expect("BUG: no commit metadata in DB for existing commit");

            let reward_cycle = commit_md
                .anchor_block
                .expect("BUG: anchor block commit has no anchor block reward cycle");

            if heaviest_am
                .at(reward_cycle)
                .unwrap_or(&AffirmationMapEntry::PoxAnchorBlockPresent)
                == &AffirmationMapEntry::PoxAnchorBlockPresent
            {
                // yup, we're expecting this
                debug!("Discovered an old anchor block: {}", pox_anchor;
                    "height" => commit.block_height,
                    "burn_block_hash" => %commit.burn_header_hash,
                    "stacks_block_hash" => %commit.block_header_hash,
                    "reward_cycle" => reward_cycle,
                    "heaviest_affirmation_map" => %heaviest_am
                );
                info!("Discovered an old anchor block: {}", pox_anchor;
                    "height" => commit.block_height,
                    "burn_block_hash" => %commit.burn_header_hash,
                    "stacks_block_hash" => %commit.block_header_hash,
                    "reward_cycle" => reward_cycle
                );
                return Ok(Some(pox_anchor.clone()));
            } else {
                // nope -- can ignore
                debug!("Discovered unaffirmed old anchor block: {}", pox_anchor;
                    "height" => commit.block_height,
                    "burn_block_hash" => %commit.burn_header_hash,
                    "stacks_block_hash" => %commit.block_header_hash,
                    "reward_cycle" => reward_cycle,
                    "heaviest_affirmation_map" => %heaviest_am
                );
                return Ok(None);
            }
        } else {
            debug!("Stacks block {} received F*w confirmations but is not the heaviest-confirmed burnchain block, so treating as non-anchor block", pox_anchor);
            return Err(Error::NotPoXAnchorBlock);
        }
    }

    /// Figure out what to do with a newly-discovered anchor block, based on the canonical
    /// affirmation map.  If the anchor block is affirmed, then returns Some(anchor-block-hash).
    /// Otherwise, returns None.
    ///
    /// Returning Some(...) means "we need to go and process the reward cycle info from this anchor
    /// block."
    ///
    /// Returning None means "we can keep processing Stacks blocks"
    #[cfg_attr(test, mutants::skip)]
    fn consider_pox_anchor(
        &self,
        pox_anchor: &BlockHeaderHash,
        pox_anchor_snapshot: &BlockSnapshot,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        // use affirmation maps even if they're not supported yet.
        // if the chain is healthy, this won't cause a chain split.
        match self.check_pox_anchor_affirmation(pox_anchor, pox_anchor_snapshot) {
            Ok(Some(pox_anchor)) => {
                // yup, affirmed.  Report it for subsequent reward cycle calculation.
                let block_id = StacksBlockId::new(&pox_anchor_snapshot.consensus_hash, &pox_anchor);
                if !StacksChainState::has_stacks_block(self.chain_state_db.db(), &block_id)? {
                    debug!(
                        "Have NOT processed anchor block {}/{}",
                        &pox_anchor_snapshot.consensus_hash, pox_anchor
                    );
                } else {
                    // already have it
                    debug!(
                        "Already have processed anchor block {}/{}",
                        &pox_anchor_snapshot.consensus_hash, pox_anchor
                    );
                }
                return Ok(Some(pox_anchor));
            }
            Ok(None) => {
                // unaffirmed old anchor block, so no rewind is needed.
                debug!(
                    "Unaffirmed old anchor block {}/{}",
                    &pox_anchor_snapshot.consensus_hash, pox_anchor
                );
                return Ok(None);
            }
            Err(Error::NotPoXAnchorBlock) => {
                // what epoch is this block in?
                let cur_epoch = SortitionDB::get_stacks_epoch(
                    self.sortition_db.conn(),
                    pox_anchor_snapshot.block_height,
                )?
                .unwrap_or_else(|| {
                    panic!(
                        "BUG: no epoch defined at height {}",
                        pox_anchor_snapshot.block_height
                    )
                });
                if cur_epoch.epoch_id < StacksEpochId::Epoch21 {
                    panic!("FATAL: found Stacks block that 2.0/2.05 rules would treat as an anchor block, but that 2.1+ would not");
                }
                return Ok(None);
            }
            Err(e) => {
                error!("Failed to check PoX affirmation: {:?}", &e);
                return Err(e);
            }
        }
    }

    ///
    /// Process any ready staging blocks until there are either:
    ///   * there are no more to process
    ///   * a PoX anchor block is processed which invalidates the current PoX fork
    ///
    /// Returns Some(BlockHeaderHash) if such an anchor block is discovered,
    ///   otherwise returns None
    ///
    fn process_ready_blocks(&mut self) -> Result<Option<BlockHeaderHash>, Error> {
        let canonical_sortition_tip = self.canonical_sortition_tip.clone().expect(
            "FAIL: processing a new Stacks block, but don't have a canonical sortition tip",
        );

        let burnchain_db_conn = self.burnchain_blocks_db.conn();
        let sortdb_handle = self
            .sortition_db
            .tx_handle_begin(&canonical_sortition_tip)?;
        let mut processed_blocks = self.chain_state_db.process_blocks(
            burnchain_db_conn,
            sortdb_handle,
            1,
            self.dispatcher,
        )?;

        while let Some(block_result) = processed_blocks.pop() {
            if block_result.0.is_none() && block_result.1.is_none() {
                // this block was invalid
                debug!("Bump blocks processed (invalid)");
                self.notifier.notify_stacks_block_processed();
                increment_stx_blocks_processed_counter();
            } else if let (Some(block_receipt), _) = block_result {
                // only bump the coordinator's state if the processed block
                //   is in our sortition fork
                //  TODO: we should update the staging block logic to prevent
                //    blocks like these from getting processed at all.
                let in_sortition_set = self.sortition_db.is_stacks_block_in_sortition_set(
                    &canonical_sortition_tip,
                    &block_receipt.header.anchored_header.block_hash(),
                )?;

                if in_sortition_set {
                    // if .signers was updated, notify the p2p thread
                    if block_receipt.signers_updated {
                        self.refresh_stacker_db
                            .store(true, std::sync::atomic::Ordering::SeqCst);
                    }

                    let new_canonical_block_snapshot = SortitionDB::get_block_snapshot(
                        self.sortition_db.conn(),
                        &canonical_sortition_tip,
                    )?
                    .unwrap_or_else(|| {
                        panic!(
                            "FAIL: could not find data for the canonical sortition {}",
                            &canonical_sortition_tip
                        )
                    });
                    let new_canonical_stacks_block =
                        new_canonical_block_snapshot.get_canonical_stacks_block_id();

                    debug!("Bump blocks processed ({})", &new_canonical_stacks_block);

                    self.notifier.notify_stacks_block_processed();
                    increment_stx_blocks_processed_counter();

                    Self::process_atlas_attachment_events(
                        self.atlas_db.as_mut(),
                        &self.atlas_config,
                        &block_receipt,
                        new_canonical_block_snapshot.canonical_stacks_tip_height,
                    );

                    let block_hash = block_receipt.header.anchored_header.block_hash();
                    let winner_snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &self.sortition_db.index_conn(),
                        &canonical_sortition_tip,
                        &block_hash,
                    )
                    .expect("FAIL: could not find block snapshot for winning block hash")
                    .expect("FAIL: could not find block snapshot for winning block hash");

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
                        if let Err(e) =
                            estimator.notify_block(&block_receipt, &stacks_epoch.block_limit)
                        {
                            warn!("FeeEstimator failed to process block receipt";
                                  "stacks_block" => %block_hash,
                                  "stacks_height" => %block_receipt.header.stacks_block_height,
                                  "error" => %e);
                        }
                    }

                    // Was this block sufficiently confirmed by the prepare phase that it was a PoX
                    // anchor block?  And if we're in epoch 2.1, does it match the heaviest-confirmed
                    // block-commit in the burnchain DB, and is it affirmed by the majority of the
                    // network?
                    if let Some(pox_anchor) = self
                        .sortition_db
                        .is_stacks_block_pox_anchor(&block_hash, &canonical_sortition_tip)?
                    {
                        debug!(
                            "Discovered PoX anchor block {} off of canonical sortition tip {}",
                            &block_hash, &canonical_sortition_tip
                        );

                        // what epoch is this block in?
                        let cur_epoch = SortitionDB::get_stacks_epoch(
                            self.sortition_db.conn(),
                            winner_snapshot.block_height,
                        )?
                        .unwrap_or_else(|| {
                            panic!(
                                "BUG: no epoch defined at height {}",
                                winner_snapshot.block_height
                            )
                        });

                        if self.affirmation_maps_active(&cur_epoch.epoch_id) {
                            if let Some(pox_anchor) =
                                self.consider_pox_anchor(&pox_anchor, &winner_snapshot)?
                            {
                                return Ok(Some(pox_anchor));
                            }
                        } else {
                            // 2.0/2.05 behavior: only consult the sortition DB
                            // if, just after processing the block, we _know_ that this block is a pox anchor, that means
                            //   that sortitions have already begun processing that didn't know about this pox anchor.
                            //   we need to trigger an unwind
                            info!("Discovered an old anchor block: {}", &pox_anchor);
                            return Ok(Some(pox_anchor));
                        }
                    }
                }
            }
            // TODO: do something with a poison result

            let sortdb_handle = self
                .sortition_db
                .tx_handle_begin(&canonical_sortition_tip)?;
            // Right before a block is set to processed, the event dispatcher will emit a new block event
            processed_blocks = self.chain_state_db.process_blocks(
                burnchain_db_conn,
                sortdb_handle,
                1,
                self.dispatcher,
            )?;
        }

        Ok(None)
    }

    /// Process a new PoX anchor block, possibly resulting in the PoX history being unwound and
    /// replayed through a different sequence of consensus hashes.  If the new anchor block causes
    /// the node to reach a prepare-phase that elects a network-affirmed anchor block that we don't
    /// have, then return its block hash so the caller can go download and process it.
    fn process_new_pox_anchor(
        &mut self,
        block_id: BlockHeaderHash,
        already_processed_burn_blocks: &mut HashSet<BurnchainHeaderHash>,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        // get the last sortition in the prepare phase that chose this anchor block
        //   that sortition is now the current canonical sortition,
        //   and now that we have process the anchor block for the corresponding reward phase,
        //   update the canonical pox bitvector.
        let sortition_id = self.canonical_sortition_tip.as_ref().expect(
            "FAIL: processing a new anchor block, but don't have a canonical sortition tip",
        );

        let mut prep_end = self
            .sortition_db
            .get_prepare_end_for(sortition_id, &block_id)?
            .unwrap_or_else(|| panic!("FAIL: expected to get a sortition for a chosen anchor block {}, but not found.",
                &block_id));

        // was this block a pox anchor for an even earlier reward cycle?
        while let Some(older_prep_end) = self
            .sortition_db
            .get_prepare_end_for(&prep_end.sortition_id, &block_id)?
        {
            prep_end = older_prep_end;
        }

        info!(
            "Reprocessing with anchor block information, starting at block height: {}",
            prep_end.block_height;
            "consensus_hash" => %prep_end.consensus_hash,
            "burn_block_hash" => %prep_end.burn_header_hash,
            "stacks_block_height" => prep_end.stacks_block_height
        );
        let mut pox_id = self.sortition_db.get_pox_id(sortition_id)?;
        pox_id.extend_with_present_block();

        // invalidate all the sortitions > canonical_sortition_tip, in the same burnchain fork
        self.sortition_db
            .invalidate_descendants_of(&prep_end.burn_header_hash)?;

        // roll back to the state as of prep_end
        self.canonical_sortition_tip = Some(prep_end.sortition_id);

        // Start processing from the beginning of the new PoX reward set
        self.handle_new_epoch2_burnchain_block(already_processed_burn_blocks)
    }
}

/// Determine whether or not the current chainstate databases are up-to-date with the current
/// epoch.
pub fn check_chainstate_db_versions(
    epochs: &[StacksEpoch],
    sortdb_path: &str,
    chainstate_path: &str,
) -> Result<bool, DBError> {
    let mut cur_epoch_opt = None;
    if fs::metadata(&sortdb_path).is_ok() {
        // check sortition DB and load up the current epoch
        let max_height = SortitionDB::get_highest_block_height_from_path(sortdb_path)
            .expect("FATAL: could not query sortition DB for maximum block height");
        let cur_epoch_idx = StacksEpoch::find_epoch(epochs, max_height)
            .unwrap_or_else(|| panic!("FATAL: no epoch defined for burn height {max_height}"));
        let cur_epoch = epochs[cur_epoch_idx].epoch_id;

        // save for later
        cur_epoch_opt = Some(cur_epoch.clone());
        let db_version = SortitionDB::get_db_version_from_path(sortdb_path)?
            .expect("FATAL: could not load sortition DB version");

        if !SortitionDB::is_db_version_supported_in_epoch(cur_epoch, &db_version) {
            error!("Sortition DB at {sortdb_path} does not support epoch {cur_epoch}");
            return Ok(false);
        }
    } else {
        warn!("Sortition DB {} does not exist; assuming it will be instantiated with the correct version", sortdb_path);
    }

    if fs::metadata(chainstate_path).is_ok() {
        let cur_epoch = cur_epoch_opt.expect(
            "FATAL: chainstate corruption: sortition DB does not exist, but chainstate does.",
        );
        let db_config = StacksChainState::get_db_config_from_path(chainstate_path)?;
        if !db_config.supports_epoch(cur_epoch) {
            error!("Chainstate DB at {chainstate_path} does not support epoch {cur_epoch}");
            return Ok(false);
        }
    } else {
        warn!("Chainstate DB {chainstate_path} does not exist; assuming it will be instantiated with the correct version");
    }

    Ok(true)
}

/// Sortition DB migrator.
/// This is an opaque struct that is meant to assist migrating an epoch 2.1-2.4 chainstate to epoch
/// 2.5.  It will not work for 2.5 to 3.0+
pub struct SortitionDBMigrator {
    chainstate: Option<StacksChainState>,
    burnchain: Burnchain,
    burnchain_db: BurnchainDB,
}

impl SortitionDBMigrator {
    /// Instantiate the migrator.
    /// The chainstate must already exist
    pub fn new(
        burnchain: Burnchain,
        chainstate_path: &str,
        marf_opts: Option<MARFOpenOpts>,
    ) -> Result<Self, Error> {
        let db_config = StacksChainState::get_db_config_from_path(chainstate_path)?;
        let (chainstate, _) = StacksChainState::open(
            db_config.mainnet,
            db_config.chain_id,
            chainstate_path,
            marf_opts,
        )?;
        let burnchain_db = BurnchainDB::open(&burnchain.get_burnchaindb_path(), false)?;

        Ok(Self {
            chainstate: Some(chainstate),
            burnchain,
            burnchain_db,
        })
    }

    /// Get the burnchain reference
    pub fn get_burnchain(&self) -> &Burnchain {
        &self.burnchain
    }

    /// Regenerate a reward cycle.  Do this by re-calculating the RewardSetInfo for the given
    /// reward cycle.  This should store the preprocessed reward cycle info to the sortition DB.
    pub fn regenerate_reward_cycle_info(
        &mut self,
        sort_db: &mut SortitionDB,
        reward_cycle: u64,
    ) -> Result<RewardCycleInfo, DBError> {
        let rc_start = sort_db
            .pox_constants
            .reward_cycle_to_block_height(sort_db.first_block_height, reward_cycle)
            .saturating_sub(1);

        let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())?;

        let ancestor_sn = {
            let sort_ih = sort_db.index_handle(&sort_tip.sortition_id);
            let sn = sort_ih
                .get_block_snapshot_by_height(rc_start)?
                .ok_or(DBError::NotFoundError)?;
            sn
        };

        let mut chainstate = self
            .chainstate
            .take()
            .expect("FATAL: failed to replace chainstate");

        // NOTE: this stores the preprocessed reward cycle info to the sortition DB as a
        // side-effect!
        let rc_info_opt_res = get_reward_cycle_info(
            ancestor_sn.block_height + 1,
            &ancestor_sn.burn_header_hash,
            &ancestor_sn.sortition_id,
            &self.burnchain,
            &self.burnchain_db,
            &mut chainstate,
            sort_db,
            &OnChainRewardSetProvider::new(),
            true,
        )
        .map_err(|e| DBError::Other(format!("get_reward_cycle_info: {:?}", &e)));

        self.chainstate = Some(chainstate);

        let rc_info = rc_info_opt_res?
            .expect("FATAL: No reward cycle info calculated at a reward-cycle start");
        Ok(rc_info)
    }
}

/// Migrate all databases to their latest schemas.
/// Verifies that this is possible as well
#[cfg_attr(test, mutants::skip)]
pub fn migrate_chainstate_dbs(
    epochs: &[StacksEpoch],
    burnchain: &Burnchain,
    sortdb_path: &str,
    chainstate_path: &str,
    chainstate_marf_opts: Option<MARFOpenOpts>,
) -> Result<(), Error> {
    if !check_chainstate_db_versions(epochs, sortdb_path, chainstate_path)? {
        warn!("Unable to migrate chainstate DBs to the latest schemas in the current epoch");
        return Err(DBError::TooOldForEpoch.into());
    }

    if fs::metadata(&sortdb_path).is_ok() {
        info!("Migrating sortition DB to the latest schema version");
        let migrator = SortitionDBMigrator::new(
            burnchain.clone(),
            chainstate_path,
            chainstate_marf_opts.clone(),
        )?;
        SortitionDB::migrate_if_exists(sortdb_path, epochs, migrator)?;
    }
    if fs::metadata(&chainstate_path).is_ok() {
        info!("Migrating chainstate DB to the latest schema version");
        let db_config = StacksChainState::get_db_config_from_path(chainstate_path)?;

        // this does the migration internally
        let _ = StacksChainState::open(
            db_config.mainnet,
            db_config.chain_id,
            chainstate_path,
            chainstate_marf_opts,
        )?;
    }
    Ok(())
}
