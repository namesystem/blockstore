// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2024 Stacks Open Internet Foundation
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

use clarity::vm::costs::ExecutionCost;
use rusqlite::params;
/// Shadow blocks
///
/// In the event of an emergency chain halt, a SIP will be written to declare that a chain halt has
/// happened, and what transactions and blocks (if any) need to be mined at which burnchain block
/// heights to recover the chain.
///
/// If this remedy is necessary, these blocks will be mined into one or more _shadow_ blocks and
/// _shadow_ tenures.
///
/// Shadow blocks are blocks that are inserted directly into the staging blocks DB as part of a
/// schema update. They are neither mined nor relayed.  Instead, they are synthesized as part of an
/// emergency node upgrade in order to ensure that the conditions which lead to the chain stall
/// never occur.
///
/// For example, if a prepare phase is mined without a single block-commit hitting the Bitcoin
/// chain, a pair of shadow block tenures will be synthesized to create a PoX anchor block and
/// restore the chain's liveness.  As another example, if insufficiently many STX are locked in PoX
/// to get a healthy set of signers, a shadow block can be synthesized with extra `stack-stx`
/// transactions submitted from healthy stackers in order to create a suitable PoX reward set.
///
/// This module contains shadow block-specific logic for the Nakamoto block header, Nakamoto block,
/// Nakamoto chainstate, and Nakamoto miner structures.
use rusqlite::Connection;
use stacks_common::codec::StacksMessageCodec;
use stacks_common::types::chainstate::{
    BlockHeaderHash, ConsensusHash, StacksAddress, StacksBlockId, StacksPrivateKey, StacksPublicKey,
};
use stacks_common::util::hash::Hash160;
use stacks_common::util::vrf::VRFProof;

use crate::burnchains::PoxConstants;
use crate::chainstate::nakamoto::miner::{MinerTenureInfo, NakamotoBlockBuilder};
use crate::chainstate::nakamoto::{
    BlockSnapshot, ChainstateError, LeaderBlockCommitOp, NakamotoBlock, NakamotoBlockHeader,
    NakamotoBlockObtainMethod, NakamotoChainState, NakamotoStagingBlocksConn,
    NakamotoStagingBlocksConnRef, NakamotoStagingBlocksTx, SetupBlockResult, SortitionDB,
    SortitionHandleConn, StacksDBIndexed,
};
use crate::chainstate::stacks::boot::RewardSet;
use crate::chainstate::stacks::db::blocks::DummyEventDispatcher;
use crate::chainstate::stacks::db::{
    ChainstateTx, ClarityTx, StacksAccount, StacksChainState, StacksHeaderInfo,
};
use crate::chainstate::stacks::miner::{
    BlockBuilder, BlockLimitFunction, TransactionError, TransactionProblematic, TransactionResult,
    TransactionSkipped,
};
use crate::chainstate::stacks::{
    CoinbasePayload, Error, StacksTransaction, StacksTransactionSigner, TenureChangeCause,
    TenureChangePayload, TransactionAnchorMode, TransactionAuth, TransactionPayload,
    TransactionVersion,
};
use crate::clarity::vm::types::StacksAddressExtensions;
use crate::clarity_vm::clarity::ClarityInstance;
use crate::clarity_vm::database::SortitionDBRef;
use crate::net::Error as NetError;
use crate::util_lib::db::{query_row, u64_to_sql, Error as DBError};

impl NakamotoBlockHeader {
    /// Is this a shadow block?
    ///
    /// This is a special kind of block that is directly inserted into the chainstate by means of a
    /// consensus rule.  It won't be downloaded or broadcasted, but every node will have it.  They
    /// get created as a result of a consensus-level SIP in order to restore the chain to working
    /// order.
    ///
    /// Shadow blocks have the high bit of their version field set.
    pub fn is_shadow_block(&self) -> bool {
        Self::is_shadow_block_version(self.version)
    }

    /// Is a block version a shadow block version?
    pub fn is_shadow_block_version(version: u8) -> bool {
        version & 0x80 != 0
    }

    /// Get the signing weight of a shadow block
    pub fn get_shadow_signer_weight(&self, reward_set: &RewardSet) -> Result<u32, Error> {
        let Some(signers) = &reward_set.signers else {
            return Err(ChainstateError::InvalidStacksBlock(
                "No signers in the reward set".to_string(),
            ));
        };
        let shadow_weight = signers
            .iter()
            .fold(0u32, |acc, signer| acc.saturating_add(signer.weight));

        Ok(shadow_weight)
    }
}

impl NakamotoBlock {
    /// Is this block a shadow block?
    /// Check the header
    pub fn is_shadow_block(&self) -> bool {
        self.header.is_shadow_block()
    }

    /// Verify that if this shadow block has a coinbase, that its VRF proof is consistent with the leader
    /// public key's VRF key. If there is no coinbase tx, then this is a no-op.
    pub(crate) fn check_shadow_coinbase_tx(&self, mainnet: bool) -> Result<(), ChainstateError> {
        if !self.is_shadow_block() {
            error!(
                "FATAL: tried to validate non-shadow block in a shadow-block-specific validator"
            );
            panic!();
        }

        // If this shadow block has a coinbase, then verify that it has a VRF proof (which will be
        // verified later) and that its recipient is the burn address.  Shadow blocks do not award
        // STX.
        if let Some(coinbase_tx) = self.get_coinbase_tx() {
            let (_, recipient_opt, vrf_proof_opt) = coinbase_tx
                .try_as_coinbase()
                .expect("FATAL: `get_coinbase_tx()` did not return a coinbase");

            if vrf_proof_opt.is_none() {
                return Err(ChainstateError::InvalidStacksBlock(
                    "Shadow Nakamoto coinbase must have a VRF proof".into(),
                ));
            }

            let Some(recipient) = recipient_opt else {
                warn!("Invalid shadow block: no recipient");
                return Err(ChainstateError::InvalidStacksBlock(
                    "Shadow block did not pay to burn address".into(),
                ));
            };

            // must be the standard burn address for this network
            let burn_addr = StacksAddress::burn_address(mainnet).to_account_principal();
            if burn_addr != *recipient {
                warn!("Invalid shadow block: recipient does not burn");
                return Err(ChainstateError::InvalidStacksBlock(
                    "Shadow block did not pay to burn address".into(),
                ));
            }

            // can't check the VRF proof because the creator of the shadow block (e.g. the SIP
            // process) isn't a miner, so it could be anything.
        }
        Ok(())
    }

    /// Validate this Nakamoto shadow block header against burnchain state.
    ///
    /// Arguments
    /// -- `mainnet`: whether or not the chain is mainnet
    /// -- `tenure_burn_chain_tip` is the BlockSnapshot containing the block-commit for this block's
    /// tenure.  It is not always the tip of the burnchain.
    /// -- `expected_burn` is the total number of burnchain tokens spent, if known.
    ///
    /// Verifies the following:
    /// -- (self.header.consensus_hash) that this block falls into this block-commit's tenure
    /// -- (self.header.burn_spent) that this block's burn total matches `burn_tip`'s total burn
    /// -- if this block has a tenure change, then it's consistent with the miner's public key and
    /// self.header.consensus_hash
    ///
    /// NOTE: unlike normal blocks, we do not need to verify the VRF proof or miner signature
    pub(crate) fn validate_shadow_against_burnchain(
        &self,
        mainnet: bool,
        tenure_burn_chain_tip: &BlockSnapshot,
        expected_burn: Option<u64>,
    ) -> Result<(), ChainstateError> {
        if !self.is_shadow_block() {
            error!(
                "FATAL: tried to validate non-shadow block in a shadow-block-specific validator"
            );
            panic!();
        }
        self.common_validate_against_burnchain(tenure_burn_chain_tip, expected_burn)?;
        self.check_tenure_tx()?;
        self.check_shadow_coinbase_tx(mainnet)?;

        // not verified by this method:
        // * chain_length       (need parent block header)
        // * parent_block_id    (need parent block header)
        // * block-commit seed  (need parent block)
        // * tx_merkle_root     (already verified; validated on deserialization)
        // * state_index_root   (validated on process_block())
        // * stacker signature  (validated on accept_block())
        Ok(())
    }
}

impl NakamotoChainState {
    /// Verify that the shadow parent of a normal block is consistent with the normal block's
    /// tenure's block-commit.
    ///
    /// * the block-commit vtxindex must be 0 (i.e. burnchain coinbase)
    /// * the block-commit block ptr must be the shadow parent tenure's sortition
    ///
    /// Returns Ok(()) if the parent is _not_ a shadow block
    /// Returns Ok(()) if the parent is a shadow block, and the above criteria are met
    /// Returns Err(ChainstateError::InvalidStacksBlock(..)) if the parent is a shadow block, and
    /// some of the criteria above are false
    /// Returns Err(..) on other (DB-related) errors
    pub(crate) fn validate_shadow_parent_burnchain(
        staging_db: NakamotoStagingBlocksConnRef,
        db_handle: &SortitionHandleConn,
        block: &NakamotoBlock,
        block_commit: &LeaderBlockCommitOp,
    ) -> Result<(), ChainstateError> {
        // only applies if the parent is a nakamoto block (since all shadow blocks are nakamoto
        // blocks)
        let Some(parent_header) =
            staging_db.get_nakamoto_block_header(&block.header.parent_block_id)?
        else {
            return Ok(());
        };

        if !parent_header.is_shadow_block() {
            return Ok(());
        }

        if block_commit.parent_vtxindex != 0 {
            warn!("Invalid Nakamoto block: parent {} of {} is a shadow block but block-commit vtxindex is {}", &parent_header.block_id(), &block.block_id(), block_commit.parent_vtxindex);
            return Err(ChainstateError::InvalidStacksBlock("Invalid Nakamoto block: invalid block-commit parent vtxindex for parent shadow block".into()));
        }
        let Some(parent_sn) =
            SortitionDB::get_block_snapshot_consensus(db_handle, &parent_header.consensus_hash)?
        else {
            warn!(
                "Invalid Nakamoto block: No sortition for parent shadow block {}",
                &block.header.parent_block_id
            );
            return Err(ChainstateError::InvalidStacksBlock(
                "Invalid Nakamoto block: parent shadow block has no sortition".into(),
            ));
        };
        if u64::from(block_commit.parent_block_ptr) != parent_sn.block_height {
            warn!("Invalid Nakamoto block: parent {} of {} is a shadow block but block-commit parent ptr is {}", &parent_header.block_id(), &block.block_id(), block_commit.parent_block_ptr);
            return Err(ChainstateError::InvalidStacksBlock("Invalid Nakamoto block: invalid block-commit parent block ptr for parent shadow block".into()));
        }

        Ok(())
    }

    /// Validate a shadow Nakamoto block against burnchain state.
    /// Wraps `NakamotoBlock::validate_shadow_against_burnchain()`, and
    /// verifies that all transactions in the block are allowed in this epoch.
    pub(crate) fn validate_shadow_nakamoto_block_burnchain(
        staging_db: NakamotoStagingBlocksConnRef,
        db_handle: &SortitionHandleConn,
        expected_burn: Option<u64>,
        block: &NakamotoBlock,
        mainnet: bool,
        chain_id: u32,
    ) -> Result<(), ChainstateError> {
        if !block.is_shadow_block() {
            error!(
                "FATAL: tried to validate non-shadow block in a shadow-block-specific validator"
            );
            panic!();
        }

        // this block must already be stored
        if !staging_db.has_shadow_nakamoto_block_with_index_hash(&block.block_id())? {
            warn!("Invalid shadow Nakamoto block, must already be stored";
                "consensus_hash" => %block.header.consensus_hash,
                "stacks_block_hash" => %block.header.block_hash(),
                "block_id" => %block.header.block_id()
            );

            return Err(ChainstateError::InvalidStacksBlock(
                "Shadow block must already be stored".into(),
            ));
        }

        let tenure_burn_chain_tip = Self::validate_nakamoto_tenure_snapshot(db_handle, block)?;
        if let Err(e) =
            block.validate_shadow_against_burnchain(mainnet, &tenure_burn_chain_tip, expected_burn)
        {
            warn!(
                "Invalid shadow Nakamoto block, could not validate on burnchain";
                "consensus_hash" => %block.header.consensus_hash,
                "stacks_block_hash" => %block.header.block_hash(),
                "block_id" => %block.header.block_id(),
                "error" => ?e
            );

            return Err(e);
        }
        Self::validate_nakamoto_block_transactions_static(
            mainnet,
            chain_id,
            db_handle.conn(),
            block,
            tenure_burn_chain_tip.block_height,
        )?;
        Ok(())
    }

    /// Load the stored VRF proof for the given shadow block's tenure.
    ///
    /// Returns Ok(Some(vrf proof)) on success
    /// Returns Ok(None) if the parent tenure isn't a shadow tenure
    pub(crate) fn get_shadow_vrf_proof<SDBI: StacksDBIndexed>(
        chainstate_conn: &mut SDBI,
        tip_block_id: &StacksBlockId,
    ) -> Result<Option<VRFProof>, ChainstateError> {
        // is the tip a shadow block (and necessarily a Nakamoto block)?
        let Some(parent_version) =
            NakamotoChainState::get_nakamoto_block_version(chainstate_conn.sqlite(), tip_block_id)?
        else {
            return Ok(None);
        };

        if !NakamotoBlockHeader::is_shadow_block_version(parent_version) {
            return Ok(None);
        }

        // this is a shadow block
        let tenure_consensus_hash = NakamotoChainState::get_block_header_nakamoto_tenure_id(
            chainstate_conn.sqlite(),
            tip_block_id,
        )?
        .ok_or_else(|| {
            warn!("No tenure consensus hash for block {}", tip_block_id);
            ChainstateError::NoSuchBlockError
        })?;

        // the shadow tenure won't have a block-commit, but we just found its tenure ID anyway
        debug!(
            "Load VRF proof for shadow tenure {}",
            &tenure_consensus_hash
        );
        let vrf_proof =
            Self::get_block_vrf_proof(chainstate_conn, tip_block_id, &tenure_consensus_hash)?
                .ok_or_else(|| {
                    warn!("No VRF proof for {tenure_consensus_hash}");
                    ChainstateError::NoSuchBlockError
                })
                .inspect_err(|_e| {
                    warn!("Could not find shadow tenure VRF proof";
                      "tip_block_id" => %tip_block_id,
                      "shadow consensus_hash" => %tenure_consensus_hash);
                })?;

        return Ok(Some(vrf_proof));
    }

    /// Begin block-processing for a shadow block and return all of the pre-processed state within a
    /// `SetupBlockResult`.
    ///
    /// Called to begin processing a shadow block
    pub(crate) fn setup_shadow_block_processing<'a, 'b>(
        chainstate_tx: &'b mut ChainstateTx,
        clarity_instance: &'a mut ClarityInstance,
        sortition_dbconn: &'b dyn SortitionDBRef,
        first_block_height: u64,
        pox_constants: &PoxConstants,
        parent_consensus_hash: ConsensusHash,
        parent_header_hash: BlockHeaderHash,
        parent_burn_height: u32,
        tenure_block_snapshot: BlockSnapshot,
        new_tenure: bool,
        coinbase_height: u64,
        tenure_extend: bool,
    ) -> Result<SetupBlockResult<'a, 'b>, ChainstateError> {
        let burn_header_hash = &tenure_block_snapshot.burn_header_hash;
        let burn_header_height =
            u32::try_from(tenure_block_snapshot.block_height).map_err(|_| {
                ChainstateError::InvalidStacksBlock(
                    "Failed to downcast burn block height to u32".into(),
                )
            })?;
        let block_consensus_hash = &tenure_block_snapshot.consensus_hash;

        let parent_block_id = StacksBlockId::new(&parent_consensus_hash, &parent_header_hash);

        // tenure start header must exist and be processed
        let _ = Self::get_nakamoto_tenure_start_block_header(
            chainstate_tx.as_tx(),
            &parent_block_id,
            &parent_consensus_hash,
        )?
        .ok_or_else(|| {
            warn!("Invalid shadow Nakamoto block: no start-tenure block for parent";
                  "parent_consensus_hash" => %parent_consensus_hash,
                  "consensus_hash" => %block_consensus_hash
            );
            ChainstateError::NoSuchBlockError
        })?;

        Self::inner_setup_block(
            chainstate_tx,
            clarity_instance,
            sortition_dbconn,
            first_block_height,
            pox_constants,
            parent_consensus_hash,
            parent_header_hash,
            parent_burn_height,
            burn_header_hash.clone(),
            burn_header_height,
            new_tenure,
            coinbase_height,
            tenure_extend,
        )
    }
}

impl NakamotoBlockBuilder {
    /// This function should be called before `tenure_begin`.
    /// It creates a MinerTenureInfo struct which owns connections to the chainstate and sortition
    /// DBs, so that block-processing is guaranteed to terminate before the lives of these handles
    /// expire.
    ///
    /// It's used to create shadow blocks.
    pub(crate) fn shadow_load_tenure_info<'a>(
        &self,
        chainstate: &'a mut StacksChainState,
        burn_dbconn: &'a SortitionHandleConn,
        cause: Option<TenureChangeCause>,
    ) -> Result<MinerTenureInfo<'a>, Error> {
        self.inner_load_tenure_info(chainstate, burn_dbconn, cause, true)
    }

    /// Begin/resume mining a shadow tenure's transactions.
    /// Returns an open ClarityTx for mining the block.
    /// NOTE: even though we don't yet know the block hash, the Clarity VM ensures that a
    /// transaction can't query information about the _current_ block (i.e. information that is not
    /// yet known).
    pub fn shadow_tenure_begin<'a, 'b>(
        &mut self,
        burn_dbconn: &'a SortitionHandleConn,
        info: &'b mut MinerTenureInfo<'a>,
        tenure_id_consensus_hash: &ConsensusHash,
    ) -> Result<ClarityTx<'b, 'b>, Error> {
        let tenure_snapshot = SortitionDB::get_block_snapshot_consensus(
            burn_dbconn.conn(),
            tenure_id_consensus_hash,
        )?
        .ok_or_else(|| Error::NoSuchBlockError)?;

        let SetupBlockResult {
            clarity_tx,
            matured_miner_rewards_opt,
            ..
        } = NakamotoChainState::setup_shadow_block_processing(
            &mut info.chainstate_tx,
            info.clarity_instance,
            burn_dbconn,
            burn_dbconn.context.first_block_height,
            &burn_dbconn.context.pox_constants,
            info.parent_consensus_hash,
            info.parent_header_hash,
            info.parent_burn_block_height,
            tenure_snapshot,
            info.cause == Some(TenureChangeCause::BlockFound),
            info.coinbase_height,
            info.cause == Some(TenureChangeCause::Extended),
        )?;
        self.matured_miner_rewards_opt = matured_miner_rewards_opt;
        Ok(clarity_tx)
    }

    /// Get an address's account
    pub fn get_account(
        chainstate: &mut StacksChainState,
        sortdb: &SortitionDB,
        addr: &StacksAddress,
        tip: &StacksHeaderInfo,
    ) -> Result<StacksAccount, Error> {
        let snapshot =
            SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &tip.consensus_hash)?
                .ok_or_else(|| Error::NoSuchBlockError)?;

        let account = chainstate
            .with_read_only_clarity_tx(
                &sortdb.index_handle(&snapshot.sortition_id),
                &tip.index_block_hash(),
                |clarity_conn| {
                    StacksChainState::get_account(clarity_conn, &addr.to_account_principal())
                },
            )
            .ok_or_else(|| Error::NoSuchBlockError)?;

        Ok(account)
    }

    /// Make a shadow block from transactions
    pub fn make_shadow_block_from_txs(
        mut builder: NakamotoBlockBuilder,
        chainstate_handle: &StacksChainState,
        burn_dbconn: &SortitionHandleConn,
        tenure_id_consensus_hash: &ConsensusHash,
        txs: Vec<StacksTransaction>,
    ) -> Result<(NakamotoBlock, u64, ExecutionCost), Error> {
        use clarity::vm::ast::ASTRules;

        debug!(
            "Build shadow Nakamoto block from {} transactions",
            txs.len()
        );
        let (mut chainstate, _) = chainstate_handle.reopen()?;

        let mut tenure_cause = None;
        for tx in txs.iter() {
            let TransactionPayload::TenureChange(payload) = &tx.payload else {
                continue;
            };
            tenure_cause = Some(payload.cause);
            break;
        }

        let mut miner_tenure_info =
            builder.shadow_load_tenure_info(&mut chainstate, burn_dbconn, tenure_cause)?;
        let mut tenure_tx = builder.shadow_tenure_begin(
            burn_dbconn,
            &mut miner_tenure_info,
            tenure_id_consensus_hash,
        )?;
        for tx in txs.into_iter() {
            let tx_len = tx.tx_len();
            match builder.try_mine_tx_with_len(
                &mut tenure_tx,
                &tx,
                tx_len,
                &BlockLimitFunction::NO_LIMIT_HIT,
                ASTRules::PrecheckSize,
            ) {
                TransactionResult::Success(..) => {
                    debug!("Included {}", &tx.txid());
                }
                TransactionResult::Skipped(TransactionSkipped { error, .. })
                | TransactionResult::ProcessingError(TransactionError { error, .. }) => {
                    match error {
                        Error::BlockTooBigError => {
                            // done mining -- our execution budget is exceeded.
                            // Make the block from the transactions we did manage to get
                            debug!("Block budget exceeded on tx {}", &tx.txid());
                        }
                        Error::InvalidStacksTransaction(_emsg, true) => {
                            // if we have an invalid transaction that was quietly ignored, don't warn here either
                            test_debug!(
                                "Failed to apply tx {}: InvalidStacksTransaction '{:?}'",
                                &tx.txid(),
                                &_emsg
                            );
                            continue;
                        }
                        Error::ProblematicTransaction(txid) => {
                            test_debug!("Encountered problematic transaction. Aborting");
                            return Err(Error::ProblematicTransaction(txid));
                        }
                        e => {
                            warn!("Failed to apply tx {}: {:?}", &tx.txid(), &e);
                            continue;
                        }
                    }
                }
                TransactionResult::Problematic(TransactionProblematic { tx, .. }) => {
                    // drop from the mempool
                    debug!("Encountered problematic transaction {}", &tx.txid());
                    return Err(Error::ProblematicTransaction(tx.txid()));
                }
            }
        }
        let block = builder.mine_nakamoto_block(&mut tenure_tx);
        let size = builder.bytes_so_far;
        let cost = builder.tenure_finish(tenure_tx)?;
        Ok((block, size, cost))
    }

    /// Produce a single-block shadow tenure.
    /// Used by tooling to synthesize shadow blocks in case of an emergency.
    /// The details and circumstances will be recorded in an accompanying SIP.
    ///
    /// `naka_tip_id` is the Stacks chain tip on top of which the shadow block will be built.
    /// `tenure_id_consensus_hash` is the sortition in which the shadow block will be built.
    /// `txs` are transactions to include, beyond a coinbase and tenure-change
    pub fn make_shadow_tenure(
        chainstate: &mut StacksChainState,
        sortdb: &SortitionDB,
        naka_tip_id: StacksBlockId,
        tenure_id_consensus_hash: ConsensusHash,
        mut txs: Vec<StacksTransaction>,
    ) -> Result<NakamotoBlock, Error> {
        let mainnet = chainstate.config().mainnet;
        let chain_id = chainstate.config().chain_id;

        let recipient = StacksAddress::burn_address(mainnet).to_account_principal();
        let vrf_proof_bytes = vec![
            0x92, 0x75, 0xdf, 0x67, 0xa6, 0x8c, 0x87, 0x45, 0xc0, 0xff, 0x97, 0xb4, 0x82, 0x01,
            0xee, 0x6d, 0xb4, 0x47, 0xf7, 0xc9, 0x3b, 0x23, 0xae, 0x24, 0xcd, 0xc2, 0x40, 0x0f,
            0x52, 0xfd, 0xb0, 0x8a, 0x1a, 0x6a, 0xc7, 0xec, 0x71, 0xbf, 0x9c, 0x9c, 0x76, 0xe9,
            0x6e, 0xe4, 0x67, 0x5e, 0xbf, 0xf6, 0x06, 0x25, 0xaf, 0x28, 0x71, 0x85, 0x01, 0x04,
            0x7b, 0xfd, 0x87, 0xb8, 0x10, 0xc2, 0xd2, 0x13, 0x9b, 0x73, 0xc2, 0x3b, 0xd6, 0x9d,
            0xe6, 0x63, 0x60, 0x95, 0x3a, 0x64, 0x2c, 0x2a, 0x33, 0x0a,
        ];

        // safety -- we know it's a good proof
        let vrf_proof = VRFProof::from_bytes(vrf_proof_bytes.as_slice()).unwrap();

        let naka_tip_header = NakamotoChainState::get_block_header(chainstate.db(), &naka_tip_id)?
            .ok_or_else(|| {
                warn!("No such Nakamoto tip: {:?}", &naka_tip_id);
                Error::NoSuchBlockError
            })?;

        let naka_tip_tenure_start_header = NakamotoChainState::get_tenure_start_block_header(
            &mut chainstate.index_conn(),
            &naka_tip_id,
            &naka_tip_header.consensus_hash,
        )?
        .ok_or_else(|| {
            Error::InvalidStacksBlock(format!(
                "No tenure-start block header for tenure {}",
                &naka_tip_header.consensus_hash
            ))
        })?;

        if naka_tip_header.anchored_header.height()
            < naka_tip_tenure_start_header.anchored_header.height()
        {
            return Err(Error::InvalidStacksBlock(
                "Nakamoto tip is lower than its tenure-start block".into(),
            ));
        }

        let coinbase_payload = CoinbasePayload(naka_tip_tenure_start_header.index_block_hash().0);

        // the miner key is irrelevant
        let miner_key = StacksPrivateKey::random();
        let miner_addr = StacksAddress::p2pkh(mainnet, &StacksPublicKey::from_private(&miner_key));
        let miner_tx_auth = TransactionAuth::from_p2pkh(&miner_key).ok_or_else(|| {
            Error::InvalidStacksBlock(
                "Unable to construct transaction auth from transient private key".into(),
            )
        })?;

        let tx_version = if mainnet {
            TransactionVersion::Mainnet
        } else {
            TransactionVersion::Testnet
        };
        let miner_account = Self::get_account(chainstate, sortdb, &miner_addr, &naka_tip_header)?;

        // tenure change payload (BlockFound)
        let tenure_change_payload = TenureChangePayload {
            tenure_consensus_hash: tenure_id_consensus_hash.clone(),
            prev_tenure_consensus_hash: naka_tip_header.consensus_hash,
            burn_view_consensus_hash: tenure_id_consensus_hash.clone(),
            previous_tenure_end: naka_tip_id,
            previous_tenure_blocks: (naka_tip_header.anchored_header.height() + 1
                - naka_tip_tenure_start_header.anchored_header.height())
                as u32,
            cause: TenureChangeCause::BlockFound,
            pubkey_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(&miner_key)),
        };

        // tenure-change tx
        let tenure_change_tx = {
            let mut tx_tenure_change = StacksTransaction::new(
                tx_version.clone(),
                miner_tx_auth.clone(),
                TransactionPayload::TenureChange(tenure_change_payload),
            );
            tx_tenure_change.chain_id = chain_id;
            tx_tenure_change.anchor_mode = TransactionAnchorMode::OnChainOnly;
            tx_tenure_change.auth.set_origin_nonce(miner_account.nonce);

            let mut tx_signer = StacksTransactionSigner::new(&tx_tenure_change);
            tx_signer.sign_origin(&miner_key)?;
            let tx_tenure_change_signed = tx_signer
                .get_tx()
                .ok_or_else(|| Error::InvalidStacksBlock("Failed to sign tenure change".into()))?;
            tx_tenure_change_signed
        };

        // coinbase tx
        let coinbase_tx = {
            let mut tx_coinbase = StacksTransaction::new(
                tx_version.clone(),
                miner_tx_auth,
                TransactionPayload::Coinbase(coinbase_payload, Some(recipient), Some(vrf_proof)),
            );
            tx_coinbase.chain_id = chain_id;
            tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
            tx_coinbase.auth.set_origin_nonce(miner_account.nonce + 1);

            let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
            tx_signer.sign_origin(&miner_key)?;
            let tx_coinbase_signed = tx_signer
                .get_tx()
                .ok_or_else(|| Error::InvalidStacksBlock("Failed to sign coinbase".into()))?;
            tx_coinbase_signed
        };

        // `burn_tip` corresponds to the burn view consensus hash of the tenure.
        let burn_tip =
            SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &tenure_id_consensus_hash)?
                .ok_or_else(|| Error::InvalidStacksBlock("No such tenure ID".into()))?;

        debug!(
            "Build Nakamoto shadow block in tenure {} sortition {} parent_tip {}",
            &tenure_id_consensus_hash, &burn_tip.consensus_hash, &naka_tip_id
        );

        // make a block
        let builder = NakamotoBlockBuilder::new(
            &naka_tip_header,
            &tenure_id_consensus_hash,
            burn_tip.total_burn,
            Some(&tenure_change_tx),
            Some(&coinbase_tx),
            1,
            None,
        )?;

        let mut block_txs = vec![tenure_change_tx, coinbase_tx];
        block_txs.append(&mut txs);
        let (mut shadow_block, _size, _cost) = Self::make_shadow_block_from_txs(
            builder,
            chainstate,
            &sortdb.index_handle(&burn_tip.sortition_id),
            &tenure_id_consensus_hash,
            block_txs,
        )?;

        shadow_block.header.version |= 0x80;

        // no need to sign with the signer set; just the miner is sufficient
        // (and it can be any miner)
        shadow_block.header.sign_miner(&miner_key)?;

        Ok(shadow_block)
    }
}

impl NakamotoStagingBlocksConnRef<'_> {
    /// Determine if we have a particular block with the given index hash.
    /// Returns Ok(true) if so
    /// Returns Ok(false) if not
    /// Returns Err(..) on DB error
    pub fn has_shadow_nakamoto_block_with_index_hash(
        &self,
        index_block_hash: &StacksBlockId,
    ) -> Result<bool, ChainstateError> {
        let qry = "SELECT 1 FROM nakamoto_staging_blocks WHERE index_block_hash = ?1 AND obtain_method = ?2";
        let args = params![
            index_block_hash,
            &NakamotoBlockObtainMethod::Shadow.to_string()
        ];
        let res: Option<i64> = query_row(self, qry, args)?;
        Ok(res.is_some())
    }

    /// Is this a shadow tenure?
    /// If any block is a shadow block in the tenure, they must all be.
    ///
    /// Returns true if the tenure has at least one shadow block.
    pub fn is_shadow_tenure(
        &self,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, ChainstateError> {
        let qry = "SELECT 1 FROM nakamoto_staging_blocks WHERE consensus_hash = ?1 AND obtain_method = ?2";
        let args = rusqlite::params![
            consensus_hash,
            NakamotoBlockObtainMethod::Shadow.to_string()
        ];
        let present: Option<u32> = query_row(self, qry, args)?;
        Ok(present.is_some())
    }

    /// Shadow blocks, unlike Stacks blocks, have a unique place in the chain history.
    /// They are inserted post-hoc, so they and their underlying burnchain blocks don't get
    /// invalidated via a fork.  A consensus hash can identify (1) no tenures, (2) a single
    /// shadow tenure, or (3) one or more non-shadow tenures.
    ///
    /// This is important when downloading a tenure that is ended by a shadow block, since it won't
    /// be processed beforehand and its hash isn't learned from the burnchain (so we must be able
    /// to infer that if this is a shadow tenure, none of the blocks in it have siblings).
    pub fn get_shadow_tenure_start_block(
        &self,
        ch: &ConsensusHash,
    ) -> Result<Option<NakamotoBlock>, ChainstateError> {
        let qry = "SELECT data FROM nakamoto_staging_blocks WHERE consensus_hash = ?1 AND obtain_method = ?2 ORDER BY height DESC LIMIT 1";
        let args = params![ch, &NakamotoBlockObtainMethod::Shadow.to_string()];
        let res: Option<Vec<u8>> = query_row(self, qry, args)?;
        let Some(block_bytes) = res else {
            return Ok(None);
        };
        let block = NakamotoBlock::consensus_deserialize(&mut block_bytes.as_slice())?;
        if !block.is_shadow_block() {
            error!("Staging DB corruption: expected shadow block from {}", ch);
            return Err(DBError::Corruption.into());
        }
        Ok(Some(block))
    }
}

impl NakamotoStagingBlocksTx<'_> {
    /// Add a shadow block.
    /// Fails if there are any non-shadow blocks present in the tenure.
    pub fn add_shadow_block(&self, shadow_block: &NakamotoBlock) -> Result<(), ChainstateError> {
        if !shadow_block.is_shadow_block() {
            return Err(ChainstateError::InvalidStacksBlock(
                "Not a shadow block".into(),
            ));
        }
        let block_id = shadow_block.block_id();

        // is this block stored already?
        let qry = "SELECT 1 FROM nakamoto_staging_blocks WHERE index_block_hash = ?1";
        let args = params![block_id];
        let present: Option<i64> = query_row(self, qry, args)?;
        if present.is_some() {
            return Ok(());
        }

        // this tenure must be empty, or it must be a shadow tenure
        let qry = "SELECT 1 FROM nakamoto_staging_blocks WHERE consensus_hash = ?1";
        let args = rusqlite::params![&shadow_block.header.consensus_hash];
        let present: Option<u32> = query_row(self, qry, args)?;
        if present.is_some()
            && !self
                .conn()
                .is_shadow_tenure(&shadow_block.header.consensus_hash)?
        {
            return Err(ChainstateError::InvalidStacksBlock(
                "Shadow block cannot be inserted into non-empty non-shadow tenure".into(),
            ));
        }

        // there must not be a block at this height in this tenure
        let qry = "SELECT 1 FROM nakamoto_staging_blocks WHERE consensus_hash = ?1 AND height = ?2";
        let args = rusqlite::params![
            &shadow_block.header.consensus_hash,
            u64_to_sql(shadow_block.header.chain_length)?
        ];
        let present: Option<u32> = query_row(self, qry, args)?;
        if present.is_some() {
            return Err(ChainstateError::InvalidStacksBlock(format!(
                "Conflicting block at height {} in tenure {}",
                shadow_block.header.chain_length, &shadow_block.header.consensus_hash
            )));
        }

        // the shadow block is crafted post-hoc, so we know the consensus hash exists.
        // thus, it's always burn-attachable
        let burn_attachable = true;

        // shadow blocks cannot be replaced
        let signing_weight = u32::MAX;

        self.store_block(
            shadow_block,
            burn_attachable,
            signing_weight,
            NakamotoBlockObtainMethod::Shadow,
        )?;
        Ok(())
    }
}

/// DO NOT RUN ON A RUNNING NODE (unless you're testing).
///
/// Insert and process a shadow block into the Stacks chainstate.
pub fn process_shadow_block(
    chain_state: &mut StacksChainState,
    sort_db: &mut SortitionDB,
    shadow_block: NakamotoBlock,
) -> Result<(), ChainstateError> {
    let tx = chain_state.staging_db_tx_begin()?;
    tx.add_shadow_block(&shadow_block)?;
    tx.commit()?;

    let no_dispatch: Option<DummyEventDispatcher> = None;
    loop {
        let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())?;

        // process at most one block per loop pass
        let processed_block_receipt = match NakamotoChainState::process_next_nakamoto_block(
            chain_state,
            sort_db,
            &sort_tip.sortition_id,
            no_dispatch.as_ref(),
            false,
        ) {
            Ok(receipt_opt) => receipt_opt,
            Err(ChainstateError::InvalidStacksBlock(msg)) => {
                warn!("Encountered invalid block: {msg}");
                continue;
            }
            Err(ChainstateError::NetError(NetError::DeserializeError(msg))) => {
                // happens if we load a zero-sized block (i.e. an invalid block)
                warn!("Encountered invalid block (codec error): {msg}");
                continue;
            }
            Err(e) => {
                // something else happened
                return Err(e);
            }
        };

        if processed_block_receipt.is_none() {
            // out of blocks
            info!("No more blocks to process (no receipts)");
            break;
        };

        let Some((_, processed, orphaned, _)) = chain_state
            .nakamoto_blocks_db()
            .get_block_processed_and_signed_weight(
                &shadow_block.header.consensus_hash,
                &shadow_block.header.block_hash(),
            )?
        else {
            return Err(ChainstateError::InvalidStacksBlock(format!(
                "Shadow block {} for tenure {} not store",
                &shadow_block.block_id(),
                &shadow_block.header.consensus_hash
            )));
        };

        if orphaned {
            return Err(ChainstateError::InvalidStacksBlock(format!(
                "Shadow block {} for tenure {} was orphaned",
                &shadow_block.block_id(),
                &shadow_block.header.consensus_hash
            )));
        }

        if processed {
            break;
        }
    }
    Ok(())
}

/// DO NOT RUN ON A RUNNING NODE (unless you're testing).
///
/// Automatically repair a node that has been stalled due to an empty prepare phase.
/// Works by synthesizing, inserting, and processing shadow tenures in-between the last sortition
/// with a winner and the burnchain tip.
///
/// This is meant to be accessed by the tooling. Once the blocks are synthesized, they would be
/// added into other broken nodes' chainstates by the same tooling.  Ultimately, a patched node
/// would be released with these shadow blocks added in as part of the chainstate schema.
///
/// Returns the syntheisized shadow blocks on success.
/// Returns error on failure.
pub fn shadow_chainstate_repair(
    chain_state: &mut StacksChainState,
    sort_db: &mut SortitionDB,
) -> Result<Vec<NakamotoBlock>, ChainstateError> {
    let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())?;

    let header = NakamotoChainState::get_canonical_block_header(chain_state.db(), sort_db)?
        .ok_or_else(|| ChainstateError::NoSuchBlockError)?;

    let header_sn =
        SortitionDB::get_block_snapshot_consensus(sort_db.conn(), &header.consensus_hash)?
            .ok_or_else(|| {
                ChainstateError::InvalidStacksBlock(
                    "Canonical stacks header does not have a sortition".into(),
                )
            })?;

    let mut shadow_blocks = vec![];
    for burn_height in (header_sn.block_height + 1)..sort_tip.block_height {
        let sort_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())?;
        let sort_handle = sort_db.index_handle(&sort_tip.sortition_id);
        let sn = sort_handle
            .get_block_snapshot_by_height(burn_height)?
            .ok_or_else(|| ChainstateError::InvalidStacksBlock("No sortition at height".into()))?;

        let header = NakamotoChainState::get_canonical_block_header(chain_state.db(), sort_db)?
            .ok_or_else(|| ChainstateError::NoSuchBlockError)?;

        let chain_tip = header.index_block_hash();
        let shadow_block = NakamotoBlockBuilder::make_shadow_tenure(
            chain_state,
            sort_db,
            chain_tip.clone(),
            sn.consensus_hash,
            vec![],
        )?;

        shadow_blocks.push(shadow_block.clone());

        process_shadow_block(chain_state, sort_db, shadow_block)?;
    }

    Ok(shadow_blocks)
}
