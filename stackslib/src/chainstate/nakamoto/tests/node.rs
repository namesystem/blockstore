// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2022 Stacks Open Internet Foundation
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

use std::cell::RefCell;
use std::collections::{HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::{fs, io};

use clarity::vm::clarity::ClarityConnection;
use clarity::vm::costs::{ExecutionCost, LimitedCostTracker};
use clarity::vm::types::*;
use hashbrown::HashMap;
use rand::seq::SliceRandom;
use rand::{CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use rusqlite::params;
use stacks_common::address::*;
use stacks_common::consts::{FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH};
use stacks_common::types::chainstate::{
    BlockHeaderHash, SortitionId, StacksAddress, StacksBlockId, VRFSeed,
};
use stacks_common::util::hash::{hex_bytes, Hash160};
use stacks_common::util::secp256k1::Secp256k1PrivateKey;
use stacks_common::util::sleep_ms;
use stacks_common::util::vrf::{VRFProof, VRFPublicKey};

use crate::burnchains::bitcoin::indexer::BitcoinIndexer;
use crate::burnchains::tests::*;
use crate::burnchains::*;
use crate::chainstate::burn::db::sortdb::*;
use crate::chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp,
};
use crate::chainstate::burn::*;
use crate::chainstate::coordinator::tests::NullEventDispatcher;
use crate::chainstate::coordinator::{
    ChainsCoordinator, Error as CoordinatorError, OnChainRewardSetProvider,
};
use crate::chainstate::nakamoto::coordinator::{
    get_nakamoto_next_recipients, load_nakamoto_reward_set,
};
use crate::chainstate::nakamoto::miner::{MinerTenureInfo, NakamotoBlockBuilder};
use crate::chainstate::nakamoto::staging_blocks::{
    NakamotoBlockObtainMethod, NakamotoStagingBlocksConnRef,
};
use crate::chainstate::nakamoto::test_signers::TestSigners;
use crate::chainstate::nakamoto::tests::get_account;
use crate::chainstate::nakamoto::{
    NakamotoBlock, NakamotoBlockHeader, NakamotoChainState, StacksDBIndexed,
};
use crate::chainstate::stacks::address::PoxAddress;
use crate::chainstate::stacks::db::blocks::test::store_staging_block;
use crate::chainstate::stacks::db::test::*;
use crate::chainstate::stacks::db::*;
use crate::chainstate::stacks::miner::*;
use crate::chainstate::stacks::tests::TestStacksNode;
use crate::chainstate::stacks::{
    Error as ChainstateError, StacksBlock, C32_ADDRESS_VERSION_TESTNET_SINGLESIG, *,
};
use crate::core::{BOOT_BLOCK_HASH, STACKS_EPOCH_3_0_MARKER};
use crate::cost_estimates::metrics::UnitMetric;
use crate::cost_estimates::UnitEstimator;
use crate::net::relay::{BlockAcceptResponse, Relayer};
use crate::net::test::{TestPeer, TestPeerConfig, *};
use crate::util_lib::boot::boot_code_addr;
use crate::util_lib::db::{query_row, Error as db_error};

#[derive(Debug, Clone)]
pub struct TestStacker {
    /// Key used to send stacking transactions
    pub stacker_private_key: StacksPrivateKey,
    /// Signer key for this stacker
    pub signer_private_key: StacksPrivateKey,
    /// amount of uSTX stacked
    pub amount: u128,
    /// PoX address to stack to (defaults to a fixed PoX address if not given)
    pub pox_addr: Option<PoxAddress>,
    /// Maximum amount to stack (defaults to u128::MAX)
    pub max_amount: Option<u128>,
}

impl TestStacker {
    pub const DEFAULT_STACKER_AMOUNT: u128 = 1_000_000_000_000_000_000;
    pub fn from_seed(seed: &[u8]) -> TestStacker {
        let stacker_private_key = StacksPrivateKey::from_seed(seed);
        let mut signer_seed = seed.to_vec();
        signer_seed.append(&mut vec![0xff, 0x00, 0x00, 0x00]);
        let signer_private_key = StacksPrivateKey::from_seed(signer_seed.as_slice());
        TestStacker {
            stacker_private_key,
            signer_private_key,
            amount: 1_000_000_000_000_000_000,
            pox_addr: None,
            max_amount: None,
        }
    }

    pub fn signer_public_key(&self) -> StacksPublicKey {
        StacksPublicKey::from_private(&self.signer_private_key)
    }

    /// make a set of stackers who will share a single signing key and stack with
    /// `Self::DEFAULT_STACKER_AMOUNT`
    pub fn common_signing_set() -> (TestSigners, Vec<TestStacker>) {
        let num_keys: u32 = 10;
        let mut signing_key_seed = num_keys.to_be_bytes().to_vec();
        signing_key_seed.extend_from_slice(&[1, 1, 1, 1]);
        let signing_key = StacksPrivateKey::from_seed(signing_key_seed.as_slice());
        let stackers = (0..num_keys)
            .map(|index| TestStacker {
                signer_private_key: signing_key.clone(),
                stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
                amount: Self::DEFAULT_STACKER_AMOUNT,
                pox_addr: None,
                max_amount: None,
            })
            .collect::<Vec<_>>();

        let test_signers = TestSigners::new(vec![signing_key]);
        (test_signers, stackers)
    }

    /// make a set of stackers who will share a set of keys and stack with
    /// `Self::DEFAULT_STACKER_AMOUNT`
    ///
    /// `key_distribution.len()` stackers will be created
    /// `key_distribution[i]` is the ID of key that the ith stacker will use.
    /// The ID is opaque -- it's used as a seed to generate the key.
    /// Each set of stackers with the same key ID will be given its own PoX address
    pub fn multi_signing_set(key_distribution: &[u8]) -> (TestSigners, Vec<TestStacker>) {
        let stackers = key_distribution
            .iter()
            .enumerate()
            .map(|(index, key_seed)| {
                let signing_key = StacksPrivateKey::from_seed(&[*key_seed]);
                let pox_key = StacksPrivateKey::from_seed(&[*key_seed, *key_seed]);
                let addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(&pox_key));
                let pox_addr =
                    PoxAddress::from_legacy(AddressHashMode::SerializeP2PKH, addr.bytes().clone());

                TestStacker {
                    signer_private_key: signing_key.clone(),
                    stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
                    amount: Self::DEFAULT_STACKER_AMOUNT,
                    pox_addr: Some(pox_addr),
                    max_amount: Some(u128::MAX - u128::try_from(index).unwrap()),
                }
            })
            .collect::<Vec<_>>();

        // N.B. the .to_hex() is needed because Secp256k1PrivateKey does not implement Hash
        let unique_signers: HashSet<_> = stackers
            .iter()
            .map(|st| st.signer_private_key.to_hex())
            .collect();
        let test_signers = TestSigners::new(
            unique_signers
                .into_iter()
                .map(|sk_hex| Secp256k1PrivateKey::from_hex(&sk_hex).unwrap())
                .collect(),
        );
        (test_signers, stackers)
    }
}

impl TestBurnchainBlock {
    pub fn add_nakamoto_tenure_commit(
        &mut self,
        ic: &SortitionDBConn,
        miner: &mut TestMiner,
        last_tenure_id: &StacksBlockId,
        burn_fee: u64,
        leader_key: &LeaderKeyRegisterOp,
        fork_snapshot: Option<&BlockSnapshot>,
        parent_block_snapshot: Option<&BlockSnapshot>,
        vrf_seed: VRFSeed,
        parent_is_shadow_block: bool,
    ) -> LeaderBlockCommitOp {
        let tenure_id_as_block_hash = BlockHeaderHash(last_tenure_id.0.clone());
        self.inner_add_block_commit(
            ic,
            miner,
            &tenure_id_as_block_hash,
            burn_fee,
            leader_key,
            fork_snapshot,
            parent_block_snapshot,
            Some(vrf_seed),
            STACKS_EPOCH_3_0_MARKER,
            parent_is_shadow_block,
        )
    }
}

impl TestMiner {
    pub fn nakamoto_miner_key(&self) -> StacksPrivateKey {
        self.privks[0].clone()
    }

    pub fn nakamoto_miner_hash160(&self) -> Hash160 {
        let pubk = StacksPublicKey::from_private(&self.nakamoto_miner_key());
        Hash160::from_node_public_key(&pubk)
    }

    pub fn make_nakamoto_coinbase(
        &mut self,
        recipient: Option<PrincipalData>,
        vrf_proof: VRFProof,
    ) -> StacksTransaction {
        self.make_nakamoto_coinbase_with_nonce(recipient, vrf_proof, self.nonce)
    }

    pub fn make_nakamoto_coinbase_with_nonce(
        &mut self,
        recipient: Option<PrincipalData>,
        vrf_proof: VRFProof,
        nonce: u64,
    ) -> StacksTransaction {
        self.make_nakamoto_coinbase_with_nonce_and_payload(
            recipient,
            vrf_proof,
            nonce,
            CoinbasePayload([(self.nonce % 256) as u8; 32]),
        )
    }

    pub fn make_nakamoto_coinbase_with_nonce_and_payload(
        &mut self,
        recipient: Option<PrincipalData>,
        vrf_proof: VRFProof,
        nonce: u64,
        payload: CoinbasePayload,
    ) -> StacksTransaction {
        let mut tx_coinbase = StacksTransaction::new(
            TransactionVersion::Testnet,
            self.as_transaction_auth().unwrap(),
            TransactionPayload::Coinbase(payload, recipient, Some(vrf_proof)),
        );
        tx_coinbase.chain_id = self.chain_id;
        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
        tx_coinbase.auth.set_origin_nonce(nonce);

        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
        self.sign_as_origin(&mut tx_signer);
        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
        tx_coinbase_signed
    }

    pub fn make_nakamoto_tenure_change(
        &mut self,
        tenure_change: TenureChangePayload,
    ) -> StacksTransaction {
        self.make_nakamoto_tenure_change_with_nonce(tenure_change, self.nonce)
    }

    pub fn make_nakamoto_tenure_change_with_nonce(
        &mut self,
        tenure_change: TenureChangePayload,
        nonce: u64,
    ) -> StacksTransaction {
        let mut tx_tenure_change = StacksTransaction::new(
            TransactionVersion::Testnet,
            self.as_transaction_auth().unwrap(),
            TransactionPayload::TenureChange(tenure_change),
        );
        tx_tenure_change.chain_id = self.chain_id;
        tx_tenure_change.anchor_mode = TransactionAnchorMode::OnChainOnly;
        tx_tenure_change.auth.set_origin_nonce(nonce);

        let mut tx_signer = StacksTransactionSigner::new(&tx_tenure_change);
        self.sign_as_origin(&mut tx_signer);
        let tx_tenure_change_signed = tx_signer.get_tx().unwrap();
        tx_tenure_change_signed
    }

    pub fn sign_nakamoto_block(&self, block: &mut NakamotoBlock) {
        block.header.sign_miner(&self.nakamoto_miner_key()).unwrap();
    }
}

impl NakamotoStagingBlocksConnRef<'_> {
    pub fn get_any_normal_tenure(&self) -> Result<Option<ConsensusHash>, ChainstateError> {
        let qry = "SELECT consensus_hash FROM nakamoto_staging_blocks WHERE obtain_method != ?1 ORDER BY RANDOM() LIMIT 1";
        let args = params![&NakamotoBlockObtainMethod::Shadow.to_string()];
        let res: Option<ConsensusHash> = query_row(self, qry, args)?;
        Ok(res)
    }
}

impl TestStacksNode {
    pub fn add_nakamoto_tenure_commit(
        sortdb: &SortitionDB,
        burn_block: &mut TestBurnchainBlock,
        miner: &mut TestMiner,
        last_tenure_start: &StacksBlockId,
        burn_amount: u64,
        key_op: &LeaderKeyRegisterOp,
        parent_block_snapshot: Option<&BlockSnapshot>,
        vrf_seed: VRFSeed,
        parent_is_shadow_block: bool,
    ) -> LeaderBlockCommitOp {
        let block_commit_op = {
            let ic = sortdb.index_conn();
            let parent_snapshot = burn_block.parent_snapshot.clone();
            burn_block.add_nakamoto_tenure_commit(
                &ic,
                miner,
                last_tenure_start,
                burn_amount,
                key_op,
                Some(&parent_snapshot),
                parent_block_snapshot,
                vrf_seed,
                parent_is_shadow_block,
            )
        };
        block_commit_op
    }

    pub fn get_last_nakamoto_tenure(&self, miner: &TestMiner) -> Option<Vec<NakamotoBlock>> {
        match miner.last_block_commit() {
            None => None,
            Some(block_commit_op) => {
                let last_tenure_id = block_commit_op.last_tenure_id();
                debug!(
                    "Last block commit was for {}: {:?}",
                    &last_tenure_id, &block_commit_op
                );
                match self.nakamoto_commit_ops.get(&last_tenure_id) {
                    None => {
                        debug!("No Nakamoto index for {}", &last_tenure_id);
                        None
                    }
                    Some(idx) => match self.nakamoto_blocks.get(*idx) {
                        Some(nakamoto_blocks) => Some(nakamoto_blocks.clone()),
                        None => {
                            debug!("Nakamoto block index {} does not correspond to list of mined nakamoto tenures (len {})", idx, self.nakamoto_blocks.len());
                            None
                        }
                    },
                }
            }
        }
    }

    pub fn get_nakamoto_tenure(
        &self,
        last_tenure_id: &StacksBlockId,
    ) -> Option<Vec<NakamotoBlock>> {
        match self.nakamoto_commit_ops.get(last_tenure_id) {
            None => None,
            Some(idx) => Some(self.nakamoto_blocks[*idx].clone()),
        }
    }

    /// Begin the next nakamoto tenure by triggering a tenure-change.
    /// Follow this call with a call to self.add_nakamoto_tenure_blocks() to add the corresponding
    /// blocks, once they've been generated.
    pub fn make_nakamoto_tenure_commitment(
        &mut self,
        sortdb: &SortitionDB,
        burn_block: &mut TestBurnchainBlock,
        miner: &mut TestMiner,
        last_tenure_id: &StacksBlockId,
        burn_amount: u64,
        miner_key: &LeaderKeyRegisterOp,
        parent_block_snapshot_opt: Option<&BlockSnapshot>,
        expect_success: bool,
        parent_is_shadow_block: bool,
    ) -> LeaderBlockCommitOp {
        info!(
            "Miner {}: Commit to Nakamoto tenure starting at {}",
            miner.id, &last_tenure_id,
        );

        let parent_block =
            NakamotoChainState::get_block_header(self.chainstate.db(), last_tenure_id)
                .unwrap()
                .unwrap();
        let vrf_proof = NakamotoChainState::get_block_vrf_proof(
            &mut self.chainstate.index_conn(),
            &parent_block.index_block_hash(),
            &parent_block.consensus_hash,
        )
        .unwrap()
        .unwrap();

        debug!(
            "proof from parent in {} is {}",
            &parent_block.consensus_hash,
            &vrf_proof.to_hex()
        );
        let vrf_seed = VRFSeed::from_proof(&vrf_proof);

        // send block commit for this block
        let block_commit_op = TestStacksNode::add_nakamoto_tenure_commit(
            sortdb,
            burn_block,
            miner,
            last_tenure_id,
            burn_amount,
            miner_key,
            parent_block_snapshot_opt,
            vrf_seed,
            parent_is_shadow_block,
        );

        test_debug!(
            "Miner {}: Nakamoto tenure commit transaction builds on {},{} (parent snapshot is {:?}). Expect success? {}",
            miner.id,
            block_commit_op.parent_block_ptr,
            block_commit_op.parent_vtxindex,
            &parent_block_snapshot_opt,
            expect_success
        );

        if expect_success {
            // NOTE: self.nakamoto_commit_ops[block_header_hash] now contains an index into
            // self.nakamoto_blocks that doesn't exist.  The caller needs to follow this call with a
            // call to self.add_nakamoto_tenure_blocks()
            self.nakamoto_commit_ops
                .insert(last_tenure_id.clone(), self.nakamoto_blocks.len());
        } else {
            // this extends the last tenure
            self.nakamoto_commit_ops
                .insert(last_tenure_id.clone(), self.nakamoto_blocks.len() - 1);
        }
        block_commit_op
    }

    /// Record the nakamoto blocks as a new tenure
    pub fn add_nakamoto_tenure_blocks(&mut self, tenure_blocks: Vec<NakamotoBlock>) {
        if let Some(last_tenure) = self.nakamoto_blocks.last_mut() {
            if !tenure_blocks.is_empty() {
                // this tenure is overwriting the last tenure
                if last_tenure.first().unwrap().header.consensus_hash
                    == tenure_blocks.first().unwrap().header.consensus_hash
                {
                    *last_tenure = tenure_blocks;
                    return;
                }
            }
        }
        self.nakamoto_blocks.push(tenure_blocks);
    }

    /// Record the nakamoto blocks as an extension of the current tenure
    pub fn add_nakamoto_extended_blocks(&mut self, mut tenure_blocks: Vec<NakamotoBlock>) {
        if let Some(ref mut blks) = self.nakamoto_blocks.last_mut() {
            blks.append(&mut tenure_blocks);
        } else {
            panic!("Tried to extend a tenure when no tenures exist");
        }
    }

    /// Begin the next Nakamoto tenure.
    /// Create a block-commit, as well as a tenure change and VRF proof for use in a follow-on call
    /// to make_nakamoto_tenure_blocks()
    pub fn begin_nakamoto_tenure(
        &mut self,
        sortdb: &SortitionDB,
        miner: &mut TestMiner,
        burn_block: &mut TestBurnchainBlock,
        miner_key: &LeaderKeyRegisterOp,
        // parent Stacks block, if this is the first Nakamoto tenure
        parent_stacks_block: Option<&StacksBlock>,
        // parent Nakamoto blocks, if we're building atop a previous Nakamoto tenure
        parent_nakamoto_tenure: Option<&[NakamotoBlock]>,
        burn_amount: u64,
        tenure_change_cause: TenureChangeCause,
    ) -> (LeaderBlockCommitOp, TenureChangePayload) {
        // this is the tenure that the block-commit confirms.
        // It's not the last-ever tenure; it's the one just before it.
        let (last_tenure_id, parent_block_snapshot, parent_is_shadow) = if let Some(parent_blocks) =
            parent_nakamoto_tenure
        {
            // parent is an epoch 3 nakamoto block
            let first_parent = parent_blocks.first().unwrap();
            let last_parent = parent_blocks.last().unwrap();
            let parent_tenure_id = StacksBlockId::new(
                &first_parent.header.consensus_hash,
                &first_parent.header.block_hash(),
            );

            let parent_sortition = if last_parent.is_shadow_block() {
                // load up sortition that the shadow block replaces
                SortitionDB::get_block_snapshot_consensus(
                    sortdb.conn(),
                    &last_parent.header.consensus_hash,
                )
                .unwrap()
                .unwrap()
            } else {
                // parent sortition must be the last sortition _with a winner_.
                // This is not guaranteed with shadow blocks, so we have to search back if
                // necessary.
                let mut cursor = first_parent.header.consensus_hash;
                let parent_sortition = loop {
                    let parent_sortition =
                        SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &cursor)
                            .unwrap()
                            .unwrap();

                    if parent_sortition.sortition {
                        break parent_sortition;
                    }

                    // last tenure was a shadow tenure?
                    let Ok(Some(tenure_start_header)) =
                        NakamotoChainState::get_tenure_start_block_header(
                            &mut self.chainstate.index_conn(),
                            &parent_tenure_id,
                            &cursor,
                        )
                    else {
                        panic!("No tenure-start block header for tenure {}", &cursor);
                    };

                    let version = tenure_start_header
                        .anchored_header
                        .as_stacks_nakamoto()
                        .unwrap()
                        .version;

                    assert!(NakamotoBlockHeader::is_shadow_block_version(version));
                    cursor = self
                        .chainstate
                        .index_conn()
                        .get_parent_tenure_consensus_hash(
                            &tenure_start_header.index_block_hash(),
                            &cursor,
                        )
                        .unwrap()
                        .unwrap();
                };
                parent_sortition
            };

            test_debug!(
                    "Work in {} {} for Nakamoto parent: {},{}. Last tenure ID is {}. Parent sortition is {}",
                    burn_block.block_height,
                    burn_block.parent_snapshot.burn_header_hash,
                    parent_sortition.total_burn,
                    last_parent.header.chain_length + 1,
                    &parent_tenure_id,
                    &parent_sortition.consensus_hash
                );

            (
                parent_tenure_id,
                parent_sortition,
                last_parent.is_shadow_block(),
            )
        } else if let Some(parent_stacks_block) = parent_stacks_block {
            // building off an existing stacks block
            let parent_stacks_block_snapshot = {
                let ic = sortdb.index_conn();
                let parent_stacks_block_snapshot =
                    SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &ic,
                        &burn_block.parent_snapshot.sortition_id,
                        &parent_stacks_block.block_hash(),
                    )
                    .unwrap()
                    .unwrap();
                parent_stacks_block_snapshot
            };

            let parent_chain_tip = StacksChainState::get_anchored_block_header_info(
                self.chainstate.db(),
                &parent_stacks_block_snapshot.consensus_hash,
                &parent_stacks_block.header.block_hash(),
            )
            .unwrap()
            .unwrap();

            let parent_tenure_id = parent_chain_tip.index_block_hash();

            test_debug!(
                "Work in {} {} for Stacks 2.x parent: {},{}. Last tenure ID is {}",
                burn_block.block_height,
                burn_block.parent_snapshot.burn_header_hash,
                parent_stacks_block_snapshot.total_burn,
                parent_chain_tip.anchored_header.height(),
                &parent_tenure_id,
            );

            (parent_tenure_id, parent_stacks_block_snapshot, false)
        } else {
            panic!("Neither Nakamoto nor epoch2 parent found");
        };

        // the tenure-change contains a pointer to the end of the last tenure, which is currently
        // the canonical tip unless overridden
        let (previous_tenure_end, previous_tenure_consensus_hash, previous_tenure_blocks) =
            if let Some(nakamoto_parent_tenure) = parent_nakamoto_tenure.as_ref() {
                let start_block = nakamoto_parent_tenure.first().clone().unwrap();
                let end_block = nakamoto_parent_tenure.last().clone().unwrap();
                let tenure_len =
                    end_block.header.chain_length + 1 - start_block.header.chain_length;
                (
                    end_block.block_id(),
                    end_block.header.consensus_hash,
                    tenure_len as u32,
                )
            } else {
                let hdr =
                    NakamotoChainState::get_canonical_block_header(self.chainstate.db(), sortdb)
                        .unwrap()
                        .unwrap();
                if hdr.anchored_header.as_stacks_nakamoto().is_some() {
                    // building atop nakamoto
                    let tenure_len = NakamotoChainState::get_nakamoto_tenure_length(
                        self.chainstate.db(),
                        &hdr.index_block_hash(),
                    )
                    .unwrap();
                    debug!(
                        "Tenure length of Nakamoto tenure {} is {}; tipped at {}",
                        &hdr.consensus_hash,
                        tenure_len,
                        &hdr.index_block_hash()
                    );
                    (hdr.index_block_hash(), hdr.consensus_hash, tenure_len)
                } else {
                    // building atop epoch2 (so the parent block can't be a shadow block, meaning
                    // that parent_block_snapshot is _guaranteed_ to be the snapshot that chose
                    // last_tenure_id).
                    debug!(
                        "Tenure length of epoch2 tenure {} is {}; tipped at {}",
                        &parent_block_snapshot.consensus_hash, 1, &last_tenure_id
                    );
                    (
                        last_tenure_id,
                        parent_block_snapshot.consensus_hash.clone(),
                        1,
                    )
                }
            };

        let tenure_change_payload = TenureChangePayload {
            tenure_consensus_hash: ConsensusHash([0x00; 20]), // will be overwritten
            prev_tenure_consensus_hash: previous_tenure_consensus_hash,
            burn_view_consensus_hash: ConsensusHash([0x00; 20]), // will be overwritten
            previous_tenure_end,
            previous_tenure_blocks,
            cause: tenure_change_cause,
            pubkey_hash: miner.nakamoto_miner_hash160(),
        };

        test_debug!("TenureChangePayload: {:?}", &tenure_change_payload);

        let block_commit_op = self.make_nakamoto_tenure_commitment(
            sortdb,
            burn_block,
            miner,
            &last_tenure_id,
            burn_amount,
            miner_key,
            Some(&parent_block_snapshot),
            tenure_change_cause == TenureChangeCause::BlockFound,
            parent_is_shadow,
        );

        (block_commit_op, tenure_change_payload)
    }

    /// Construct or extend a full Nakamoto tenure with the given block builder.
    /// After block assembly, invoke `after_block` before signing and then processing.
    /// If `after_block` returns false, do not attempt to process the block, instead just
    /// add it to the result Vec and exit the block building loop (the block builder cannot
    /// build any subsequent blocks without processing the prior block)
    ///
    /// The first block will contain a coinbase, if coinbase is Some(..)
    /// Process the blocks via the chains coordinator as we produce them.
    ///
    /// If malleablize is true, then malleablized blocks will be created by varying the number of
    /// signatures. Each malleablized block will be processed and stored if its signatures clear
    /// the signing threshold.
    ///
    /// Returns a list of
    ///     * the block
    ///     * its size
    ///     * its execution cost
    ///     * a list of malleablized blocks with the same contents, if desired
    pub fn make_nakamoto_tenure_blocks<'a, S, F, G>(
        chainstate: &mut StacksChainState,
        sortdb: &mut SortitionDB,
        miner: &mut TestMiner,
        signers: &mut TestSigners,
        tenure_id_consensus_hash: &ConsensusHash,
        mut tenure_change: Option<StacksTransaction>,
        mut coinbase: Option<StacksTransaction>,
        coord: &mut ChainsCoordinator<
            'a,
            TestEventObserver,
            (),
            OnChainRewardSetProvider<'a, TestEventObserver>,
            (),
            (),
            BitcoinIndexer,
        >,
        mut miner_setup: S,
        mut block_builder: F,
        mut after_block: G,
        malleablize: bool,
        mined_canonical: bool,
    ) -> Result<Vec<(NakamotoBlock, u64, ExecutionCost, Vec<NakamotoBlock>)>, ChainstateError>
    where
        S: FnMut(&mut NakamotoBlockBuilder),
        F: FnMut(
            &mut TestMiner,
            &mut StacksChainState,
            &SortitionDB,
            &[(NakamotoBlock, u64, ExecutionCost)],
        ) -> Vec<StacksTransaction>,
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        let mut blocks = vec![];
        let mut all_malleablized_blocks = vec![];
        let mut block_count = 0;
        loop {
            let mut txs = vec![];
            if let Some(tenure_change) = tenure_change.clone().take() {
                txs.push(tenure_change);
            }
            if let Some(coinbase) = coinbase.clone().take() {
                txs.push(coinbase);
            }
            let mut next_block_txs = block_builder(miner, chainstate, sortdb, &blocks);
            txs.append(&mut next_block_txs);

            if txs.is_empty() {
                break;
            }

            // there may be a tenure-extend here. Go find it if so
            let mut parent_id_opt = None;
            for tx in txs.iter() {
                if let TransactionPayload::TenureChange(payload) = &tx.payload {
                    parent_id_opt = Some(payload.previous_tenure_end.clone());
                }
            }

            let parent_tip_opt = if let Some(parent_id) = parent_id_opt {
                if let Some(nakamoto_parent) =
                    NakamotoChainState::get_block_header(chainstate.db(), &parent_id)?
                {
                    debug!(
                        "Use parent tip identified by produced TenureChange ({})",
                        &parent_id
                    );
                    Some(nakamoto_parent)
                } else {
                    warn!("Produced Tenure change transaction does not point to a real block");
                    NakamotoChainState::get_canonical_block_header(chainstate.db(), sortdb)?
                }
            } else if let Some(tenure_change) = tenure_change.as_ref() {
                // make sure parent tip is consistent with a tenure change
                if let TransactionPayload::TenureChange(payload) = &tenure_change.payload {
                    if let Some(nakamoto_parent) = NakamotoChainState::get_block_header(
                        chainstate.db(),
                        &payload.previous_tenure_end,
                    )? {
                        debug!(
                            "Use parent tip identified by given TenureChange ({})",
                            &payload.previous_tenure_end
                        );
                        Some(nakamoto_parent)
                    } else {
                        debug!("Use parent tip identified by canonical tip pointer (no parent block {})", &payload.previous_tenure_end);
                        NakamotoChainState::get_canonical_block_header(chainstate.db(), sortdb)?
                    }
                } else {
                    panic!("Tenure change transaction does not have a TenureChange payload");
                }
            } else {
                NakamotoChainState::get_canonical_block_header(chainstate.db(), sortdb)?
            };

            let burn_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())?;

            debug!(
                "Build Nakamoto block in tenure {} sortition {} parent_tip {:?}",
                &tenure_id_consensus_hash,
                &burn_tip.consensus_hash,
                &parent_tip_opt.clone().map(|blk| blk.index_block_hash())
            );

            // make a block
            let mut builder = if let Some(parent_tip) = parent_tip_opt {
                NakamotoBlockBuilder::new(
                    &parent_tip,
                    tenure_id_consensus_hash,
                    burn_tip.total_burn,
                    if block_count == 0 && tenure_change.is_some() {
                        tenure_change.as_ref()
                    } else {
                        None
                    },
                    if block_count == 0 && coinbase.is_some() {
                        coinbase.as_ref()
                    } else {
                        None
                    },
                    1,
                    None,
                )?
            } else {
                NakamotoBlockBuilder::new_first_block(
                    &tenure_change.clone().unwrap(),
                    &coinbase.clone().unwrap(),
                )
            };
            miner_setup(&mut builder);

            tenure_change = None;
            coinbase = None;

            let (mut nakamoto_block, size, cost) = Self::make_nakamoto_block_from_txs(
                builder,
                chainstate,
                &sortdb.index_handle_at_tip(),
                txs,
            )?;
            let try_to_process = after_block(&mut nakamoto_block);
            miner.sign_nakamoto_block(&mut nakamoto_block);

            let tenure_sn =
                SortitionDB::get_block_snapshot_consensus(sortdb.conn(), tenure_id_consensus_hash)?
                    .ok_or_else(|| ChainstateError::NoSuchBlockError)?;

            let cycle = sortdb
                .pox_constants
                .block_height_to_reward_cycle(sortdb.first_block_height, tenure_sn.block_height)
                .unwrap();

            // Get the reward set
            let sort_tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())?;
            let reward_set = load_nakamoto_reward_set(
                miner
                    .burnchain
                    .block_height_to_reward_cycle(sort_tip_sn.block_height)
                    .expect("FATAL: no reward cycle for sortition"),
                &sort_tip_sn.sortition_id,
                &miner.burnchain,
                chainstate,
                &nakamoto_block.header.parent_block_id,
                sortdb,
                &OnChainRewardSetProvider::new(),
            )
            .expect("Failed to load reward set")
            .expect("Expected a reward set")
            .0
            .known_selected_anchor_block_owned()
            .expect("Unknown reward set");

            test_debug!(
                "Signing Nakamoto block {} in tenure {} with key in cycle {}",
                nakamoto_block.block_id(),
                tenure_id_consensus_hash,
                cycle
            );

            signers.sign_block_with_reward_set(&mut nakamoto_block, &reward_set);

            let block_id = nakamoto_block.block_id();

            if try_to_process {
                debug!(
                    "Process Nakamoto block {} ({:?}",
                    &block_id, &nakamoto_block.header
                );
            }
            debug!(
                "Nakamoto block {} txs: {:?}",
                &block_id, &nakamoto_block.txs
            );

            let sort_tip = SortitionDB::get_canonical_sortition_tip(sortdb.conn())?;
            let mut sort_handle = sortdb.index_handle(&sort_tip);
            let stacks_tip = sort_handle
                .get_nakamoto_tip_block_id()?
                .ok_or_else(|| ChainstateError::NoSuchBlockError)?;

            let mut block_to_store = nakamoto_block.clone();
            let mut processed_blocks = vec![];
            let mut malleablized_blocks = vec![];
            loop {
                // don't process if we don't have enough signatures
                if let Err(e) = block_to_store.header.verify_signer_signatures(&reward_set) {
                    info!(
                        "Will stop processing malleablized blocks for {}: {:?}",
                        &block_id, &e
                    );
                    break;
                }
                if block_to_store.block_id() == block_id {
                    info!("Processing the new nakamoto block {}", &block_id);
                } else {
                    info!(
                        "Processing the new malleablized nakamoto block {}, original is {}",
                        &block_to_store.block_id(),
                        &block_id
                    );
                    malleablized_blocks.push(block_to_store.clone());
                }

                let accepted = if try_to_process {
                    match Relayer::process_new_nakamoto_block(
                        &miner.burnchain,
                        sortdb,
                        &mut sort_handle,
                        chainstate,
                        &stacks_tip,
                        &block_to_store,
                        None,
                        NakamotoBlockObtainMethod::Pushed,
                    ) {
                        Ok(accepted) => accepted,
                        Err(e) => {
                            panic!("Failed to process nakamoto block: {e:?}\n{nakamoto_block:?}");
                        }
                    }
                } else {
                    BlockAcceptResponse::Rejected("try_to_process is false".into())
                };
                if accepted.is_accepted() {
                    test_debug!("Accepted Nakamoto block {}", &block_to_store.block_id());
                    coord.handle_new_nakamoto_stacks_block().unwrap();
                    processed_blocks.push(block_to_store.clone());

                    if block_to_store.block_id() == block_id && mined_canonical {
                        // confirm that the chain tip advanced -- we intended to mine on the
                        // canonical tip
                        let stacks_chain_tip = NakamotoChainState::get_canonical_block_header(
                            chainstate.db(),
                            sortdb,
                        )?
                        .ok_or_else(|| ChainstateError::NoSuchBlockError)?;
                        let nakamoto_chain_tip = stacks_chain_tip
                            .anchored_header
                            .as_stacks_nakamoto()
                            .expect("FATAL: chain tip is not a Nakamoto block");
                        assert_eq!(nakamoto_chain_tip, &nakamoto_block.header);
                    }
                } else if try_to_process {
                    test_debug!(
                        "Did NOT accept Nakamoto block {}",
                        &block_to_store.block_id()
                    );
                    break;
                } else {
                    test_debug!(
                        "Test will NOT process Nakamoto block {}",
                        &block_to_store.block_id()
                    );
                }

                if !malleablize {
                    debug!("Will not produce malleablized blocks");
                    break;
                }

                let num_sigs = block_to_store.header.signer_signature.len();

                // force this block to have a different sighash, in addition to different
                // signatures, so that both blocks are valid at a consensus level
                block_to_store.header.version += 1;
                block_to_store.header.signer_signature.clear();

                miner.sign_nakamoto_block(&mut block_to_store);
                signers.sign_block_with_reward_set(&mut block_to_store, &reward_set);

                while block_to_store.header.signer_signature.len() >= num_sigs {
                    block_to_store.header.signer_signature.pop();
                }
            }

            for processed_block in processed_blocks {
                debug!("Begin check Nakamoto block {}", &processed_block.block_id());
                TestPeer::check_processed_nakamoto_block(sortdb, chainstate, &processed_block);
                debug!("End check Nakamoto block {}", &processed_block.block_id());
            }
            blocks.push((nakamoto_block, size, cost));
            all_malleablized_blocks.push(malleablized_blocks);
            block_count += 1;
        }
        Ok(blocks
            .into_iter()
            .zip(all_malleablized_blocks)
            .map(|((blk, sz, cost), mals)| (blk, sz, cost, mals))
            .collect())
    }

    pub fn make_nakamoto_block_from_txs(
        mut builder: NakamotoBlockBuilder,
        chainstate_handle: &StacksChainState,
        burn_dbconn: &SortitionHandleConn,
        txs: Vec<StacksTransaction>,
    ) -> Result<(NakamotoBlock, u64, ExecutionCost), ChainstateError> {
        use clarity::vm::ast::ASTRules;

        debug!("Build Nakamoto block from {} transactions", txs.len());
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
            builder.load_tenure_info(&mut chainstate, burn_dbconn, tenure_cause)?;
        let mut tenure_tx = builder.tenure_begin(burn_dbconn, &mut miner_tenure_info)?;
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
                        ChainstateError::BlockTooBigError => {
                            // done mining -- our execution budget is exceeded.
                            // Make the block from the transactions we did manage to get
                            debug!("Block budget exceeded on tx {}", &tx.txid());
                        }
                        ChainstateError::InvalidStacksTransaction(_emsg, true) => {
                            // if we have an invalid transaction that was quietly ignored, don't warn here either
                            test_debug!(
                                "Failed to apply tx {}: InvalidStacksTransaction '{:?}'",
                                &tx.txid(),
                                &_emsg
                            );
                            continue;
                        }
                        ChainstateError::ProblematicTransaction(txid) => {
                            test_debug!("Encountered problematic transaction. Aborting");
                            return Err(ChainstateError::ProblematicTransaction(txid));
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
                    return Err(ChainstateError::ProblematicTransaction(tx.txid()));
                }
            }
        }
        let block = builder.mine_nakamoto_block(&mut tenure_tx);
        let size = builder.bytes_so_far;
        let cost = builder.tenure_finish(tenure_tx).unwrap();
        Ok((block, size, cost))
    }
}

impl TestPeer<'_> {
    /// Get the Nakamoto parent linkage data for building atop the last-produced tenure or
    /// Stacks 2.x block.
    /// Returns (last-tenure-id, epoch2-parent, nakamoto-parent-tenure, parent-sortition)
    fn get_nakamoto_parent(
        miner: &TestMiner,
        stacks_node: &TestStacksNode,
        sortdb: &SortitionDB,
    ) -> (
        StacksBlockId,
        Option<StacksBlock>,
        Option<Vec<NakamotoBlock>>,
    ) {
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        if let Some(parent_blocks) = stacks_node.get_last_nakamoto_tenure(miner) {
            debug!("Parent will be a Nakamoto block");

            // parent is an epoch 3 nakamoto block
            let first_parent = parent_blocks.first().unwrap();
            debug!("First parent is {:?}", first_parent);

            // sanity check -- this parent must correspond to a sortition
            assert!(
                SortitionDB::get_block_snapshot_consensus(
                    sortdb.conn(),
                    &first_parent.header.consensus_hash,
                )
                .unwrap()
                .unwrap()
                .sortition
            );

            let last_tenure_id = StacksBlockId::new(
                &first_parent.header.consensus_hash,
                &first_parent.header.block_hash(),
            );
            (last_tenure_id, None, Some(parent_blocks))
        } else {
            // parent may be an epoch 2.x block
            let (parent_opt, parent_sortition_opt) = if let Some(parent_block) =
                stacks_node.get_last_anchored_block(miner)
            {
                debug!("Parent will be a Stacks 2.x block");
                let ic = sortdb.index_conn();
                let sort_opt = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                    &ic,
                    &tip.sortition_id,
                    &parent_block.block_hash(),
                )
                .unwrap();
                if sort_opt.is_none() {
                    warn!("No parent sortition in epoch2: tip.sortition_id = {}, parent_block.block_hash() = {}", &tip.sortition_id, &parent_block.block_hash());
                }
                (Some(parent_block), sort_opt)
            } else {
                warn!(
                    "No parent sortition in epoch2: tip.sortition_id = {}",
                    &tip.sortition_id
                );
                (None, None)
            };

            let last_tenure_id = if let Some(last_epoch2_block) = parent_opt.as_ref() {
                let parent_sort = parent_sortition_opt.as_ref().unwrap();
                StacksBlockId::new(
                    &parent_sort.consensus_hash,
                    &last_epoch2_block.header.block_hash(),
                )
            } else {
                // must be a genesis block (testing only!)
                StacksBlockId(BOOT_BLOCK_HASH.0.clone())
            };
            (last_tenure_id, parent_opt, None)
        }
    }

    /// Start the next Nakamoto tenure.
    /// This generates the VRF key and block-commit txs, as well as the TenureChange and
    /// leader key this commit references
    pub fn begin_nakamoto_tenure(
        &mut self,
        tenure_change_cause: TenureChangeCause,
    ) -> (
        Vec<BlockstackOperationType>,
        TenureChangePayload,
        LeaderKeyRegisterOp,
    ) {
        let mut sortdb = self.sortdb.take().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();

        let mut burn_block = TestBurnchainBlock::new(&tip, 0);
        let mut stacks_node = self.stacks_node.take().unwrap();

        let (last_tenure_id, parent_block_opt, parent_tenure_opt) =
            if let Some(nakamoto_parent_tenure) = self.nakamoto_parent_tenure_opt.as_ref() {
                (
                    nakamoto_parent_tenure.first().as_ref().unwrap().block_id(),
                    None,
                    Some(nakamoto_parent_tenure.clone()),
                )
            } else {
                Self::get_nakamoto_parent(&self.miner, &stacks_node, &sortdb)
            };

        // find the VRF leader key register tx to use.
        // it's the one pointed to by the parent tenure
        let parent_consensus_hash_and_tenure_start_id_opt =
            if let Some(parent_tenure) = parent_tenure_opt.as_ref() {
                let tenure_start_block = parent_tenure.first().unwrap();
                Some((
                    tenure_start_block.header.consensus_hash,
                    tenure_start_block.block_id(),
                ))
            } else if let Some(parent_block) = parent_block_opt.as_ref() {
                let parent_header_info =
                    StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                        stacks_node.chainstate.db(),
                        &last_tenure_id,
                    )
                    .unwrap()
                    .unwrap();
                Some((
                    parent_header_info.consensus_hash,
                    parent_header_info.index_block_hash(),
                ))
            } else {
                None
            };

        let last_key = if let Some((ch, parent_tenure_start_block_id)) =
            parent_consensus_hash_and_tenure_start_id_opt.clone()
        {
            // it's possible that the parent was a shadow block.
            // if so, find the highest non-shadow ancestor's block-commit, so we can
            let mut cursor = ch;
            let (tenure_sn, tenure_block_commit) = loop {
                let tenure_sn = SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &cursor)
                    .unwrap()
                    .unwrap();

                let Some(tenure_block_commit) = get_block_commit_by_txid(
                    sortdb.conn(),
                    &tenure_sn.sortition_id,
                    &tenure_sn.winning_block_txid,
                )
                .unwrap() else {
                    // parent must be a shadow block
                    let header = NakamotoChainState::get_block_header_nakamoto(
                        stacks_node.chainstate.db(),
                        &parent_tenure_start_block_id,
                    )
                    .unwrap()
                    .unwrap()
                    .anchored_header
                    .as_stacks_nakamoto()
                    .cloned()
                    .unwrap();

                    if !header.is_shadow_block() {
                        panic!("Parent tenure start block ID {} has no block-commit and is not a shadow block", &parent_tenure_start_block_id);
                    }

                    cursor = stacks_node
                        .chainstate
                        .index_conn()
                        .get_parent_tenure_consensus_hash(&parent_tenure_start_block_id, &cursor)
                        .unwrap()
                        .unwrap();

                    continue;
                };
                break (tenure_sn, tenure_block_commit);
            };

            let tenure_leader_key = SortitionDB::get_leader_key_at(
                &sortdb.index_conn(),
                tenure_block_commit.key_block_ptr.into(),
                tenure_block_commit.key_vtxindex.into(),
                &tenure_sn.sortition_id,
            )
            .unwrap()
            .unwrap();
            tenure_leader_key
        } else {
            panic!("No leader key");
        };

        let network_id = self.config.network_id;
        let chainstate_path = self.chainstate_path.clone();
        let burn_block_height = burn_block.block_height;

        let (mut block_commit_op, tenure_change_payload) = stacks_node.begin_nakamoto_tenure(
            &sortdb,
            &mut self.miner,
            &mut burn_block,
            &last_key,
            parent_block_opt.as_ref(),
            parent_tenure_opt.as_ref().map(|blocks| blocks.as_slice()),
            1000,
            tenure_change_cause,
        );

        // patch up block-commit -- these blocks all mine off of genesis
        if last_tenure_id == StacksBlockId(BOOT_BLOCK_HASH.0.clone()) {
            block_commit_op.parent_block_ptr = 0;
            block_commit_op.parent_vtxindex = 0;
        }

        let mut burn_ops = vec![];
        if self.miner.last_VRF_public_key().is_none() {
            let leader_key_op = stacks_node.add_key_register(&mut burn_block, &mut self.miner);
            burn_ops.push(BlockstackOperationType::LeaderKeyRegister(leader_key_op));
        }

        // patch in reward set info
        match get_nakamoto_next_recipients(
            &tip,
            &mut sortdb,
            &mut stacks_node.chainstate,
            &tenure_change_payload.previous_tenure_end,
            &self.config.burnchain,
        ) {
            Ok(recipients) => {
                block_commit_op.commit_outs = match recipients {
                    Some(info) => {
                        let mut recipients = info
                            .recipients
                            .into_iter()
                            .map(|x| x.0)
                            .collect::<Vec<PoxAddress>>();
                        if recipients.len() == 1 {
                            recipients.push(PoxAddress::standard_burn_address(false));
                        }
                        recipients
                    }
                    None => {
                        if self
                            .config
                            .burnchain
                            .is_in_prepare_phase(burn_block.block_height)
                        {
                            vec![PoxAddress::standard_burn_address(false)]
                        } else {
                            vec![
                                PoxAddress::standard_burn_address(false),
                                PoxAddress::standard_burn_address(false),
                            ]
                        }
                    }
                };
                test_debug!(
                    "Block commit at height {} has {} recipients: {:?}",
                    block_commit_op.block_height,
                    block_commit_op.commit_outs.len(),
                    &block_commit_op.commit_outs
                );
            }
            Err(e) => {
                panic!("Failure fetching recipient set: {e:?}");
            }
        };

        burn_ops.push(BlockstackOperationType::LeaderBlockCommit(block_commit_op));

        // prepare to mine
        let miner_addr = self.miner.origin_address().unwrap();
        let miner_account = get_account(&mut stacks_node.chainstate, &sortdb, &miner_addr);
        self.miner.set_nonce(miner_account.nonce);

        self.stacks_node = Some(stacks_node);
        self.sortdb = Some(sortdb);
        (burn_ops, tenure_change_payload, last_key)
    }

    /// Make the VRF proof for this tenure.
    /// Call after processing the block-commit
    pub fn make_nakamoto_vrf_proof(&mut self, miner_key: LeaderKeyRegisterOp) -> VRFProof {
        let sortdb = self.sortdb.take().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        let proof = self
            .miner
            .make_proof(&miner_key.public_key, &tip.sortition_hash)
            .unwrap_or_else(|| panic!("FATAL: no private key for {:?}", miner_key.public_key));
        self.sortdb = Some(sortdb);
        debug!(
            "VRF proof made from {:?} over {}: {proof:?}",
            miner_key.public_key, &tip.sortition_hash
        );
        proof
    }

    pub fn try_process_block(
        &mut self,
        block: &NakamotoBlock,
        txindex: bool,
    ) -> Result<bool, ChainstateError> {
        let mut sort_handle = self.sortdb.as_ref().unwrap().index_handle_at_tip();
        let stacks_tip = sort_handle.get_nakamoto_tip_block_id().unwrap().unwrap();
        let accepted = Relayer::process_new_nakamoto_block(
            &self.config.burnchain,
            self.sortdb.as_ref().unwrap(),
            &mut sort_handle,
            &mut self.stacks_node.as_mut().unwrap().chainstate,
            &stacks_tip,
            block,
            None,
            NakamotoBlockObtainMethod::Pushed,
        )?;
        if !accepted.is_accepted() {
            return Ok(false);
        }
        let sort_tip = SortitionDB::get_canonical_sortition_tip(self.sortdb().conn()).unwrap();
        let Some(block_receipt) =
            NakamotoChainState::process_next_nakamoto_block::<NullEventDispatcher>(
                &mut self.stacks_node.as_mut().unwrap().chainstate,
                self.sortdb.as_mut().unwrap(),
                &sort_tip,
                None,
                txindex,
            )?
        else {
            return Ok(false);
        };
        if block_receipt.header.index_block_hash() == block.block_id() {
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Produce and process a Nakamoto tenure, after processing the block-commit from
    /// begin_nakamoto_tenure().  You'd process the burnchain ops from begin_nakamoto_tenure(),
    /// take the consensus hash, and feed it in here.
    ///
    /// Returns the blocks, their sizes, and runtime costs
    pub fn make_nakamoto_tenure<F>(
        &mut self,
        tenure_change: StacksTransaction,
        coinbase: StacksTransaction,
        signers: &mut TestSigners,
        block_builder: F,
    ) -> Vec<(NakamotoBlock, u64, ExecutionCost)>
    where
        F: FnMut(
            &mut TestMiner,
            &mut StacksChainState,
            &SortitionDB,
            &[(NakamotoBlock, u64, ExecutionCost)],
        ) -> Vec<StacksTransaction>,
    {
        self.make_nakamoto_tenure_and(
            tenure_change,
            coinbase,
            signers,
            |_| {},
            block_builder,
            |_| true,
        )
        .unwrap()
    }

    /// Produce and process a Nakamoto tenure, after processing the block-commit from
    /// begin_nakamoto_tenure().  You'd process the burnchain ops from begin_nakamoto_tenure(),
    /// take the consensus hash, and feed it in here.
    ///
    /// Returns the blocks, their sizes, and runtime costs
    pub fn make_nakamoto_tenure_and<S, F, G>(
        &mut self,
        tenure_change: StacksTransaction,
        coinbase: StacksTransaction,
        signers: &mut TestSigners,
        miner_setup: S,
        block_builder: F,
        after_block: G,
    ) -> Result<Vec<(NakamotoBlock, u64, ExecutionCost)>, ChainstateError>
    where
        S: FnMut(&mut NakamotoBlockBuilder),
        F: FnMut(
            &mut TestMiner,
            &mut StacksChainState,
            &SortitionDB,
            &[(NakamotoBlock, u64, ExecutionCost)],
        ) -> Vec<StacksTransaction>,
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        let cycle = self.get_reward_cycle();
        self.with_dbs(|peer, sortdb, stacks_node, mempool| {
            // Ensure the signers are setup for the current cycle
            signers.generate_aggregate_key(cycle);

            let blocks = TestStacksNode::make_nakamoto_tenure_blocks(
                &mut stacks_node.chainstate,
                sortdb,
                &mut peer.miner,
                signers,
                &tenure_change
                    .try_as_tenure_change()
                    .unwrap()
                    .tenure_consensus_hash
                    .clone(),
                Some(tenure_change),
                Some(coinbase),
                &mut peer.coord,
                miner_setup,
                block_builder,
                after_block,
                peer.mine_malleablized_blocks,
                peer.nakamoto_parent_tenure_opt.is_none(),
            )?;

            let just_blocks = blocks
                .clone()
                .into_iter()
                .map(|(block, _, _, _)| block)
                .collect();

            stacks_node.add_nakamoto_tenure_blocks(just_blocks);

            let mut malleablized_blocks: Vec<NakamotoBlock> = blocks
                .clone()
                .into_iter()
                .flat_map(|(_, _, _, malleablized)| malleablized)
                .collect();

            peer.malleablized_blocks.append(&mut malleablized_blocks);

            let block_data = blocks
                .into_iter()
                .map(|(blk, sz, cost, _)| (blk, sz, cost))
                .collect();

            Ok(block_data)
        })
    }

    /// Produce and process a Nakamoto tenure extension.
    /// `tenure_change_payload` is the original tenure-change payload for this tenure.
    /// `last_tenure_block_header` is the final block's header produced in the last batch of blocks
    /// `num_blocks_so_far` is the number of blocks produced so far in this tenure,
    /// Returns the blocks, their sizes, and runtime costs
    pub fn make_nakamoto_tenure_extension<F>(
        &mut self,
        tenure_extend_tx: StacksTransaction,
        signers: &mut TestSigners,
        block_builder: F,
    ) -> Vec<(NakamotoBlock, u64, ExecutionCost)>
    where
        F: FnMut(
            &mut TestMiner,
            &mut StacksChainState,
            &SortitionDB,
            &[(NakamotoBlock, u64, ExecutionCost)],
        ) -> Vec<StacksTransaction>,
    {
        let mut stacks_node = self.stacks_node.take().unwrap();
        let mut sortdb = self.sortdb.take().unwrap();

        let tenure_extend_payload =
            if let TransactionPayload::TenureChange(ref tc) = &tenure_extend_tx.payload {
                tc
            } else {
                panic!("Not a tenure-extend payload");
            };

        let tenure_start_sn = SortitionDB::get_block_snapshot_consensus(
            sortdb.conn(),
            &tenure_extend_payload.tenure_consensus_hash,
        )
        .unwrap()
        .unwrap();
        let cycle = sortdb
            .pox_constants
            .block_height_to_reward_cycle(sortdb.first_block_height, tenure_start_sn.block_height)
            .unwrap();

        // Ensure the signers are setup for the current cycle
        signers.generate_aggregate_key(cycle);

        let blocks = TestStacksNode::make_nakamoto_tenure_blocks(
            &mut stacks_node.chainstate,
            &mut sortdb,
            &mut self.miner,
            signers,
            &tenure_extend_tx
                .try_as_tenure_change()
                .unwrap()
                .tenure_consensus_hash
                .clone(),
            Some(tenure_extend_tx),
            None,
            &mut self.coord,
            |_| {},
            block_builder,
            |_| true,
            self.mine_malleablized_blocks,
            self.nakamoto_parent_tenure_opt.is_none(),
        )
        .unwrap();

        let just_blocks = blocks
            .clone()
            .into_iter()
            .map(|(block, _, _, _)| block)
            .collect();

        stacks_node.add_nakamoto_extended_blocks(just_blocks);

        let mut malleablized_blocks: Vec<NakamotoBlock> = blocks
            .clone()
            .into_iter()
            .flat_map(|(_, _, _, malleablized)| malleablized)
            .collect();

        self.malleablized_blocks.append(&mut malleablized_blocks);

        let block_data = blocks
            .into_iter()
            .map(|(blk, sz, cost, _)| (blk, sz, cost))
            .collect();

        self.stacks_node = Some(stacks_node);
        self.sortdb = Some(sortdb);

        block_data
    }

    /// Accept a new Nakamoto tenure via the relayer, and then try to process them.
    pub fn process_nakamoto_tenure(&mut self, blocks: Vec<NakamotoBlock>) {
        debug!("Peer will process {} Nakamoto blocks", blocks.len());

        let mut sortdb = self.sortdb.take().unwrap();
        let mut node = self.stacks_node.take().unwrap();

        let tip = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();

        node.add_nakamoto_tenure_blocks(blocks.clone());
        for block in blocks.iter() {
            let mut sort_handle = sortdb.index_handle(&tip);
            let block_id = block.block_id();
            debug!("Process Nakamoto block {} ({:?}", &block_id, &block.header);
            let accepted = Relayer::process_new_nakamoto_block(
                &self.network.burnchain,
                &sortdb,
                &mut sort_handle,
                &mut node.chainstate,
                &self.network.stacks_tip.block_id(),
                block,
                None,
                NakamotoBlockObtainMethod::Pushed,
            )
            .unwrap();
            if accepted.is_accepted() {
                test_debug!("Accepted Nakamoto block {}", &block_id);
                self.coord.handle_new_nakamoto_stacks_block().unwrap();

                debug!("Begin check Nakamoto block {}", &block.block_id());
                TestPeer::check_processed_nakamoto_block(&mut sortdb, &mut node.chainstate, block);
                debug!("Eegin check Nakamoto block {}", &block.block_id());
            } else {
                test_debug!("Did NOT accept Nakamoto block {}", &block_id);
            }
        }

        self.sortdb = Some(sortdb);
        self.stacks_node = Some(node);
    }

    /// Get the tenure-start block of the parent tenure of `tenure_id_consensus_hash`
    fn get_parent_tenure_start_header(
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip_block_id: &StacksBlockId,
        tenure_id_consensus_hash: &ConsensusHash,
    ) -> StacksHeaderInfo {
        let Ok(Some(tenure_start_header)) = NakamotoChainState::get_tenure_start_block_header(
            &mut chainstate.index_conn(),
            tip_block_id,
            tenure_id_consensus_hash,
        ) else {
            panic!(
                "No tenure-start block header for tenure {}",
                tenure_id_consensus_hash
            );
        };

        let Ok(Some((tenure_start_block, _))) = chainstate
            .nakamoto_blocks_db()
            .get_nakamoto_block(&tenure_start_header.index_block_hash())
        else {
            panic!(
                "Unable to load tenure-start block {}",
                &tenure_start_header.index_block_hash()
            );
        };

        let Some(tenure_start_tx) = tenure_start_block.get_tenure_change_tx_payload() else {
            panic!(
                "Tenure-start block {} has no tenure-change tx",
                &tenure_start_header.index_block_hash()
            );
        };

        let prev_tenure_consensus_hash = &tenure_start_tx.prev_tenure_consensus_hash;

        // get the tenure-start block of the last tenure
        let Ok(Some(prev_tenure_start_header)) = NakamotoChainState::get_tenure_start_block_header(
            &mut chainstate.index_conn(),
            tip_block_id,
            prev_tenure_consensus_hash,
        ) else {
            panic!(
                "No tenure-start block header for tenure {}",
                tenure_id_consensus_hash
            );
        };

        prev_tenure_start_header
    }

    /// Get the block-commit for a tenure. It corresponds to the tenure-start block of
    /// its parent tenure.
    fn get_tenure_block_commit(
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip_block_id: &StacksBlockId,
        tenure_id_consensus_hash: &ConsensusHash,
    ) -> LeaderBlockCommitOp {
        let prev_tenure_start_header = Self::get_parent_tenure_start_header(
            sortdb,
            chainstate,
            tip_block_id,
            tenure_id_consensus_hash,
        );
        let block_hash = BlockHeaderHash(prev_tenure_start_header.index_block_hash().0);
        let Ok(Some(block_commit)) = SortitionDB::get_block_commit_for_stacks_block(
            sortdb.conn(),
            tenure_id_consensus_hash,
            &block_hash,
        ) else {
            panic!(
                "No block-commit for tenure {}: parent tenure-start was {} {:?}",
                tenure_id_consensus_hash,
                &prev_tenure_start_header.index_block_hash(),
                &prev_tenure_start_header
            );
        };
        block_commit
    }

    /// Load up all blocks from the given block back to the last tenure-change block-found tx
    fn load_nakamoto_tenure(
        chainstate: &StacksChainState,
        tip_block_id: &StacksBlockId,
    ) -> Vec<NakamotoBlock> {
        // count up the number of blocks between `tip_block_id` and its ancestral tenure-change
        let mut ancestors = vec![];
        let mut cursor = tip_block_id.clone();
        loop {
            let block = chainstate
                .nakamoto_blocks_db()
                .get_nakamoto_block(&cursor)
                .unwrap()
                .unwrap()
                .0;
            cursor = block.header.parent_block_id.clone();
            let is_tenure_change = block.get_tenure_change_tx_payload().is_some();
            ancestors.push(block);

            if is_tenure_change {
                break;
            }
        }
        ancestors
    }

    /// Check various properties of the chainstate regarding this nakamoto block.
    /// Tests:
    /// * get_coinbase_height
    /// * get_tenure_start_block_header
    /// * get_nakamoto_tenure_start_block_header
    /// * get_highest_block_header_in_tenure
    /// * get_block_vrf_proof
    /// * get_nakamoto_tenure_vrf_proof
    /// * get_parent_vrf_proof
    /// * validate_vrf_seed
    /// * check_block_commit_vrf_seed
    /// * get_nakamoto_parent_tenure_id_consensus_hash
    /// * get_ongoing_tenure
    /// * get_block_found_tenure
    /// * get_nakamoto_tenure_length
    /// * has_processed_nakamoto_tenure
    /// * check_nakamoto_tenure
    /// * check_tenure_continuity
    pub fn check_processed_nakamoto_block(
        sortdb: &mut SortitionDB,
        chainstate: &mut StacksChainState,
        block: &NakamotoBlock,
    ) {
        let Ok(Some(parent_block_header)) =
            NakamotoChainState::get_block_header(chainstate.db(), &block.header.parent_block_id)
        else {
            panic!("No parent block for {:?}", &block);
        };

        // get_coinbase_height
        // Verify that it only increases if the given block has a tenure-change block-found
        // transaction
        let block_coinbase_height = NakamotoChainState::get_coinbase_height(
            &mut chainstate.index_conn(),
            &block.block_id(),
        )
        .unwrap()
        .unwrap();
        let parent_coinbase_height = NakamotoChainState::get_coinbase_height(
            &mut chainstate.index_conn(),
            &block.header.parent_block_id,
        )
        .unwrap()
        .unwrap();

        if let Some(tenure_tx) = block.get_tenure_change_tx_payload() {
            // crosses a tenure block-found boundary
            assert_eq!(parent_coinbase_height + 1, block_coinbase_height);
        } else {
            assert_eq!(parent_coinbase_height, block_coinbase_height);
        }

        // get_tenure_start_block_header
        // Verify that each Nakamoto block's tenure-start header is defined
        let Ok(Some(tenure_start_header)) = NakamotoChainState::get_tenure_start_block_header(
            &mut chainstate.index_conn(),
            &block.block_id(),
            &block.header.consensus_hash,
        ) else {
            panic!("No tenure-start block header for {:?}", &block);
        };

        // get_nakamoto_tenure_start_block_header
        // Verify that if this tenure_start_header is a Nakamoto block, then we can load it.
        // Otherwise, we shouldn't be able to load it
        if tenure_start_header
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            assert_eq!(
                tenure_start_header,
                NakamotoChainState::get_nakamoto_tenure_start_block_header(
                    &mut chainstate.index_conn(),
                    &block.block_id(),
                    &block.header.consensus_hash
                )
                .unwrap()
                .unwrap()
            );
        } else {
            assert!(NakamotoChainState::get_nakamoto_tenure_start_block_header(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &block.header.consensus_hash
            )
            .unwrap()
            .is_none());
        }

        // only blocks with a tenure-change block-found transaction are tenure-start blocks
        if block.get_tenure_change_tx_payload().is_some() {
            assert_eq!(
                &block.header,
                tenure_start_header
                    .anchored_header
                    .as_stacks_nakamoto()
                    .unwrap()
            );
        } else {
            assert_ne!(
                &block.header,
                tenure_start_header
                    .anchored_header
                    .as_stacks_nakamoto()
                    .unwrap()
            );
        }

        // get highest block header in tenure
        if tenure_start_header
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            assert_eq!(
                &block.header,
                NakamotoChainState::get_highest_block_header_in_tenure(
                    &mut chainstate.index_conn(),
                    &block.block_id(),
                    &block.header.consensus_hash
                )
                .unwrap()
                .unwrap()
                .anchored_header
                .as_stacks_nakamoto()
                .unwrap()
            )
        } else {
            assert!(NakamotoChainState::get_highest_block_header_in_tenure(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &block.header.consensus_hash
            )
            .unwrap()
            .is_none())
        }

        // get_block_vrf_proof
        // Verify that a VRF proof is defined for each tenure
        let Ok(Some(vrf_proof)) = NakamotoChainState::get_block_vrf_proof(
            &mut chainstate.index_conn(),
            &block.block_id(),
            &block.header.consensus_hash,
        ) else {
            panic!(
                "No VRF proof defined for tenure {}",
                &block.header.consensus_hash
            );
        };

        // get_nakamoto_tenure_vrf_proof
        // if this is the tenure-start block, then the block VRF proof must be the VRF proof stored in the headers
        // DB fo it.  Otherwise, there must not be a VRF proof for this block.
        if block.get_tenure_change_tx_payload().is_some() {
            let Ok(Some(block_vrf_proof)) = NakamotoChainState::get_nakamoto_tenure_vrf_proof(
                chainstate.db(),
                &block.block_id(),
            ) else {
                panic!(
                    "No VRF proof stored for tenure-start block {}: {:?}",
                    &block.block_id(),
                    &block
                );
            };
            assert_eq!(block_vrf_proof, vrf_proof);
        } else {
            // this block has no VRF proof defined
            assert!(NakamotoChainState::get_nakamoto_tenure_vrf_proof(
                chainstate.db(),
                &block.block_id()
            )
            .unwrap()
            .is_none());
        }

        // get_parent_vrf_proof
        // The parent VRF proof needs to be the same as the VRF proof for the parent tenure
        let parent_tenure_start = Self::get_parent_tenure_start_header(
            sortdb,
            chainstate,
            &block.block_id(),
            &block.header.consensus_hash,
        );
        let tenure_block_commit = Self::get_tenure_block_commit(
            sortdb,
            chainstate,
            &block.block_id(),
            &block.header.consensus_hash,
        );
        let parent_vrf_proof = NakamotoChainState::get_parent_vrf_proof(
            &mut chainstate.index_conn(),
            &block.header.parent_block_id,
            sortdb.conn(),
            &block.header.consensus_hash,
            &tenure_block_commit.txid,
        )
        .unwrap();

        if let Ok(Some(expected_parent_vrf_proof)) =
            NakamotoChainState::get_nakamoto_tenure_vrf_proof(
                chainstate.db(),
                &parent_tenure_start.index_block_hash(),
            )
        {
            assert_eq!(expected_parent_vrf_proof, parent_vrf_proof);
        } else if parent_tenure_start
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            panic!(
                "No VRF proof stored for parent Nakamoto tenure-start block {}: {:?}",
                &parent_tenure_start.index_block_hash(),
                &parent_tenure_start
            );
        };

        // get_nakamoto_parent_tenure_id_consensus_hash
        // The parent tenure start header must have the parent tenure's consensus hash.
        assert_eq!(
            NakamotoChainState::get_nakamoto_parent_tenure_id_consensus_hash(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &block.header.consensus_hash
            )
            .unwrap()
            .unwrap(),
            parent_tenure_start.consensus_hash
        );

        // get_ongoing_tenure
        // changes when we cross _any_ boundary
        if let Some(tenure_tx) = block.get_tenure_tx_payload() {
            if parent_block_header
                .anchored_header
                .as_stacks_nakamoto()
                .is_some()
            {
                // crosses a tenure block-found or extend boundary
                assert_ne!(
                    NakamotoChainState::get_ongoing_tenure(
                        &mut chainstate.index_conn(),
                        &block.block_id()
                    )
                    .unwrap()
                    .unwrap(),
                    NakamotoChainState::get_ongoing_tenure(
                        &mut chainstate.index_conn(),
                        &parent_block_header.index_block_hash()
                    )
                    .unwrap()
                    .unwrap()
                );
            } else {
                assert!(NakamotoChainState::get_ongoing_tenure(
                    &mut chainstate.index_conn(),
                    &parent_block_header.index_block_hash()
                )
                .unwrap()
                .is_none());
            }
        } else if parent_block_header
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            assert_eq!(
                NakamotoChainState::get_ongoing_tenure(
                    &mut chainstate.index_conn(),
                    &block.block_id()
                )
                .unwrap()
                .unwrap(),
                NakamotoChainState::get_ongoing_tenure(
                    &mut chainstate.index_conn(),
                    &parent_block_header.index_block_hash()
                )
                .unwrap()
                .unwrap()
            );
        } else {
            assert!(NakamotoChainState::get_ongoing_tenure(
                &mut chainstate.index_conn(),
                &parent_block_header.index_block_hash()
            )
            .unwrap()
            .is_none());
        }

        // get_block_found_tenure
        // changes when we cross a tenure-change block-found boundary
        if let Some(tenure_tx) = block.get_tenure_change_tx_payload() {
            if parent_block_header
                .anchored_header
                .as_stacks_nakamoto()
                .is_some()
            {
                // crosses a tenure block-found or extend boundary
                assert_ne!(
                    NakamotoChainState::get_block_found_tenure(
                        &mut chainstate.index_conn(),
                        &block.block_id(),
                        &block.header.consensus_hash
                    )
                    .unwrap()
                    .unwrap(),
                    NakamotoChainState::get_block_found_tenure(
                        &mut chainstate.index_conn(),
                        &block.block_id(),
                        &parent_block_header.consensus_hash
                    )
                    .unwrap()
                    .unwrap()
                );
            } else {
                assert!(NakamotoChainState::get_block_found_tenure(
                    &mut chainstate.index_conn(),
                    &block.block_id(),
                    &parent_block_header.consensus_hash
                )
                .unwrap()
                .is_none());
            }
        } else if parent_block_header
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            assert_eq!(
                NakamotoChainState::get_block_found_tenure(
                    &mut chainstate.index_conn(),
                    &block.block_id(),
                    &block.header.consensus_hash
                )
                .unwrap()
                .unwrap(),
                NakamotoChainState::get_block_found_tenure(
                    &mut chainstate.index_conn(),
                    &block.block_id(),
                    &parent_block_header.consensus_hash
                )
                .unwrap()
                .unwrap()
            );
        } else {
            assert!(NakamotoChainState::get_block_found_tenure(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &parent_block_header.consensus_hash
            )
            .unwrap()
            .is_none());
        }

        // get_nakamoto_tenure_length
        // compare the DB to the block's ancestors
        let ancestors = Self::load_nakamoto_tenure(chainstate, &block.block_id());
        assert!(!ancestors.is_empty());
        assert_eq!(
            ancestors.len(),
            NakamotoChainState::get_nakamoto_tenure_length(chainstate.db(), &block.block_id())
                .unwrap() as usize
        );

        // has_processed_nakamoto_tenure
        // this tenure is unprocessed as of this block.
        // the parent tenure is already processed.
        assert!(!NakamotoChainState::has_processed_nakamoto_tenure(
            &mut chainstate.index_conn(),
            &block.block_id(),
            &block.header.consensus_hash
        )
        .unwrap());
        if parent_tenure_start
            .anchored_header
            .as_stacks_nakamoto()
            .is_some()
        {
            // MARF stores parent tenure info for Nakamoto
            assert!(NakamotoChainState::has_processed_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &parent_tenure_start.consensus_hash
            )
            .unwrap());
        } else {
            // MARF does NOT store parent tenure info for epoch2
            assert!(!NakamotoChainState::has_processed_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &block.block_id(),
                &parent_tenure_start.consensus_hash
            )
            .unwrap());
        }

        // validate_vrf_seed
        // Check against the tenure block-commit
        assert!(block
            .validate_vrf_seed(
                sortdb.conn(),
                &mut chainstate.index_conn(),
                &tenure_block_commit
            )
            .is_ok());
        let mut bad_commit = tenure_block_commit.clone();
        bad_commit.new_seed = VRFSeed([0xff; 32]);
        assert!(block
            .validate_vrf_seed(sortdb.conn(), &mut chainstate.index_conn(), &bad_commit)
            .is_err());

        // check_block_commit_vrf_seed
        assert!(NakamotoChainState::check_block_commit_vrf_seed(
            &mut chainstate.index_conn(),
            sortdb.conn(),
            block
        )
        .is_ok());

        if let Some(tenure_tx) = block.get_tenure_tx_payload() {
            if let Some(expected_tenure) = NakamotoChainState::get_ongoing_tenure(
                &mut chainstate.index_conn(),
                &block.header.parent_block_id,
            )
            .unwrap()
            {
                // this block connects to its parent's tenure
                assert_eq!(
                    expected_tenure,
                    NakamotoChainState::check_nakamoto_tenure(
                        &mut chainstate.index_conn(),
                        &mut sortdb.index_handle_at_tip(),
                        &block.header,
                        tenure_tx
                    )
                    .unwrap()
                    .unwrap()
                );
            } else {
                // this block connects to the last epoch 2.x tenure
                assert_eq!(
                    NakamotoChainState::check_first_nakamoto_tenure_change(
                        chainstate.db(),
                        tenure_tx
                    )
                    .unwrap()
                    .unwrap(),
                    NakamotoChainState::check_nakamoto_tenure(
                        &mut chainstate.index_conn(),
                        &mut sortdb.index_handle_at_tip(),
                        &block.header,
                        tenure_tx
                    )
                    .unwrap()
                    .unwrap()
                );
            }

            if tenure_tx.cause == TenureChangeCause::BlockFound {
                // block-founds are always in new tenures
                assert!(!NakamotoChainState::check_tenure_continuity(
                    &mut chainstate.index_conn(),
                    &parent_block_header.consensus_hash,
                    &block.header
                )
                .unwrap());
            } else {
                // extends are in the same tenure as their parents
                assert!(NakamotoChainState::check_tenure_continuity(
                    &mut chainstate.index_conn(),
                    &parent_block_header.consensus_hash,
                    &block.header
                )
                .unwrap());
            }

            // get a valid but too-old consensus hash
            let prev_tenure_sn = SortitionDB::get_block_snapshot_consensus(
                sortdb.conn(),
                &tenure_tx.prev_tenure_consensus_hash,
            )
            .unwrap()
            .unwrap();
            let invalid_tenure_sn =
                SortitionDB::get_block_snapshot(sortdb.conn(), &prev_tenure_sn.parent_sortition_id)
                    .unwrap()
                    .unwrap();

            // this fails if we change any tenure-identifying fields
            let mut bad_tenure_tx = tenure_tx.clone();
            bad_tenure_tx.tenure_consensus_hash = invalid_tenure_sn.consensus_hash.clone();
            assert!(NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sortdb.index_handle_at_tip(),
                &block.header,
                &bad_tenure_tx
            )
            .unwrap()
            .is_none());

            let mut bad_tenure_tx = tenure_tx.clone();
            bad_tenure_tx.prev_tenure_consensus_hash = invalid_tenure_sn.consensus_hash.clone();
            assert!(NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sortdb.index_handle_at_tip(),
                &block.header,
                &bad_tenure_tx
            )
            .unwrap()
            .is_none());

            let mut bad_tenure_tx = tenure_tx.clone();
            bad_tenure_tx.burn_view_consensus_hash = invalid_tenure_sn.consensus_hash.clone();
            assert!(NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sortdb.index_handle_at_tip(),
                &block.header,
                &bad_tenure_tx
            )
            .unwrap()
            .is_none());

            let mut bad_tenure_tx = tenure_tx.clone();
            bad_tenure_tx.previous_tenure_end =
                StacksBlockId(prev_tenure_sn.winning_stacks_block_hash.clone().0);
            assert!(NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sortdb.index_handle_at_tip(),
                &block.header,
                &bad_tenure_tx
            )
            .unwrap()
            .is_none());

            let mut bad_tenure_tx = tenure_tx.clone();
            bad_tenure_tx.previous_tenure_blocks = u32::MAX;
            assert!(NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sortdb.index_handle_at_tip(),
                &block.header,
                &bad_tenure_tx
            )
            .unwrap()
            .is_none());
        } else {
            assert!(NakamotoChainState::check_tenure_continuity(
                &mut chainstate.index_conn(),
                &parent_block_header.consensus_hash,
                &block.header
            )
            .unwrap());
        }

        // validate_shadow_parent_burnchain
        // should always succeed
        NakamotoChainState::validate_shadow_parent_burnchain(
            chainstate.nakamoto_blocks_db(),
            &sortdb.index_handle_at_tip(),
            block,
            &tenure_block_commit,
        )
        .unwrap();

        if parent_block_header
            .anchored_header
            .as_stacks_nakamoto()
            .map(|hdr| hdr.is_shadow_block())
            .unwrap_or(false)
        {
            // test error cases
            let mut bad_tenure_block_commit_vtxindex = tenure_block_commit.clone();
            bad_tenure_block_commit_vtxindex.parent_vtxindex = 1;

            let mut bad_tenure_block_commit_block_ptr = tenure_block_commit.clone();
            bad_tenure_block_commit_block_ptr.parent_block_ptr += 1;

            let mut bad_block_no_parent = block.clone();
            bad_block_no_parent.header.parent_block_id = StacksBlockId([0x11; 32]);

            // not a problem if there's no (nakamoto) parent, since the parent can be a
            // (non-shadow) epoch2 block not present in the staging chainstate
            NakamotoChainState::validate_shadow_parent_burnchain(
                chainstate.nakamoto_blocks_db(),
                &sortdb.index_handle_at_tip(),
                &bad_block_no_parent,
                &tenure_block_commit,
            )
            .unwrap();

            // should fail because vtxindex must be 0
            let ChainstateError::InvalidStacksBlock(_) =
                NakamotoChainState::validate_shadow_parent_burnchain(
                    chainstate.nakamoto_blocks_db(),
                    &sortdb.index_handle_at_tip(),
                    block,
                    &bad_tenure_block_commit_vtxindex,
                )
                .unwrap_err()
            else {
                panic!("validate_shadow_parent_burnchain did not fail as expected");
            };

            // should fail because it doesn't point to shadow tenure
            let ChainstateError::InvalidStacksBlock(_) =
                NakamotoChainState::validate_shadow_parent_burnchain(
                    chainstate.nakamoto_blocks_db(),
                    &sortdb.index_handle_at_tip(),
                    block,
                    &bad_tenure_block_commit_block_ptr,
                )
                .unwrap_err()
            else {
                panic!("validate_shadow_parent_burnchain did not fail as expected");
            };
        }

        if block.is_shadow_block() {
            // block is stored
            assert!(chainstate
                .nakamoto_blocks_db()
                .has_shadow_nakamoto_block_with_index_hash(&block.block_id())
                .unwrap());

            // block is in a shadow tenure
            assert!(chainstate
                .nakamoto_blocks_db()
                .is_shadow_tenure(&block.header.consensus_hash)
                .unwrap());

            // shadow tenure has a start block
            assert!(chainstate
                .nakamoto_blocks_db()
                .get_shadow_tenure_start_block(&block.header.consensus_hash)
                .unwrap()
                .is_some());

            // succeeds without burn
            NakamotoChainState::validate_shadow_nakamoto_block_burnchain(
                chainstate.nakamoto_blocks_db(),
                &sortdb.index_handle_at_tip(),
                None,
                block,
                false,
                0x80000000,
            )
            .unwrap();

            // succeeds with expected burn
            NakamotoChainState::validate_shadow_nakamoto_block_burnchain(
                chainstate.nakamoto_blocks_db(),
                &sortdb.index_handle_at_tip(),
                Some(block.header.burn_spent),
                block,
                false,
                0x80000000,
            )
            .unwrap();

            // fails with invalid burn
            let ChainstateError::InvalidStacksBlock(_) =
                NakamotoChainState::validate_shadow_nakamoto_block_burnchain(
                    chainstate.nakamoto_blocks_db(),
                    &sortdb.index_handle_at_tip(),
                    Some(block.header.burn_spent + 1),
                    block,
                    false,
                    0x80000000,
                )
                .unwrap_err()
            else {
                panic!("validate_shadow_nakamoto_block_burnchain succeeded when it shouldn't have");
            };

            // block must be stored alreay
            let mut bad_block = block.clone();
            bad_block.header.version += 1;

            // fails because block_id() isn't present
            let ChainstateError::InvalidStacksBlock(_) =
                NakamotoChainState::validate_shadow_nakamoto_block_burnchain(
                    chainstate.nakamoto_blocks_db(),
                    &sortdb.index_handle_at_tip(),
                    None,
                    &bad_block,
                    false,
                    0x80000000,
                )
                .unwrap_err()
            else {
                panic!("validate_shadow_nakamoto_block_burnchain succeeded when it shouldn't have");
            };

            // VRF proof must be present
            assert!(NakamotoChainState::get_shadow_vrf_proof(
                &mut chainstate.index_conn(),
                &block.block_id()
            )
            .unwrap()
            .is_some());
        } else {
            // not a shadow block
            assert!(!chainstate
                .nakamoto_blocks_db()
                .has_shadow_nakamoto_block_with_index_hash(&block.block_id())
                .unwrap());
            assert!(!chainstate
                .nakamoto_blocks_db()
                .is_shadow_tenure(&block.header.consensus_hash)
                .unwrap());
            assert!(chainstate
                .nakamoto_blocks_db()
                .get_shadow_tenure_start_block(&block.header.consensus_hash)
                .unwrap()
                .is_none());
            assert!(NakamotoChainState::get_shadow_vrf_proof(
                &mut chainstate.index_conn(),
                &block.block_id()
            )
            .unwrap()
            .is_none());
        }
    }

    /// Add a shadow tenure on a given tip.
    /// * Advance the burnchain and create an empty sortition (so we have a new consensus hash)
    /// * Generate a shadow block for the empty sortition
    /// * Store the shadow block to the staging DB
    /// * Process it
    ///
    /// Tests:
    /// * NakamotoBlockHeader::get_shadow_signer_weight()
    pub fn make_shadow_tenure(&mut self, tip: Option<StacksBlockId>) -> NakamotoBlock {
        let naka_tip_id = tip.unwrap_or(self.network.stacks_tip.block_id());
        let (_, _, tenure_id_consensus_hash) = self.next_burnchain_block(vec![]);

        test_debug!(
            "\n\nMake shadow tenure for tenure {} off of tip {}\n\n",
            &tenure_id_consensus_hash,
            &naka_tip_id
        );

        let mut stacks_node = self.stacks_node.take().unwrap();
        let sortdb = self.sortdb.take().unwrap();

        let shadow_block = NakamotoBlockBuilder::make_shadow_tenure(
            &mut stacks_node.chainstate,
            &sortdb,
            naka_tip_id,
            tenure_id_consensus_hash,
            vec![],
        )
        .unwrap();

        // Get the reward set
        let sort_tip_sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        let reward_set = load_nakamoto_reward_set(
            self.miner
                .burnchain
                .block_height_to_reward_cycle(sort_tip_sn.block_height)
                .expect("FATAL: no reward cycle for sortition"),
            &sort_tip_sn.sortition_id,
            &self.miner.burnchain,
            &mut stacks_node.chainstate,
            &shadow_block.header.parent_block_id,
            &sortdb,
            &OnChainRewardSetProvider::new(),
        )
        .expect("Failed to load reward set")
        .expect("Expected a reward set")
        .0
        .known_selected_anchor_block_owned()
        .expect("Unknown reward set");

        // check signer weight
        let mut max_signing_weight = 0;
        for signer in reward_set.signers.as_ref().unwrap().iter() {
            max_signing_weight += signer.weight;
        }

        assert_eq!(
            shadow_block
                .header
                .get_shadow_signer_weight(&reward_set)
                .unwrap(),
            max_signing_weight
        );

        // put it into Stacks staging DB
        let tx = stacks_node.chainstate.staging_db_tx_begin().unwrap();
        tx.add_shadow_block(&shadow_block).unwrap();

        // inserts of the same block are idempotent
        tx.add_shadow_block(&shadow_block).unwrap();

        tx.commit().unwrap();

        let rollback_tx = stacks_node.chainstate.staging_db_tx_begin().unwrap();

        if let Some(normal_tenure) = rollback_tx.conn().get_any_normal_tenure().unwrap() {
            // can't insert into a non-shadow tenure
            let mut bad_shadow_block_tenure = shadow_block.clone();
            bad_shadow_block_tenure.header.consensus_hash = normal_tenure;

            let ChainstateError::InvalidStacksBlock(_) = rollback_tx
                .add_shadow_block(&bad_shadow_block_tenure)
                .unwrap_err()
            else {
                panic!("add_shadow_block succeeded when it should have failed");
            };
        }

        // can't insert into the same height twice with different blocks
        let mut bad_shadow_block_height = shadow_block.clone();
        bad_shadow_block_height.header.version += 1;
        let ChainstateError::InvalidStacksBlock(_) = rollback_tx
            .add_shadow_block(&bad_shadow_block_height)
            .unwrap_err()
        else {
            panic!("add_shadow_block succeeded when it should have failed");
        };

        drop(rollback_tx);

        self.stacks_node = Some(stacks_node);
        self.sortdb = Some(sortdb);

        // process it
        self.coord.handle_new_nakamoto_stacks_block().unwrap();

        // verify that it processed
        self.refresh_burnchain_view();
        assert_eq!(self.network.stacks_tip.block_id(), shadow_block.block_id());

        shadow_block
    }
}
