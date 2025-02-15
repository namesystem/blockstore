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
use std::sync::Mutex;

use clarity::consts::CHAIN_ID_TESTNET;
use clarity::vm::clarity::ClarityConnection;
use clarity::vm::costs::ExecutionCost;
use clarity::vm::database::clarity_db::NullBurnStateDB;
use clarity::vm::types::{PrincipalData, QualifiedContractIdentifier};
use clarity::vm::{ClarityVersion, Value};
use rand::prelude::SliceRandom;
use rand::{thread_rng, Rng, RngCore};
use stacks_common::address::{AddressHashMode, C32_ADDRESS_VERSION_TESTNET_SINGLESIG};
use stacks_common::bitvec::BitVec;
use stacks_common::consts::{
    FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH, SIGNER_SLOTS_PER_USER,
};
use stacks_common::types::chainstate::{
    BurnchainHeaderHash, StacksAddress, StacksBlockId, StacksPrivateKey, StacksPublicKey,
};
use stacks_common::types::{Address, StacksEpoch, StacksEpochId, StacksPublicKeyBuffer};
use stacks_common::util::hash::Hash160;
use stacks_common::util::secp256k1::Secp256k1PrivateKey;
use stacks_common::util::vrf::VRFProof;

use crate::burnchains::tests::TestMiner;
use crate::burnchains::{PoxConstants, Txid};
use crate::chainstate::burn::db::sortdb::{SortitionDB, SortitionHandle};
use crate::chainstate::burn::operations::{
    BlockstackOperationType, DelegateStxOp, LeaderBlockCommitOp, StackStxOp, TransferStxOp,
    VoteForAggregateKeyOp,
};
use crate::chainstate::coordinator::tests::{p2pkh_from, pox_addr_from};
use crate::chainstate::nakamoto::coordinator::load_nakamoto_reward_set;
use crate::chainstate::nakamoto::fault_injection::*;
use crate::chainstate::nakamoto::miner::NakamotoBlockBuilder;
use crate::chainstate::nakamoto::signer_set::NakamotoSigners;
use crate::chainstate::nakamoto::test_signers::TestSigners;
use crate::chainstate::nakamoto::tests::get_account;
use crate::chainstate::nakamoto::tests::node::TestStacker;
use crate::chainstate::nakamoto::{
    NakamotoBlock, NakamotoBlockObtainMethod, NakamotoChainState, NakamotoStagingBlocksConnRef,
};
use crate::chainstate::stacks::address::PoxAddress;
use crate::chainstate::stacks::boot::pox_4_tests::{get_stacking_minimum, get_tip};
use crate::chainstate::stacks::boot::signers_tests::{readonly_call, readonly_call_with_sortdb};
use crate::chainstate::stacks::boot::test::{
    key_to_stacks_addr, make_pox_4_lockup, make_signer_key_signature, with_sortdb,
};
use crate::chainstate::stacks::boot::{MINERS_NAME, SIGNERS_NAME};
use crate::chainstate::stacks::db::{MinerPaymentTxFees, StacksAccount, StacksChainState};
use crate::chainstate::stacks::events::TransactionOrigin;
use crate::chainstate::stacks::{
    CoinbasePayload, Error as ChainstateError, StacksTransaction, StacksTransactionSigner,
    TenureChangeCause, TokenTransferMemo, TransactionAnchorMode, TransactionAuth,
    TransactionPayload, TransactionSmartContract, TransactionVersion,
};
use crate::clarity::vm::types::StacksAddressExtensions;
use crate::core::StacksEpochExtension;
use crate::net::relay::{BlockAcceptResponse, Relayer};
use crate::net::stackerdb::StackerDBConfig;
use crate::net::test::{TestEventObserver, TestPeer, TestPeerConfig};
use crate::net::tests::NakamotoBootPlan;
use crate::stacks_common::codec::StacksMessageCodec;
use crate::util_lib::boot::boot_code_id;
use crate::util_lib::db::{query_rows, u64_to_sql};
use crate::util_lib::signed_structured_data::pox4::Pox4SignatureTopic;
use crate::util_lib::strings::StacksString;

impl NakamotoStagingBlocksConnRef<'_> {
    pub fn get_blocks_at_height(&self, height: u64) -> Vec<NakamotoBlock> {
        let sql = "SELECT data FROM nakamoto_staging_blocks WHERE height = ?1";
        let args = rusqlite::params![&u64_to_sql(height).unwrap()];
        let serialized_blocks: Vec<Vec<u8>> = query_rows(self, sql, args).unwrap();
        serialized_blocks
            .into_iter()
            .map(|blk_bytes| NakamotoBlock::consensus_deserialize(&mut &blk_bytes[..]).unwrap())
            .collect()
    }
}

/// Bring a TestPeer into the Nakamoto Epoch
fn advance_to_nakamoto(
    peer: &mut TestPeer,
    test_signers: &mut TestSigners,
    test_stackers: &[TestStacker],
) {
    let mut peer_nonce = 0;
    let private_key = peer.config.private_key.clone();
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();
    let default_pox_addr =
        PoxAddress::from_legacy(AddressHashMode::SerializeP2PKH, addr.bytes().clone());

    for sortition_height in 0..11 {
        // stack to pox-3 in cycle 7
        let txs = if sortition_height == 6 {
            // Make all the test Stackers stack
            test_stackers
                .iter()
                .map(|test_stacker| {
                    let pox_addr = test_stacker
                        .pox_addr
                        .clone()
                        .unwrap_or(default_pox_addr.clone());
                    let max_amount = test_stacker.max_amount.clone().unwrap_or(u128::MAX);

                    let signature = make_signer_key_signature(
                        &pox_addr,
                        &test_stacker.signer_private_key,
                        6,
                        &Pox4SignatureTopic::StackStx,
                        12_u128,
                        max_amount,
                        1,
                    );
                    let signing_key =
                        StacksPublicKey::from_private(&test_stacker.signer_private_key);

                    make_pox_4_lockup(
                        &test_stacker.stacker_private_key,
                        0,
                        test_stacker.amount,
                        &pox_addr,
                        12,
                        &signing_key,
                        34,
                        Some(signature),
                        max_amount,
                        1,
                    )
                })
                .collect()
        } else {
            vec![]
        };

        peer.tenure_with_txs(&txs, &mut peer_nonce);
    }
    // peer is at the start of cycle 8
}

/// Make a peer and transition it into the Nakamoto epoch.
/// The node needs to be stacking.
/// otherwise, Nakamoto can't activate.
pub fn boot_nakamoto<'a>(
    test_name: &str,
    mut initial_balances: Vec<(PrincipalData, u64)>,
    test_signers: &mut TestSigners,
    test_stackers: &[TestStacker],
    observer: Option<&'a TestEventObserver>,
) -> TestPeer<'a> {
    let mut peer_config = TestPeerConfig::new(test_name, 0, 0);
    let private_key = peer_config.private_key.clone();
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    // reward cycles are 5 blocks long
    // first 25 blocks are boot-up
    // reward cycle 6 instantiates pox-3
    // we stack in reward cycle 7 so pox-3 is evaluated to find reward set participation
    peer_config
        .stacker_dbs
        .push(boot_code_id(MINERS_NAME, false));
    peer_config.epochs = Some(StacksEpoch::unit_test_3_0_only(37));
    peer_config.initial_balances = vec![(addr.to_account_principal(), 1_000_000_000_000_000_000)];

    // Create some balances for test Stackers
    let mut stacker_balances = test_stackers
        .iter()
        .map(|test_stacker| {
            (
                PrincipalData::from(key_to_stacks_addr(&test_stacker.stacker_private_key)),
                u64::try_from(test_stacker.amount + 10000).expect("Stacking amount too large"),
            )
        })
        .collect();

    // Create some balances for test Signers
    let mut signer_balances = test_stackers
        .iter()
        .map(|stacker| {
            (
                PrincipalData::from(p2pkh_from(&stacker.signer_private_key)),
                1000,
            )
        })
        .collect();

    peer_config.initial_balances.append(&mut stacker_balances);
    peer_config.initial_balances.append(&mut signer_balances);
    peer_config.initial_balances.append(&mut initial_balances);
    peer_config.burnchain.pox_constants.v2_unlock_height = 21;
    peer_config.burnchain.pox_constants.pox_3_activation_height = 26;
    peer_config.burnchain.pox_constants.v3_unlock_height = 27;
    peer_config.burnchain.pox_constants.pox_4_activation_height = 31;
    peer_config.test_stackers = Some(test_stackers.to_vec());
    peer_config.test_signers = Some(test_signers.clone());
    let mut peer = TestPeer::new_with_observer(peer_config, observer);

    advance_to_nakamoto(&mut peer, test_signers, test_stackers);

    peer
}

/// Make a replay peer, used for replaying the blockchain
pub fn make_replay_peer<'a>(peer: &mut TestPeer<'a>) -> TestPeer<'a> {
    let mut replay_config = peer.config.clone();
    replay_config.test_name = format!("{}.replay", &peer.config.test_name);
    replay_config.server_port = 0;
    replay_config.http_port = 0;
    replay_config.test_stackers = peer.config.test_stackers.clone();

    let test_stackers = replay_config.test_stackers.clone().unwrap_or_default();
    let mut test_signers = replay_config.test_signers.clone().unwrap();
    let mut replay_peer = TestPeer::new(replay_config);
    let observer = TestEventObserver::new();
    advance_to_nakamoto(
        &mut replay_peer,
        &mut test_signers,
        test_stackers.as_slice(),
    );

    // sanity check
    let replay_tip = {
        let sort_db = replay_peer.sortdb.as_ref().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        tip
    };
    let tip = {
        let sort_db = peer.sortdb.as_ref().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let sort_ic = sort_db.index_conn();
        let ancestor_tip = SortitionDB::get_ancestor_snapshot(
            &sort_ic,
            replay_tip.block_height,
            &tip.sortition_id,
        )
        .unwrap()
        .unwrap();
        ancestor_tip
    };

    assert_eq!(tip, replay_tip);
    replay_peer
}

/// Make a token-transfer from a private key
pub fn make_token_transfer(
    chainstate: &mut StacksChainState,
    sortdb: &SortitionDB,
    private_key: &StacksPrivateKey,
    nonce: u64,
    amt: u64,
    fee: u64,
    recipient_addr: &StacksAddress,
) -> StacksTransaction {
    let mut stx_transfer = StacksTransaction::new(
        TransactionVersion::Testnet,
        TransactionAuth::from_p2pkh(private_key).unwrap(),
        TransactionPayload::TokenTransfer(
            recipient_addr.clone().to_account_principal(),
            amt,
            TokenTransferMemo([0x00; 34]),
        ),
    );
    stx_transfer.chain_id = chainstate.chain_id;
    stx_transfer.anchor_mode = TransactionAnchorMode::OnChainOnly;
    stx_transfer.set_tx_fee(fee);
    stx_transfer.auth.set_origin_nonce(nonce);

    let mut tx_signer = StacksTransactionSigner::new(&stx_transfer);
    tx_signer.sign_origin(private_key).unwrap();
    let stx_transfer_signed = tx_signer.get_tx().unwrap();

    stx_transfer_signed
}

/// Make contract publish
pub fn make_contract(
    chainstate: &mut StacksChainState,
    name: &str,
    code: &str,
    private_key: &StacksPrivateKey,
    version: ClarityVersion,
    nonce: u64,
    fee: u64,
) -> StacksTransaction {
    let mut stx_tx = StacksTransaction::new(
        TransactionVersion::Testnet,
        TransactionAuth::from_p2pkh(private_key).unwrap(),
        TransactionPayload::SmartContract(
            TransactionSmartContract {
                name: name.into(),
                code_body: StacksString::from_str(code).unwrap(),
            },
            Some(version),
        ),
    );
    stx_tx.chain_id = chainstate.chain_id;
    stx_tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
    stx_tx.set_tx_fee(fee);
    stx_tx.auth.set_origin_nonce(nonce);

    let mut tx_signer = StacksTransactionSigner::new(&stx_tx);
    tx_signer.sign_origin(private_key).unwrap();
    tx_signer.get_tx().unwrap()
}

/// Given the blocks and block-commits for a reward cycle, replay the sortitions on the given
/// TestPeer, always processing the first block of the reward cycle before processing all
/// subsequent blocks in random order.
fn replay_reward_cycle(
    peer: &mut TestPeer,
    burn_ops: &[Vec<BlockstackOperationType>],
    stacks_blocks: &[NakamotoBlock],
) {
    eprintln!("\n\n=============================================\nBegin replay\n==============================================\n");
    let reward_cycle_length = peer.config.burnchain.pox_constants.reward_cycle_length as usize;
    let reward_cycle_indices: Vec<usize> = (0..stacks_blocks.len())
        .step_by(reward_cycle_length)
        .collect();

    for burn_ops in burn_ops.iter() {
        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
    }

    let sortdb = peer.sortdb.take().unwrap();
    let mut node = peer.stacks_node.take().unwrap();

    let sort_tip = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
    let mut sort_handle = sortdb.index_handle(&sort_tip);
    let nakamoto_tip = sort_handle.get_nakamoto_tip_block_id().unwrap().unwrap();

    let mut blocks_to_process = stacks_blocks.to_vec();
    blocks_to_process.shuffle(&mut thread_rng());
    while let Some(block) = blocks_to_process.pop() {
        let block_id = block.block_id();
        info!("Process Nakamoto block {} ({:?}", &block_id, &block.header);

        let accepted = Relayer::process_new_nakamoto_block(
            &peer.config.burnchain,
            &sortdb,
            &mut sort_handle,
            &mut node.chainstate,
            &nakamoto_tip,
            &block,
            None,
            NakamotoBlockObtainMethod::Pushed,
        )
        .unwrap_or(BlockAcceptResponse::Rejected(
            "encountered error on acceptance".into(),
        ));
        if accepted.is_accepted() {
            test_debug!("Accepted Nakamoto block {block_id}");
            peer.coord.handle_new_nakamoto_stacks_block().unwrap();
        } else {
            test_debug!("Did NOT accept Nakamoto block {block_id}");
            blocks_to_process.push(block);
            blocks_to_process.shuffle(&mut thread_rng());
        }
    }

    peer.sortdb = Some(sortdb);
    peer.stacks_node = Some(node);

    peer.check_nakamoto_migration();
}

/// Mine a single Nakamoto tenure with a single Nakamoto block
#[test]
fn test_simple_nakamoto_coordinator_bootup() {
    let (mut test_signers, test_stackers) = TestStacker::common_signing_set();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let (burn_ops, mut tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
    let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops);
    let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    tenure_change.tenure_consensus_hash = consensus_hash.clone();
    tenure_change.burn_view_consensus_hash = consensus_hash.clone();
    let tenure_change_tx = peer.miner.make_nakamoto_tenure_change(tenure_change);
    let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

    let blocks_and_sizes = peer.make_nakamoto_tenure(
        tenure_change_tx,
        coinbase_tx,
        &mut test_signers,
        |_miner, _chainstate, _sort_dbconn, _blocks| vec![],
    );
    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
    let sort_db = peer.sortdb.as_mut().unwrap();
    let tip = NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
        .unwrap()
        .unwrap();
    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        12
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    peer.check_nakamoto_migration();
}

/// Mine a single Nakamoto tenure with 10 Nakamoto blocks
#[test]
fn test_simple_nakamoto_coordinator_1_tenure_10_blocks() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    let (mut test_signers, test_stackers) = TestStacker::common_signing_set();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let (burn_ops, mut tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
    let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
    let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    tenure_change.tenure_consensus_hash = consensus_hash.clone();
    tenure_change.burn_view_consensus_hash = consensus_hash.clone();

    let tenure_change_tx = peer.miner.make_nakamoto_tenure_change(tenure_change);
    let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

    // do a stx transfer in each block to a given recipient
    let recipient_addr =
        StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();

    let blocks_and_sizes = peer.make_nakamoto_tenure(
        tenure_change_tx,
        coinbase_tx,
        &mut test_signers,
        |_miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        21
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    // replay the blocks and sortitions in random order, and verify that we still reach the chain
    // tip
    let mut replay_peer = make_replay_peer(&mut peer);
    replay_reward_cycle(&mut replay_peer, &[burn_ops], &blocks);

    let tip = {
        let chainstate = &mut replay_peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = replay_peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        21
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    peer.check_nakamoto_migration();
}

impl TestPeer<'_> {
    pub fn mine_single_block_tenure<F, G>(
        &mut self,
        sender_key: &StacksPrivateKey,
        tenure_change_tx: &StacksTransaction,
        coinbase_tx: &StacksTransaction,
        miner_setup: F,
        after_block: G,
    ) -> Result<NakamotoBlock, ChainstateError>
    where
        F: FnMut(&mut NakamotoBlockBuilder),
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        let nakamoto_tip = {
            let chainstate = &mut self.stacks_node.as_mut().unwrap().chainstate;
            let sort_db = self.sortdb.as_mut().unwrap();
            NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
                .unwrap()
                .unwrap()
        };
        self.mine_single_block_tenure_at_tip(
            &nakamoto_tip.index_block_hash(),
            sender_key,
            tenure_change_tx,
            coinbase_tx,
            miner_setup,
            after_block,
        )
    }

    pub fn mine_single_block_tenure_at_tip<F, G>(
        &mut self,
        nakamoto_tip: &StacksBlockId,
        sender_key: &StacksPrivateKey,
        tenure_change_tx: &StacksTransaction,
        coinbase_tx: &StacksTransaction,
        miner_setup: F,
        after_block: G,
    ) -> Result<NakamotoBlock, ChainstateError>
    where
        F: FnMut(&mut NakamotoBlockBuilder),
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        let sender_addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(sender_key));
        let mut test_signers = self.config.test_signers.clone().unwrap();
        let recipient_addr =
            StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();

        let sender_acct = self.get_account(nakamoto_tip, &sender_addr.to_account_principal());

        // do a stx transfer in each block to a given recipient
        let mut blocks_and_sizes = self.make_nakamoto_tenure_and(
            tenure_change_tx.clone(),
            coinbase_tx.clone(),
            &mut test_signers,
            miner_setup,
            |_miner, chainstate, sortdb, blocks_so_far| {
                if blocks_so_far.is_empty() {
                    let stx_transfer = make_token_transfer(
                        chainstate,
                        sortdb,
                        sender_key,
                        sender_acct.nonce,
                        200,
                        1,
                        &recipient_addr,
                    );

                    vec![stx_transfer]
                } else {
                    vec![]
                }
            },
            after_block,
        )?;
        assert_eq!(blocks_and_sizes.len(), 1);
        let block = blocks_and_sizes.pop().unwrap().0;
        Ok(block)
    }

    pub fn mine_tenure<F>(&mut self, block_builder: F) -> Vec<(NakamotoBlock, u64, ExecutionCost)>
    where
        F: FnMut(
            &mut TestMiner,
            &mut StacksChainState,
            &SortitionDB,
            &[(NakamotoBlock, u64, ExecutionCost)],
        ) -> Vec<StacksTransaction>,
    {
        let (burn_ops, mut tenure_change, miner_key) =
            self.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
        let (burn_height, _, consensus_hash) = self.next_burnchain_block(burn_ops);
        let pox_constants = self.sortdb().pox_constants.clone();
        let first_burn_height = self.sortdb().first_block_height;
        let mut test_signers = self.config.test_signers.clone().unwrap();

        info!(
            "Burnchain block produced: {burn_height}, in_prepare_phase?: {}, first_reward_block?: {}",
            pox_constants.is_in_prepare_phase(first_burn_height, burn_height),
            pox_constants.is_naka_signing_cycle_start(first_burn_height, burn_height)
        );
        let vrf_proof = self.make_nakamoto_vrf_proof(miner_key);

        tenure_change.tenure_consensus_hash = consensus_hash.clone();
        tenure_change.burn_view_consensus_hash = consensus_hash.clone();

        let nakamoto_tip =
            if let Some(nakamoto_parent_tenure) = self.nakamoto_parent_tenure_opt.as_ref() {
                nakamoto_parent_tenure.last().as_ref().unwrap().block_id()
            } else {
                let tip = {
                    let chainstate = &mut self.stacks_node.as_mut().unwrap().chainstate;
                    let sort_db = self.sortdb.as_mut().unwrap();
                    NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
                        .unwrap()
                        .unwrap()
                };
                tip.index_block_hash()
            };

        let miner_addr = self.miner.origin_address().unwrap();
        let miner_acct = self.get_account(&nakamoto_tip, &miner_addr.to_account_principal());

        let tenure_change_tx = self
            .miner
            .make_nakamoto_tenure_change_with_nonce(tenure_change, miner_acct.nonce);

        let coinbase_tx =
            self.miner
                .make_nakamoto_coinbase_with_nonce(None, vrf_proof, miner_acct.nonce + 1);

        self.make_nakamoto_tenure_and(
            tenure_change_tx,
            coinbase_tx,
            &mut test_signers,
            |_| {},
            block_builder,
            |_| true,
        )
        .unwrap()
    }

    pub fn single_block_tenure<S, F, G>(
        &mut self,
        sender_key: &StacksPrivateKey,
        miner_setup: S,
        after_burn_ops: F,
        after_block: G,
    ) -> (NakamotoBlock, u64, StacksTransaction, StacksTransaction)
    where
        S: FnMut(&mut NakamotoBlockBuilder),
        F: FnMut(&mut Vec<BlockstackOperationType>),
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        self.single_block_tenure_fallible(sender_key, miner_setup, after_burn_ops, after_block)
            .unwrap()
    }

    /// Produce a single-block tenure, containing a stx-transfer sent from `sender_key`.
    ///
    /// * `after_burn_ops` is called right after `self.begin_nakamoto_tenure` to modify any burn ops
    /// for this tenure
    ///
    /// * `miner_setup` is called right after the Nakamoto block builder is constructed, but before
    /// any txs are mined
    ///
    /// * `after_block` is called right after the block is assembled, but before it is signed.
    pub fn single_block_tenure_fallible<S, F, G>(
        &mut self,
        sender_key: &StacksPrivateKey,
        miner_setup: S,
        mut after_burn_ops: F,
        after_block: G,
    ) -> Result<(NakamotoBlock, u64, StacksTransaction, StacksTransaction), ChainstateError>
    where
        S: FnMut(&mut NakamotoBlockBuilder),
        F: FnMut(&mut Vec<BlockstackOperationType>),
        G: FnMut(&mut NakamotoBlock) -> bool,
    {
        let (mut burn_ops, mut tenure_change, miner_key) =
            self.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
        after_burn_ops(&mut burn_ops);
        let (burn_height, _, consensus_hash) = self.next_burnchain_block(burn_ops.clone());
        let pox_constants = self.sortdb().pox_constants.clone();
        let first_burn_height = self.sortdb().first_block_height;

        info!(
            "Burnchain block produced: {burn_height}, in_prepare_phase?: {}, first_reward_block?: {}",
            pox_constants.is_in_prepare_phase(first_burn_height, burn_height),
            pox_constants.is_naka_signing_cycle_start(first_burn_height, burn_height)
        );
        let vrf_proof = self.make_nakamoto_vrf_proof(miner_key);

        tenure_change.tenure_consensus_hash = consensus_hash.clone();
        tenure_change.burn_view_consensus_hash = consensus_hash.clone();

        let nakamoto_tip =
            if let Some(nakamoto_parent_tenure) = self.nakamoto_parent_tenure_opt.as_ref() {
                nakamoto_parent_tenure.last().as_ref().unwrap().block_id()
            } else {
                let tip = {
                    let chainstate = &mut self.stacks_node.as_mut().unwrap().chainstate;
                    let sort_db = self.sortdb.as_mut().unwrap();
                    NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
                        .unwrap()
                        .unwrap()
                };
                tip.index_block_hash()
            };

        let miner_addr = self.miner.origin_address().unwrap();
        let miner_acct = self.get_account(&nakamoto_tip, &miner_addr.to_account_principal());

        let tenure_change_tx = self
            .miner
            .make_nakamoto_tenure_change_with_nonce(tenure_change, miner_acct.nonce);

        let coinbase_tx =
            self.miner
                .make_nakamoto_coinbase_with_nonce(None, vrf_proof, miner_acct.nonce + 1);

        let block = self.mine_single_block_tenure_at_tip(
            &nakamoto_tip,
            sender_key,
            &tenure_change_tx,
            &coinbase_tx,
            miner_setup,
            after_block,
        )?;

        Ok((block, burn_height, tenure_change_tx, coinbase_tx))
    }
}

#[test]
// Test the block commit descendant check in nakamoto
//   - create a 12 address PoX reward set
//   - make a normal block commit, assert that the bitvec must contain 1s for those addresses
//   - make a burn block commit, assert that the bitvec must contain 0s for those addresses
fn block_descendant() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(&private_key));

    let num_stackers: u32 = 4;
    let mut signing_key_seed = num_stackers.to_be_bytes().to_vec();
    signing_key_seed.extend_from_slice(&[1, 1, 1, 1]);
    let signing_key = StacksPrivateKey::from_seed(signing_key_seed.as_slice());
    let test_stackers = (0..num_stackers)
        .map(|index| TestStacker {
            signer_private_key: signing_key.clone(),
            stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
            amount: u64::MAX as u128 - 10000,
            max_amount: Some(u64::MAX as u128),
            pox_addr: Some(PoxAddress::Standard(
                StacksAddress::new(
                    C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                    Hash160::from_data(&index.to_be_bytes()),
                )
                .unwrap(),
                Some(AddressHashMode::SerializeP2PKH),
            )),
        })
        .collect::<Vec<_>>();
    let test_signers = TestSigners::new(vec![signing_key]);
    let mut pox_constants = TestPeerConfig::default().burnchain.pox_constants;
    pox_constants.reward_cycle_length = 10;
    pox_constants.v2_unlock_height = 21;
    pox_constants.pox_3_activation_height = 26;
    pox_constants.v3_unlock_height = 27;
    pox_constants.pox_4_activation_height = 28;

    let mut boot_plan = NakamotoBootPlan::new(function_name!())
        .with_test_stackers(test_stackers)
        .with_test_signers(test_signers)
        .with_private_key(private_key);
    boot_plan.pox_constants = pox_constants;

    let mut peer = boot_plan.boot_into_nakamoto_peer(vec![], None);
    let pox_constants = peer.sortdb().pox_constants.clone();
    let first_burn_height = peer.sortdb().first_block_height;

    // mine until we're at the start of the prepare reward phase (so we *know*
    //  that the reward set contains entries)
    loop {
        let (block, burn_height, ..) =
            peer.single_block_tenure(&private_key, |_| {}, |_| {}, |_| true);

        if pox_constants.is_in_prepare_phase(first_burn_height, burn_height + 1) {
            info!("At prepare phase start"; "burn_height" => burn_height);
            break;
        }
    }

    // mine until right before the end of the prepare phase
    loop {
        let (burn_height, ..) = peer.mine_empty_tenure();
        if pox_constants.is_reward_cycle_start(first_burn_height, burn_height + 3) {
            info!("At prepare phase end"; "burn_height" => burn_height);
            break;
        }
    }

    // this should get chosen as the anchor block.
    let (naka_anchor_block, ..) = peer.single_block_tenure(&private_key, |_| {}, |_| {}, |_| true);

    // make the index=0 block empty, because it doesn't get a descendancy check
    //  so, if this has a tenure mined, the direct parent check won't occur
    peer.mine_empty_tenure();

    // this would be where things go haywire. this tenure's parent will be the anchor block.
    let (first_reward_block, ..) = peer.single_block_tenure(&private_key, |_| {}, |_| {}, |_| true);

    assert_eq!(
        first_reward_block.header.parent_block_id,
        naka_anchor_block.block_id()
    );
}

#[test]
fn block_info_primary_testnet() {
    block_info_tests(true)
}

#[test]
fn block_info_other_testnet() {
    block_info_tests(false)
}

fn block_info_tests(use_primary_testnet: bool) {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(&private_key));

    let num_stackers: u32 = 4;
    let mut signing_key_seed = num_stackers.to_be_bytes().to_vec();
    signing_key_seed.extend_from_slice(&[1, 1, 1, 1]);
    let signing_key = StacksPrivateKey::from_seed(signing_key_seed.as_slice());
    let test_stackers = (0..num_stackers)
        .map(|index| TestStacker {
            signer_private_key: signing_key.clone(),
            stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
            amount: u64::MAX as u128 - 10000,
            pox_addr: Some(PoxAddress::Standard(
                StacksAddress::new(
                    C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                    Hash160::from_data(&index.to_be_bytes()),
                )
                .unwrap(),
                Some(AddressHashMode::SerializeP2PKH),
            )),
            max_amount: None,
        })
        .collect::<Vec<_>>();
    let test_signers = TestSigners::new(vec![signing_key]);
    let mut pox_constants = TestPeerConfig::default().burnchain.pox_constants;
    pox_constants.reward_cycle_length = 10;
    pox_constants.v2_unlock_height = 21;
    pox_constants.pox_3_activation_height = 26;
    pox_constants.v3_unlock_height = 27;
    pox_constants.pox_4_activation_height = 28;

    let chain_id = if use_primary_testnet {
        CHAIN_ID_TESTNET
    } else {
        CHAIN_ID_TESTNET + 1
    };
    let mut boot_plan =
        NakamotoBootPlan::new(&format!("{}.{use_primary_testnet}", function_name!()))
            .with_test_stackers(test_stackers)
            .with_test_signers(test_signers)
            .with_private_key(private_key)
            .with_network_id(chain_id);
    boot_plan.pox_constants = pox_constants;

    // Supply an empty vec to make sure we have no nakamoto blocks when this test begins
    let mut peer = boot_plan.boot_into_nakamoto_peer(vec![], None);

    let clar1_contract = "
       (define-read-only (get-info (height uint)) (get-block-info? id-header-hash height))
    ";
    let clar3_contract = "
       (define-read-only (get-info (height uint)) (get-stacks-block-info? id-header-hash height))
    ";

    let clar1_contract_name = "clar1";
    let clar3_contract_name = "clar3";

    let clar1_contract_id = QualifiedContractIdentifier {
        issuer: addr.clone().into(),
        name: clar1_contract_name.into(),
    };
    let clar3_contract_id = QualifiedContractIdentifier {
        issuer: addr.clone().into(),
        name: clar3_contract_name.into(),
    };

    let get_tip_info = |peer: &mut TestPeer| {
        peer.with_db_state(|sortdb, _, _, _| {
            let (tip_ch, tip_bh, tip_height) =
                SortitionDB::get_canonical_stacks_chain_tip_hash_and_height(sortdb.conn()).unwrap();
            let tip_block_id = StacksBlockId::new(&tip_ch, &tip_bh);
            Ok((tip_block_id, tip_height))
        })
        .unwrap()
    };

    let get_info = |peer: &mut TestPeer,
                    version: ClarityVersion,
                    query_ht: u64,
                    tip_block_id: &StacksBlockId| {
        let contract_id = match version {
            ClarityVersion::Clarity1 => &clar1_contract_id,
            ClarityVersion::Clarity2 => panic!("Clarity2 not supported in this test"),
            ClarityVersion::Clarity3 => &clar3_contract_id,
        };
        peer.with_db_state(|sortdb, chainstate, _, _| {
            let sortdb_handle = sortdb.index_handle_at_tip();
            let output = chainstate
                .clarity_eval_read_only(
                    &sortdb_handle,
                    tip_block_id,
                    contract_id,
                    &format!("(get-info u{query_ht})"),
                )
                .expect_optional()
                .unwrap()
                .map(|value| StacksBlockId::from_vec(&value.expect_buff(32).unwrap()).unwrap());

            info!("At stacks block {tip_block_id}, {contract_id} returned {output:?}");

            Ok(output)
        })
        .unwrap()
    };

    let (last_2x_block_id, last_2x_block_ht) = get_tip_info(&mut peer);

    peer.mine_tenure(|miner, chainstate, sortdb, blocks_so_far| {
        if !blocks_so_far.is_empty() {
            return vec![];
        }
        info!("Producing first nakamoto block, publishing our three contracts");
        let account = get_account(chainstate, sortdb, &addr);
        let tx_0 = make_contract(
            chainstate,
            clar1_contract_name,
            clar1_contract,
            &private_key,
            ClarityVersion::Clarity1,
            account.nonce,
            1000,
        );
        let tx_1 = make_contract(
            chainstate,
            clar3_contract_name,
            clar3_contract,
            &private_key,
            ClarityVersion::Clarity3,
            account.nonce + 1,
            1000,
        );

        vec![tx_0, tx_1]
    });

    let (tenure_1_start_block_id, tenure_1_block_ht) = get_tip_info(&mut peer);
    assert_eq!(
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            last_2x_block_ht,
            &tenure_1_start_block_id
        )
        .unwrap(),
        last_2x_block_id,
    );
    assert_eq!(
        get_info(
            &mut peer,
            ClarityVersion::Clarity3,
            last_2x_block_ht,
            &tenure_1_start_block_id
        )
        .unwrap(),
        last_2x_block_id,
    );
    assert!(get_info(
        &mut peer,
        ClarityVersion::Clarity1,
        tenure_1_block_ht,
        &tenure_1_start_block_id
    )
    .is_none());
    assert!(get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_1_block_ht,
        &tenure_1_start_block_id
    )
    .is_none());

    let recipient_addr = StacksAddress::p2pkh(
        false,
        &StacksPublicKey::from_private(&StacksPrivateKey::from_seed(&[2, 1, 2])),
    );

    let tenure_2_blocks: Vec<_> = peer
        .mine_tenure(|miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() > 3 {
                return vec![];
            }
            info!("Producing block #{} in Tenure #2", blocks_so_far.len());
            let account = get_account(chainstate, sortdb, &addr);
            let tx_0 = make_token_transfer(
                chainstate,
                sortdb,
                &private_key,
                account.nonce,
                100,
                1,
                &recipient_addr,
            );

            vec![tx_0]
        })
        .into_iter()
        .map(|(block, ..)| block.header.block_id())
        .collect();

    let (tenure_2_last_block_id, tenure_2_last_block_ht) = get_tip_info(&mut peer);

    assert_eq!(&tenure_2_last_block_id, tenure_2_blocks.last().unwrap());

    let c3_tenure1_from_tenure2 = get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_1_block_ht,
        &tenure_2_blocks[0],
    )
    .unwrap();
    let c1_tenure1_from_tenure2 = get_info(
        &mut peer,
        ClarityVersion::Clarity1,
        tenure_1_block_ht,
        &tenure_2_blocks[0],
    )
    .unwrap();

    // note, since tenure_1 only has one block in it, tenure_1_block_ht is *also* the tenure height, so this should return the
    // same value regardless of the `primary_tesnet` flag
    assert_eq!(c1_tenure1_from_tenure2, c3_tenure1_from_tenure2);
    assert_eq!(c1_tenure1_from_tenure2, tenure_1_start_block_id);

    let tenure_2_start_block_ht = tenure_1_block_ht + 1;
    let tenure_2_tenure_ht = tenure_1_block_ht + 1;

    // make sure we can't look up block info from the block we're evaluating at
    if use_primary_testnet {
        assert!(get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_start_block_ht,
            &tenure_2_blocks[0]
        )
        .is_none());
    } else {
        assert!(get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_tenure_ht,
            &tenure_2_blocks[0]
        )
        .is_none());
    }
    assert!(get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_2_start_block_ht,
        &tenure_2_blocks[0]
    )
    .is_none());

    // but we can from the next block in the tenure
    let c1_tenure_2_start_block = if use_primary_testnet {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_start_block_ht,
            &tenure_2_blocks[1],
        )
        .unwrap()
    } else {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_tenure_ht,
            &tenure_2_blocks[1],
        )
        .unwrap()
    };
    let c3_tenure_2_start_block = get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_2_start_block_ht,
        &tenure_2_blocks[1],
    )
    .unwrap();
    assert_eq!(c1_tenure_2_start_block, c3_tenure_2_start_block);
    assert_eq!(&c1_tenure_2_start_block, &tenure_2_blocks[0]);

    // try to query the middle block from the last block in the tenure
    let c1_tenure_2_mid_block = if use_primary_testnet {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_start_block_ht + 1,
            &tenure_2_blocks[2],
        )
    } else {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_start_block_ht + 1,
            &tenure_2_blocks[2],
        )
    };
    let c3_tenure_2_mid_block = get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_2_start_block_ht + 1,
        &tenure_2_blocks[2],
    )
    .unwrap();
    assert_eq!(&c3_tenure_2_mid_block, &tenure_2_blocks[1]);
    if use_primary_testnet {
        assert_eq!(c1_tenure_2_mid_block.unwrap(), c3_tenure_2_mid_block);
    } else {
        // if interpreted as a tenure-height, this will return none, because there's no tenure at height +1 yet
        assert!(c1_tenure_2_mid_block.is_none());

        // query the tenure height again from the latest block for good measure
        let start_block_result = get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_2_tenure_ht,
            &tenure_2_blocks[2],
        )
        .unwrap();
        assert_eq!(&start_block_result, &tenure_2_blocks[0]);
    }

    let tenure_3_tenure_ht = tenure_2_tenure_ht + 1;
    let tenure_3_start_block_ht =
        tenure_2_start_block_ht + u64::try_from(tenure_2_blocks.len()).unwrap();

    let tenure_3_blocks: Vec<_> = peer
        .mine_tenure(|miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() > 3 {
                return vec![];
            }
            info!("Producing block #{} in Tenure #3", blocks_so_far.len());
            let account = get_account(chainstate, sortdb, &addr);
            let tx_0 = make_token_transfer(
                chainstate,
                sortdb,
                &private_key,
                account.nonce,
                100,
                1,
                &recipient_addr,
            );

            vec![tx_0]
        })
        .into_iter()
        .map(|(block, ..)| block.header.block_id())
        .collect();

    let (tenure_3_last_block_id, tenure_3_last_block_ht) = get_tip_info(&mut peer);

    assert_eq!(&tenure_3_last_block_id, tenure_3_blocks.last().unwrap());
    assert_eq!(tenure_3_start_block_ht, tenure_2_last_block_ht + 1);

    // query the current tenure information from the middle block
    let c1_tenure_3_start_block = if use_primary_testnet {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_3_start_block_ht,
            &tenure_3_blocks[1],
        )
        .unwrap()
    } else {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_3_tenure_ht,
            &tenure_3_blocks[1],
        )
        .unwrap()
    };
    let c3_tenure_3_start_block = get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_3_start_block_ht,
        &tenure_3_blocks[1],
    )
    .unwrap();
    assert_eq!(c1_tenure_3_start_block, c3_tenure_3_start_block);
    assert_eq!(&c1_tenure_3_start_block, &tenure_3_blocks[0]);

    // try to query the middle block from the last block in the tenure
    let c1_tenure_3_mid_block = if use_primary_testnet {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_3_start_block_ht + 1,
            &tenure_3_blocks[2],
        )
    } else {
        get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_3_start_block_ht + 1,
            &tenure_3_blocks[2],
        )
    };
    let c3_tenure_3_mid_block = get_info(
        &mut peer,
        ClarityVersion::Clarity3,
        tenure_3_start_block_ht + 1,
        &tenure_3_blocks[2],
    )
    .unwrap();
    assert_eq!(&c3_tenure_3_mid_block, &tenure_3_blocks[1]);
    if use_primary_testnet {
        assert_eq!(c1_tenure_3_mid_block.unwrap(), c3_tenure_3_mid_block);
    } else {
        // if interpreted as a tenure-height, this will return none, because there's no tenure at height +1 yet
        assert!(c1_tenure_3_mid_block.is_none());

        // query the tenure height again from the latest block for good measure
        let start_block_result = get_info(
            &mut peer,
            ClarityVersion::Clarity1,
            tenure_3_tenure_ht,
            &tenure_3_blocks[2],
        )
        .unwrap();
        assert_eq!(&start_block_result, &tenure_3_blocks[0]);
    }
}

#[test]
// Test PoX Reward and Punish treatment in nakamoto
//   - create a 12 address PoX reward set
//   - make a normal block commit, assert that the bitvec must contain 1s for those addresses
//   - make a burn block commit, assert that the bitvec must contain 0s for those addresses
fn pox_treatment() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(&private_key));

    let num_stackers: u32 = 4;
    let mut signing_key_seed = num_stackers.to_be_bytes().to_vec();
    signing_key_seed.extend_from_slice(&[1, 1, 1, 1]);
    let signing_key = StacksPrivateKey::from_seed(signing_key_seed.as_slice());
    let test_stackers = (0..num_stackers)
        .map(|index| TestStacker {
            signer_private_key: signing_key.clone(),
            stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
            amount: u64::MAX as u128 - 10000,
            pox_addr: Some(PoxAddress::Standard(
                StacksAddress::new(
                    C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                    Hash160::from_data(&index.to_be_bytes()),
                )
                .unwrap(),
                Some(AddressHashMode::SerializeP2PKH),
            )),
            max_amount: None,
        })
        .collect::<Vec<_>>();
    let test_signers = TestSigners::new(vec![signing_key]);
    let mut pox_constants = TestPeerConfig::default().burnchain.pox_constants;
    pox_constants.reward_cycle_length = 10;
    pox_constants.v2_unlock_height = 21;
    pox_constants.pox_3_activation_height = 26;
    pox_constants.v3_unlock_height = 27;
    pox_constants.pox_4_activation_height = 28;

    let mut boot_plan = NakamotoBootPlan::new(function_name!())
        .with_test_stackers(test_stackers.clone())
        .with_test_signers(test_signers)
        .with_private_key(private_key);
    boot_plan.pox_constants = pox_constants;

    let mut peer = boot_plan.boot_into_nakamoto_peer(vec![], None);
    let mut blocks = vec![];
    let pox_constants = peer.sortdb().pox_constants.clone();
    let first_burn_height = peer.sortdb().first_block_height;

    // mine until we're at the start of the next reward phase (so we *know*
    //  that the reward set contains entries)
    loop {
        let (block, burn_height, ..) =
            peer.single_block_tenure(&private_key, |_| {}, |_| {}, |_| true);
        blocks.push(block);

        // note: we use `is_reward_cycle_start` here rather than naka_reward_cycle_start
        //  because in this test, we're interested in getting to the reward blocks,
        //  not validating the signer set. the reward blocks only begin at modulo 1
        if pox_constants.is_reward_cycle_start(first_burn_height, burn_height + 1) {
            break;
        }
    }

    let mut expected_reward_set = vec![];
    for stacker in test_stackers.iter() {
        let pox_addr = stacker.pox_addr.as_ref().unwrap();
        (0..3).for_each(|_| expected_reward_set.push(pox_addr.clone()));
    }
    expected_reward_set.sort_by_key(|addr| addr.to_burnchain_repr());
    expected_reward_set.reverse();
    let pox_recipients = Mutex::new(vec![]);
    info!("Starting the test... beginning with an reward commit");
    // The next block should be the start of a reward phase, so the PoX recipient should
    //  be chosen.
    //
    // First: perform a normal block commit, and then try to mine a block with all zeros in the
    //        bitvector.
    let (invalid_block, _, tenure_change_tx, coinbase_tx) = peer.single_block_tenure(
        &private_key,
        |_| {},
        |burn_ops| {
            burn_ops.iter().for_each(|op| {
                if let BlockstackOperationType::LeaderBlockCommit(ref commit) = op {
                    *pox_recipients.lock().unwrap() = commit.commit_outs.clone();
                }
            });
        },
        |block| {
            let pox_recipients = pox_recipients.lock().unwrap();
            assert_eq!(pox_recipients.len(), 2);
            info!(
                "Expected reward set: {:?}",
                expected_reward_set
                    .iter()
                    .map(|x| x.to_burnchain_repr())
                    .collect::<Vec<_>>()
            );
            let target_indexes = pox_recipients.iter().map(|pox_addr| {
                expected_reward_set
                    .iter()
                    .enumerate()
                    .find_map(|(ix, rs_addr)| if rs_addr == pox_addr { Some(ix) } else { None })
                    .unwrap()
            });
            let mut bitvec = BitVec::ones(12).unwrap();
            target_indexes.for_each(|ix| {
                let ix: u16 = ix.try_into().unwrap();
                bitvec.set(ix, false).unwrap();
                bitvec.set(1 + ix, false).unwrap();
                bitvec.set(2 + ix, false).unwrap();
            });
            block.header.pox_treatment = bitvec;
            // don't try to process this block yet, just return it so that
            //  we can assert the block error.
            false
        },
    );
    let processing_result = peer.try_process_block(&invalid_block).unwrap_err();
    assert_eq!(
        processing_result.to_string(),
        "Bitvec does not match the block commit's PoX handling".to_string(),
    );
    assert!(matches!(
        processing_result,
        ChainstateError::InvalidStacksBlock(_),
    ));

    // set the bitvec to a heterogenous one: either punish or
    //  reward is acceptable, so this block should just process.
    let block = peer
        .mine_single_block_tenure(
            &private_key,
            &tenure_change_tx,
            &coinbase_tx,
            |_| {},
            |block| {
                // each stacker has 3 entries in the bitvec.
                // entries are ordered by PoxAddr, so this makes every entry a 1-of-3
                block.header.pox_treatment = BitVec::try_from(
                    [
                        false, false, true, false, false, true, false, false, true, false, false,
                        true,
                    ]
                    .as_slice(),
                )
                .unwrap();
                true
            },
        )
        .unwrap();
    blocks.push(block);

    // now we need to test punishment!
    info!("Testing a punish commit");
    let pox_recipients = Mutex::new(vec![]);
    let (invalid_block, _, tenure_change_tx, coinbase_tx) = peer.single_block_tenure(
        &private_key,
        |miner| {
            // we want the miner to finish assembling the block, and then we'll
            //  alter the bitvec before it signs the block (in a subsequent closure).
            // this way, we can test the block processing behavior.
            miner.header.pox_treatment = BitVec::try_from(
                [
                    false, false, true, false, false, true, false, false, true, false, false, true,
                ]
                .as_slice(),
            )
            .unwrap();
        },
        |burn_ops| {
            burn_ops.iter_mut().for_each(|op| {
                if let BlockstackOperationType::LeaderBlockCommit(ref mut commit) = op {
                    *pox_recipients.lock().unwrap() = vec![commit.commit_outs[0].clone()];
                    commit.commit_outs[0] = PoxAddress::standard_burn_address(false);
                }
            });
        },
        |block| {
            let pox_recipients = pox_recipients.lock().unwrap();
            assert_eq!(pox_recipients.len(), 1);
            info!(
                "Expected reward set: {:?}",
                expected_reward_set
                    .iter()
                    .map(|x| x.to_burnchain_repr())
                    .collect::<Vec<_>>()
            );
            let target_indexes = pox_recipients.iter().map(|pox_addr| {
                expected_reward_set
                    .iter()
                    .enumerate()
                    .find_map(|(ix, rs_addr)| if rs_addr == pox_addr { Some(ix) } else { None })
                    .unwrap()
            });
            let mut bitvec = BitVec::zeros(12).unwrap();
            target_indexes.for_each(|ix| {
                let ix: u16 = ix.try_into().unwrap();
                bitvec.set(ix, true).unwrap();
                bitvec.set(1 + ix, true).unwrap();
                bitvec.set(2 + ix, true).unwrap();
            });

            block.header.pox_treatment = bitvec;
            // don't try to process this block yet, just return it so that
            //  we can assert the block error.
            false
        },
    );
    let processing_result = peer.try_process_block(&invalid_block).unwrap_err();
    assert_eq!(
        processing_result.to_string(),
        "Bitvec does not match the block commit's PoX handling".to_string(),
    );
    assert!(matches!(
        processing_result,
        ChainstateError::InvalidStacksBlock(_),
    ));

    // set the bitvec to a heterogenous one: either punish or
    //  reward is acceptable, so this block should just process.
    let block = peer
        .mine_single_block_tenure(
            &private_key,
            &tenure_change_tx,
            &coinbase_tx,
            |miner| {
                // each stacker has 3 entries in the bitvec.
                // entries are ordered by PoxAddr, so this makes every entry a 1-of-3
                miner.header.pox_treatment = BitVec::try_from(
                    [
                        false, false, true, false, false, true, false, false, true, false, false,
                        true,
                    ]
                    .as_slice(),
                )
                .unwrap();
            },
            |_block| true,
        )
        .unwrap();
    blocks.push(block);

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );
}

/// Test chainstate getters against an instantiated epoch2/Nakamoto chain.
/// There are 11 epoch2 blocks and 2 nakamto tenure with 10 nakamoto blocks each
/// Tests:
/// * get_header_by_coinbase_height
/// * get_ongoing_tenure
/// * check_first_nakamoto_tenure
/// * check_valid_consensus_hash
/// * check_nakamoto_tenure
/// * check_tenure_continuity
#[test]
fn test_nakamoto_chainstate_getters() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();
    let (mut test_signers, test_stackers) = TestStacker::common_signing_set();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let sort_tip = {
        let sort_db = peer.sortdb.as_ref().unwrap();
        SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap()
    };
    {
        // scope this to drop the chainstate ref and db tx
        let chainstate = &peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let sort_handle = sort_db.index_handle(&sort_tip.sortition_id);

        // no tenures yet
        assert!(NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_handle.get_nakamoto_tip_block_id().unwrap().unwrap()
        )
        .unwrap()
        .is_none());

        // sortition-existence-check works
        assert_eq!(
            NakamotoChainState::check_sortition_exists(&sort_handle, &sort_tip.consensus_hash)
                .unwrap(),
            sort_tip
        );
    }

    let (burn_ops, mut tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
    let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops);
    let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    tenure_change.tenure_consensus_hash = consensus_hash.clone();
    tenure_change.burn_view_consensus_hash = consensus_hash.clone();
    let tenure_change_tx = peer.miner.make_nakamoto_tenure_change(tenure_change);
    let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

    // do a stx transfer in each block to a given recipient
    let recipient_addr =
        StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();

    let blocks_and_sizes = peer.make_nakamoto_tenure(
        tenure_change_tx,
        coinbase_tx,
        &mut test_signers,
        |miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    let tip = {
        let chainstate = &peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        21
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    let sort_tip = {
        let sort_db = peer.sortdb.as_ref().unwrap();
        SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap()
    };
    {
        // scope this to drop the chainstate ref and db tx
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_ref().unwrap();

        for coinbase_height in 0..=((tip
            .anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length
            - 10)
            + 1)
        {
            let header_opt = NakamotoChainState::get_header_by_coinbase_height(
                &mut chainstate.index_conn(),
                &tip.index_block_hash(),
                coinbase_height,
            )
            .unwrap();
            let header = header_opt.expect("No tenure");

            if coinbase_height
                <= tip
                    .anchored_header
                    .as_stacks_nakamoto()
                    .unwrap()
                    .chain_length
                    - 10
            {
                // all tenures except the last are epoch2
                assert!(header.anchored_header.as_stacks_epoch2().is_some());
            } else {
                // last tenure is nakamoto
                assert!(header.anchored_header.as_stacks_nakamoto().is_some());
            }
        }
    }

    debug!("\n======================================\nBegin tests\n===========================================\n");
    {
        // scope this to drop the chainstate ref and db tx
        let chainstate = &peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let mut sort_tx = sort_db.tx_handle_begin(&sort_tip.sortition_id).unwrap();

        // we now have a tenure, and it confirms the last epoch2 block
        let highest_tenure = NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_tx.get_nakamoto_tip_block_id().unwrap().unwrap(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(highest_tenure.coinbase_height, 12);
        assert_eq!(highest_tenure.num_blocks_confirmed, 1);
        assert_eq!(highest_tenure.tenure_id_consensus_hash, consensus_hash);
        assert_eq!(highest_tenure.burn_view_consensus_hash, consensus_hash);

        // confirm that getting the burn block for this highest tenure works
        let sn = SortitionDB::get_block_snapshot_consensus(
            sort_tx.tx(),
            &highest_tenure.tenure_id_consensus_hash,
        )
        .unwrap()
        .unwrap();

        // this tenure's TC tx is the first-ever TC
        let tenure_change_payload = blocks[0].get_tenure_change_tx_payload().unwrap().clone();

        assert!(NakamotoChainState::check_first_nakamoto_tenure_change(
            chainstate.db(),
            &tenure_change_payload,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_tenure_continuity(
            &mut chainstate.index_conn(),
            &blocks[0].header.consensus_hash,
            &blocks[1].header,
        )
        .unwrap());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.prev_tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.burn_view_consensus_hash,
        )
        .unwrap()
        .is_some());

        // this should return the previous tenure
        assert_eq!(
            NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sort_tx,
                &blocks[0].header,
                &tenure_change_payload,
            )
            .unwrap()
            .unwrap()
            .tenure_id_consensus_hash,
            tenure_change_payload.prev_tenure_consensus_hash
        );

        let cur_burn_tip = SortitionDB::get_canonical_burn_chain_tip(sort_tx.sqlite()).unwrap();
        let (cur_stacks_ch, cur_stacks_bhh, cur_stacks_height) =
            SortitionDB::get_canonical_stacks_chain_tip_hash_and_height(sort_tx.sqlite()).unwrap();
        sort_tx
            .test_update_canonical_stacks_tip(
                &cur_burn_tip.sortition_id,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                0,
            )
            .unwrap();

        // drop the highest tenure, so this check can pass
        NakamotoChainState::delete_nakamoto_tenure(
            chainstate.db(),
            &blocks[0].header.consensus_hash,
        )
        .unwrap();

        // check works (this would be the first tenure)
        assert_eq!(
            NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sort_tx,
                &blocks[0].header,
                &tenure_change_payload,
            )
            .unwrap()
            .unwrap()
            .tenure_id_consensus_hash,
            tenure_change_payload.prev_tenure_consensus_hash
        );

        // restore
        sort_tx
            .test_update_canonical_stacks_tip(
                &cur_burn_tip.sortition_id,
                &cur_stacks_ch,
                &cur_stacks_bhh,
                cur_stacks_height,
            )
            .unwrap();
        NakamotoChainState::insert_nakamoto_tenure(
            chainstate.db(),
            &blocks[0].header,
            12,
            &tenure_change_payload,
        )
        .unwrap();
    }

    debug!("\n======================================\nBegin second tenure\n===========================================\n");
    // begin another tenure
    let (burn_ops, mut next_tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);

    // find the txid
    let mut txid = None;
    for op in burn_ops.iter() {
        if let BlockstackOperationType::LeaderBlockCommit(ref op) = &op {
            txid = Some(op.txid.clone());
        }
    }
    let txid = txid.unwrap();

    let (_, _, next_consensus_hash) = peer.next_burnchain_block(burn_ops);
    let next_vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    next_tenure_change.tenure_consensus_hash = next_consensus_hash.clone();
    next_tenure_change.burn_view_consensus_hash = next_consensus_hash.clone();

    let next_tenure_change_tx = peer.miner.make_nakamoto_tenure_change(next_tenure_change);
    let next_coinbase_tx = peer.miner.make_nakamoto_coinbase(None, next_vrf_proof);

    // make the second tenure's blocks
    let blocks_and_sizes = peer.make_nakamoto_tenure(
        next_tenure_change_tx,
        next_coinbase_tx,
        &mut test_signers,
        |miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let new_blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    let sort_tip = {
        let sort_db = peer.sortdb.as_ref().unwrap();
        SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap()
    };
    {
        // scope this to drop the chainstate ref and db tx
        let chainstate = &peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();

        let mut sort_tx = sort_db.tx_handle_begin(&sort_tip.sortition_id).unwrap();

        // we now have a new highest tenure
        let highest_tenure = NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_tx.get_nakamoto_tip_block_id().unwrap().unwrap(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(highest_tenure.coinbase_height, 13);
        assert_eq!(highest_tenure.num_blocks_confirmed, 10);
        assert_eq!(highest_tenure.tenure_id_consensus_hash, next_consensus_hash);
        assert_eq!(highest_tenure.prev_tenure_id_consensus_hash, consensus_hash);
        assert_eq!(highest_tenure.burn_view_consensus_hash, next_consensus_hash);

        // this tenure's TC tx is NOT the first-ever TC
        let tenure_change_payload = new_blocks[0]
            .get_tenure_change_tx_payload()
            .unwrap()
            .clone();
        let old_tenure_change_payload = blocks[0].get_tenure_change_tx_payload().unwrap().clone();

        assert!(NakamotoChainState::check_first_nakamoto_tenure_change(
            chainstate.db(),
            &tenure_change_payload,
        )
        .unwrap()
        .is_none());
        assert!(NakamotoChainState::check_tenure_continuity(
            &mut chainstate.index_conn(),
            &new_blocks[0].header.consensus_hash,
            &new_blocks[1].header,
        )
        .unwrap());
        assert!(!NakamotoChainState::check_tenure_continuity(
            &mut chainstate.index_conn(),
            &blocks[0].header.consensus_hash,
            &new_blocks[1].header,
        )
        .unwrap());

        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.prev_tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &tenure_change_payload.burn_view_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &old_tenure_change_payload.tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &old_tenure_change_payload.prev_tenure_consensus_hash,
        )
        .unwrap()
        .is_some());
        assert!(NakamotoChainState::check_valid_consensus_hash(
            &mut sort_tx,
            &old_tenure_change_payload.burn_view_consensus_hash,
        )
        .unwrap()
        .is_some());

        let cur_burn_tip = SortitionDB::get_canonical_burn_chain_tip(sort_tx.sqlite()).unwrap();
        let (cur_stacks_ch, cur_stacks_bhh, cur_stacks_height) =
            SortitionDB::get_canonical_stacks_chain_tip_hash_and_height(sort_tx.sqlite()).unwrap();
        sort_tx
            .test_update_canonical_stacks_tip(
                &cur_burn_tip.sortition_id,
                &blocks[9].header.consensus_hash,
                &blocks[9].header.block_hash(),
                blocks[9].header.chain_length,
            )
            .unwrap();

        NakamotoChainState::delete_nakamoto_tenure(
            chainstate.db(),
            &new_blocks[0].header.consensus_hash,
        )
        .unwrap();

        assert_eq!(
            NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sort_tx,
                &new_blocks[0].header,
                &tenure_change_payload,
            )
            .unwrap()
            .unwrap()
            .tenure_id_consensus_hash,
            tenure_change_payload.prev_tenure_consensus_hash
        );

        // checks on older confired tenures return the prev tenure
        assert_eq!(
            NakamotoChainState::check_nakamoto_tenure(
                &mut chainstate.index_conn(),
                &mut sort_tx,
                &blocks[0].header,
                &old_tenure_change_payload,
            )
            .unwrap()
            .unwrap()
            .tenure_id_consensus_hash,
            old_tenure_change_payload.prev_tenure_consensus_hash
        );

        // restore
        sort_tx
            .test_update_canonical_stacks_tip(
                &cur_burn_tip.sortition_id,
                &cur_stacks_ch,
                &cur_stacks_bhh,
                cur_stacks_height,
            )
            .unwrap();
        NakamotoChainState::insert_nakamoto_tenure(
            chainstate.db(),
            &new_blocks[0].header,
            13,
            &tenure_change_payload,
        )
        .unwrap();
    }

    peer.check_nakamoto_migration();
}

/// Mine a 10 Nakamoto tenures with between 1 and 10 Nakamoto blocks each.
/// Checks the matured mining rewards as well.
pub fn simple_nakamoto_coordinator_10_tenures_10_sortitions<'a>() -> TestPeer<'a> {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    let (mut test_signers, test_stackers) = TestStacker::common_signing_set();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let mut all_blocks: Vec<NakamotoBlock> = vec![];
    let mut all_burn_ops = vec![];
    let mut rc_blocks = vec![];
    let mut rc_burn_ops = vec![];
    let mut consensus_hashes = vec![];
    let mut fee_counts = vec![];
    let mut total_blocks = 0;
    let stx_miner_key = peer.miner.nakamoto_miner_key();
    let stx_miner_addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    for i in 0..10 {
        debug!("Tenure {}", i);
        let (burn_ops, mut tenure_change, miner_key) =
            peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
        let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

        tenure_change.tenure_consensus_hash = consensus_hash.clone();
        tenure_change.burn_view_consensus_hash = consensus_hash.clone();

        let tenure_change_tx = peer
            .miner
            .make_nakamoto_tenure_change(tenure_change.clone());
        let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

        debug!("Next burnchain block: {}", &consensus_hash);

        let num_blocks: usize = (thread_rng().gen::<usize>() % 10) + 1;

        let block_height = peer.get_burn_block_height();

        // do a stx transfer in each block to a given recipient
        let recipient_addr =
            StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();
        let blocks_and_sizes = peer.make_nakamoto_tenure(
            tenure_change_tx,
            coinbase_tx,
            &mut test_signers,
            |miner, chainstate, sortdb, blocks_so_far| {
                let mut txs = vec![];
                if blocks_so_far.len() < num_blocks {
                    debug!("\n\nProduce block {}\n\n", all_blocks.len());

                    let account = get_account(chainstate, sortdb, &addr);

                    let stx_transfer = make_token_transfer(
                        chainstate,
                        sortdb,
                        &private_key,
                        account.nonce,
                        100,
                        1,
                        &recipient_addr,
                    );
                    txs.push(stx_transfer);
                }
                txs
            },
        );

        let fees = blocks_and_sizes
            .iter()
            .map(|(block, _, _)| {
                block
                    .txs
                    .iter()
                    .map(|tx| tx.get_tx_fee() as u128)
                    .sum::<u128>()
            })
            .sum::<u128>();

        consensus_hashes.push(consensus_hash);
        fee_counts.push(fees);
        total_blocks += num_blocks;

        let mut blocks: Vec<NakamotoBlock> = blocks_and_sizes
            .into_iter()
            .map(|(block, _, _)| block)
            .collect();

        // if we're starting a new reward cycle, then save the current one
        let tip = {
            let sort_db = peer.sortdb.as_mut().unwrap();
            SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap()
        };
        if peer
            .config
            .burnchain
            .is_naka_signing_cycle_start(tip.block_height)
        {
            rc_blocks.push(all_blocks.clone());
            rc_burn_ops.push(all_burn_ops.clone());

            all_burn_ops.clear();
            all_blocks.clear();
        }

        all_blocks.append(&mut blocks);
        all_burn_ops.push(burn_ops);
    }

    rc_blocks.push(all_blocks.clone());
    rc_burn_ops.push(all_burn_ops.clone());

    all_burn_ops.clear();
    all_blocks.clear();

    // in nakamoto, tx fees are rewarded by the next tenure, so the
    // scheduled rewards come 1 tenure after the coinbase reward matures
    let miner = p2pkh_from(&stx_miner_key);
    let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
    let sort_db = peer.sortdb.as_mut().unwrap();

    // this is sortition height 12, and this miner has earned all 12 of the coinbases
    // plus the initial per-block mining bonus of 2600 STX, but minus the last three rewards (since
    // the miner rewards take three sortitions to confirm).
    //
    // This is (1000 + 2600) * 10 + 1000 - (3600 * 2 + 1000)
    //            first 10          block    unmatured rewards
    //            blocks             11
    debug!("block fees: {:?}", &fee_counts);
    let mut expected_coinbase_rewards: u128 = 28800000000;
    let mut fees_so_far: u128 = 0;
    for (i, ch) in consensus_hashes.into_iter().enumerate() {
        let sn = SortitionDB::get_block_snapshot_consensus(sort_db.conn(), &ch)
            .unwrap()
            .unwrap();

        if !sn.sortition {
            continue;
        }
        let block_id = StacksBlockId(sn.winning_stacks_block_hash.0);

        let (chainstate_tx, clarity_instance) = chainstate.chainstate_tx_begin().unwrap();
        let sort_db_tx = sort_db.tx_begin_at_tip();

        let stx_balance = clarity_instance
            .read_only_connection(&block_id, &chainstate_tx, &sort_db_tx)
            .with_clarity_db_readonly(|db| db.get_account_stx_balance(&miner.clone().into()))
            .unwrap();

        // only count matured rewards (last 3 blocks are not mature)
        let block_fee = if i > 3 {
            fee_counts[i.saturating_sub(4)]
        } else {
            0
        };
        let expected_total_tx_fees = fees_so_far + block_fee;
        let expected_total_coinbase = expected_coinbase_rewards;
        fees_so_far += block_fee;

        if i == 0 {
            // first tenure awards the last of the initial mining bonus
            expected_coinbase_rewards += (1000 + 2600) * 1000000;
        } else {
            // subsequent tenures award normal coinbases
            expected_coinbase_rewards += 1000 * 1000000;
        }

        eprintln!(
            "Checking block #{} ({},{}): {} =?= {} + {}",
            i,
            &ch,
            &sn.block_height,
            stx_balance.amount_unlocked(),
            expected_total_coinbase,
            expected_total_tx_fees
        );
        assert_eq!(
            stx_balance.amount_unlocked(),
            expected_total_coinbase + expected_total_tx_fees
        );
    }

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        (11 + total_blocks) as u64
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &rc_blocks.last().unwrap().last().unwrap().header
    );

    // verify that matured miner records were in place
    let mut matured_rewards = vec![];
    {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let (mut chainstate_tx, _) = chainstate.chainstate_tx_begin().unwrap();
        for i in 0..24 {
            let matured_reward_opt = NakamotoChainState::get_matured_miner_reward_schedules(
                &mut chainstate_tx,
                &tip.index_block_hash(),
                i,
            )
            .unwrap();
            matured_rewards.push(matured_reward_opt);
        }
    }
    for (i, matured_reward_opt) in matured_rewards[4..].into_iter().enumerate() {
        let matured_reward = (*matured_reward_opt).clone().unwrap();
        debug!("{}: {:?}", i, &matured_reward);

        if i < 10 {
            assert_eq!(matured_reward.parent_miner.coinbase, 3_600_000_000);
        } else {
            assert_eq!(matured_reward.parent_miner.coinbase, 1_000_000_000);
        }

        match i.cmp(&11) {
            Ordering::Less => {
                // epoch2
                assert_eq!(
                    matured_reward.parent_miner.tx_fees,
                    MinerPaymentTxFees::Epoch2 {
                        anchored: 0,
                        streamed: 0,
                    }
                );
            }
            Ordering::Equal => {
                // transition
                assert_eq!(
                    matured_reward.parent_miner.tx_fees,
                    MinerPaymentTxFees::Nakamoto { parent_fees: 0 }
                );
            }
            Ordering::Greater => {
                // nakamoto
                assert_eq!(
                    matured_reward.parent_miner.tx_fees,
                    MinerPaymentTxFees::Nakamoto {
                        parent_fees: fee_counts[i - 12]
                    }
                )
            }
        };

        assert_eq!(matured_reward.latest_miners.len(), 1);

        let miner_reward = &matured_reward.latest_miners[0];

        if i < 9 {
            assert_eq!(miner_reward.coinbase, 3_600_000_000);
        } else {
            assert_eq!(miner_reward.coinbase, 1_000_000_000);
        }

        match i.cmp(&10) {
            Ordering::Less => {
                // epoch2
                assert_eq!(
                    miner_reward.tx_fees,
                    MinerPaymentTxFees::Epoch2 {
                        anchored: 0,
                        streamed: 0,
                    }
                )
            }
            Ordering::Equal => {
                // transition
                assert_eq!(
                    miner_reward.tx_fees,
                    MinerPaymentTxFees::Nakamoto { parent_fees: 0 }
                )
            }
            Ordering::Greater => {
                // nakamoto
                assert_eq!(
                    miner_reward.tx_fees,
                    MinerPaymentTxFees::Nakamoto {
                        parent_fees: fee_counts[i - 11]
                    }
                )
            }
        };
    }

    // replay the blocks and sortitions in random order, and verify that we still reach the chain
    // tip
    let mut replay_peer = make_replay_peer(&mut peer);
    for (burn_ops, blocks) in rc_burn_ops.iter().zip(rc_blocks.iter()) {
        replay_reward_cycle(&mut replay_peer, burn_ops, blocks);
    }

    let tip = {
        let chainstate = &mut replay_peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = replay_peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        (11 + total_blocks) as u64
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &rc_blocks.last().unwrap().last().unwrap().header
    );

    peer.check_nakamoto_migration();
    return peer;
}

#[test]
fn test_nakamoto_coordinator_10_tenures_10_sortitions() {
    simple_nakamoto_coordinator_10_tenures_10_sortitions();
}

/// Mine two tenures across three sortitions, using a tenure-extend to allow the first tenure to
/// cover the time of two sortitions.
///
/// Use a tenure-extend to grant the miner of the first tenure the ability to mine
/// 20 blocks in the first tenure (10 before the second sortiton, and 10 after)
pub fn simple_nakamoto_coordinator_2_tenures_3_sortitions<'a>() -> TestPeer<'a> {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();
    let (mut test_signers, test_stackers) = TestStacker::common_signing_set();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let mut rc_burn_ops = vec![];
    let mut all_blocks = vec![];

    // first tenure
    let (burn_ops, mut tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
    let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
    let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    tenure_change.tenure_consensus_hash = consensus_hash.clone();
    tenure_change.burn_view_consensus_hash = consensus_hash.clone();
    let tenure_change_tx = peer
        .miner
        .make_nakamoto_tenure_change(tenure_change.clone());
    let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

    rc_burn_ops.push(burn_ops);

    // do a stx transfer in each block to a given recipient
    let recipient_addr =
        StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();

    let blocks_and_sizes = peer.make_nakamoto_tenure(
        tenure_change_tx,
        coinbase_tx,
        &mut test_signers,
        |miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    all_blocks.append(&mut blocks.clone());

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        21
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    // highest tenure is our tenure-change
    let (highest_tenure, sort_tip) = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let tenure = NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_db
                .index_handle_at_tip()
                .get_nakamoto_tip_block_id()
                .unwrap()
                .unwrap(),
        )
        .unwrap()
        .unwrap();
        (tenure, tip)
    };
    assert_eq!(highest_tenure.tenure_id_consensus_hash, tip.consensus_hash);
    assert_eq!(
        highest_tenure.burn_view_consensus_hash,
        sort_tip.consensus_hash
    );
    assert!(tip.consensus_hash == sort_tip.consensus_hash);
    assert_eq!(highest_tenure.coinbase_height, 12);
    assert_eq!(highest_tenure.cause, TenureChangeCause::BlockFound);
    assert_eq!(highest_tenure.num_blocks_confirmed, 1);

    // extend first tenure
    let (burn_ops, tenure_change_extend, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::Extended);
    let (_, _, next_consensus_hash) = peer.next_burnchain_block(burn_ops.clone());

    rc_burn_ops.push(burn_ops);

    // extending first tenure
    let tenure_change_extend = tenure_change.extend(
        next_consensus_hash,
        blocks.last().cloned().unwrap().header.block_id(),
        blocks.len() as u32,
    );
    let tenure_change_tx = peer.miner.make_nakamoto_tenure_change(tenure_change_extend);

    let blocks_and_sizes = peer.make_nakamoto_tenure_extension(
        tenure_change_tx,
        &mut test_signers,
        |miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce extended block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    all_blocks.append(&mut blocks.clone());

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    // chain grew
    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        31
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    // highest tenure is our tenure-extend
    let (highest_tenure, sort_tip) = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let tenure = NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_db
                .index_handle_at_tip()
                .get_nakamoto_tip_block_id()
                .unwrap()
                .unwrap(),
        )
        .unwrap()
        .unwrap();
        (tenure, tip)
    };
    assert_eq!(highest_tenure.tenure_id_consensus_hash, tip.consensus_hash);
    assert_eq!(
        highest_tenure.burn_view_consensus_hash,
        sort_tip.consensus_hash
    );
    assert!(tip.consensus_hash != sort_tip.consensus_hash);
    assert_eq!(highest_tenure.coinbase_height, 12);
    assert_eq!(highest_tenure.cause, TenureChangeCause::Extended);
    assert_eq!(highest_tenure.num_blocks_confirmed, 10);

    // second tenure
    let (burn_ops, mut tenure_change, miner_key) =
        peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
    let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
    let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

    tenure_change.tenure_consensus_hash = consensus_hash.clone();
    tenure_change.burn_view_consensus_hash = consensus_hash.clone();

    let tenure_change_tx = peer.miner.make_nakamoto_tenure_change(tenure_change);
    let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

    rc_burn_ops.push(burn_ops);

    // do a stx transfer in each block to a given recipient
    let recipient_addr =
        StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();

    let blocks_and_sizes = peer.make_nakamoto_tenure(
        tenure_change_tx,
        coinbase_tx,
        &mut test_signers,
        |miner, chainstate, sortdb, blocks_so_far| {
            if blocks_so_far.len() < 10 {
                debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                let account = get_account(chainstate, sortdb, &addr);
                let stx_transfer = make_token_transfer(
                    chainstate,
                    sortdb,
                    &private_key,
                    account.nonce,
                    100,
                    1,
                    &recipient_addr,
                );

                vec![stx_transfer]
            } else {
                vec![]
            }
        },
    );

    let blocks: Vec<_> = blocks_and_sizes
        .into_iter()
        .map(|(block, _, _)| block)
        .collect();

    all_blocks.append(&mut blocks.clone());

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        41
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    // highest tenure is our new tenure-change
    let (highest_tenure, sort_tip) = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let tenure = NakamotoChainState::get_ongoing_tenure(
            &mut chainstate.index_conn(),
            &sort_db
                .index_handle_at_tip()
                .get_nakamoto_tip_block_id()
                .unwrap()
                .unwrap(),
        )
        .unwrap()
        .unwrap();
        (tenure, tip)
    };
    assert_eq!(highest_tenure.tenure_id_consensus_hash, tip.consensus_hash);
    assert_eq!(
        highest_tenure.burn_view_consensus_hash,
        sort_tip.consensus_hash
    );
    assert!(tip.consensus_hash == sort_tip.consensus_hash);
    assert_eq!(highest_tenure.coinbase_height, 13);
    assert_eq!(highest_tenure.cause, TenureChangeCause::BlockFound);
    assert_eq!(highest_tenure.num_blocks_confirmed, 20);

    // replay the blocks and sortitions in random order, and verify that we still reach the chain
    // tip
    let mut replay_peer = make_replay_peer(&mut peer);
    replay_reward_cycle(&mut replay_peer, &rc_burn_ops, &all_blocks);

    let tip = {
        let chainstate = &mut replay_peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = replay_peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        41
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &blocks.last().unwrap().header
    );

    peer.check_nakamoto_migration();
    return peer;
}

#[test]
fn test_nakamoto_coordinator_2_tenures_3_sortitions() {
    simple_nakamoto_coordinator_2_tenures_3_sortitions();
}

/// Mine a 10 Nakamoto tenures with 10 Nakamoto blocks, but do a tenure-extend in each block
pub fn simple_nakamoto_coordinator_10_extended_tenures_10_sortitions() -> TestPeer<'static> {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    // make enough signers and signing keys so we can create a block and a malleablized block that
    // are both valid
    let (mut test_signers, test_stackers) = TestStacker::multi_signing_set(&[
        0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3,
    ]);
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        None,
    );

    let mut all_blocks: Vec<NakamotoBlock> = vec![];
    let mut all_burn_ops = vec![];
    let mut rc_blocks = vec![];
    let mut rc_burn_ops = vec![];
    let mut consensus_hashes = vec![];
    let mut fee_counts = vec![];
    let stx_miner_key = peer.miner.nakamoto_miner_key();

    for i in 0..10 {
        let (burn_ops, mut tenure_change, miner_key) =
            peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);
        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
        let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

        tenure_change.tenure_consensus_hash = consensus_hash.clone();
        tenure_change.burn_view_consensus_hash = consensus_hash.clone();

        let tenure_change_tx = peer
            .miner
            .make_nakamoto_tenure_change(tenure_change.clone());
        let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

        debug!("Next burnchain block: {}", &consensus_hash);

        let block_height = peer.get_burn_block_height();

        // do a stx transfer in each block to a given recipient
        let recipient_addr =
            StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();
        let blocks_and_sizes = peer.make_nakamoto_tenure(
            tenure_change_tx,
            coinbase_tx,
            &mut test_signers,
            |miner, chainstate, sortdb, blocks_so_far| {
                if blocks_so_far.len() < 10 {
                    let mut txs = vec![];

                    debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                    let account = get_account(chainstate, sortdb, &addr);

                    let stx_transfer = make_token_transfer(
                        chainstate,
                        sortdb,
                        &private_key,
                        account.nonce,
                        100,
                        1,
                        &recipient_addr,
                    );
                    txs.push(stx_transfer);

                    let last_block_opt = blocks_so_far
                        .last()
                        .as_ref()
                        .map(|(block, _size, _cost)| block.header.block_id());

                    let mut final_txs = vec![];
                    if let Some(last_block) = last_block_opt.as_ref() {
                        let tenure_extension = tenure_change.extend(
                            consensus_hash.clone(),
                            last_block.clone(),
                            blocks_so_far.len() as u32,
                        );
                        let tenure_extension_tx =
                            miner.make_nakamoto_tenure_change(tenure_extension);
                        final_txs.push(tenure_extension_tx);
                    }
                    final_txs.append(&mut txs);
                    final_txs
                } else {
                    vec![]
                }
            },
        );

        let fees = blocks_and_sizes
            .iter()
            .map(|(block, _, _)| {
                block
                    .txs
                    .iter()
                    .map(|tx| tx.get_tx_fee() as u128)
                    .sum::<u128>()
            })
            .sum::<u128>();

        consensus_hashes.push(consensus_hash);
        fee_counts.push(fees);
        let mut blocks: Vec<NakamotoBlock> = blocks_and_sizes
            .into_iter()
            .map(|(block, _, _)| block)
            .collect();

        // check that our tenure-extends have been getting applied
        let (highest_tenure, sort_tip) = {
            let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
            let sort_db = peer.sortdb.as_mut().unwrap();
            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let tenure = NakamotoChainState::get_ongoing_tenure(
                &mut chainstate.index_conn(),
                &sort_db
                    .index_handle_at_tip()
                    .get_nakamoto_tip_block_id()
                    .unwrap()
                    .unwrap(),
            )
            .unwrap()
            .unwrap();
            (tenure, tip)
        };

        let last_block = blocks.last().as_ref().cloned().unwrap();
        assert_eq!(
            highest_tenure.tenure_id_consensus_hash,
            last_block.header.consensus_hash
        );
        assert_eq!(
            highest_tenure.burn_view_consensus_hash,
            sort_tip.consensus_hash
        );
        assert!(last_block.header.consensus_hash == sort_tip.consensus_hash);
        assert_eq!(highest_tenure.coinbase_height, 12 + i);
        assert_eq!(highest_tenure.cause, TenureChangeCause::Extended);
        assert_eq!(
            highest_tenure.num_blocks_confirmed,
            (blocks.len() as u32) - 1
        );

        // if we're starting a new reward cycle, then save the current one
        let tip = {
            let sort_db = peer.sortdb.as_mut().unwrap();
            SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap()
        };
        if peer
            .config
            .burnchain
            .is_naka_signing_cycle_start(tip.block_height)
        {
            rc_blocks.push(all_blocks.clone());
            rc_burn_ops.push(all_burn_ops.clone());

            all_burn_ops.clear();
            all_blocks.clear();
        }

        all_blocks.append(&mut blocks);
        all_burn_ops.push(burn_ops);
    }

    rc_blocks.push(all_blocks.clone());
    rc_burn_ops.push(all_burn_ops.clone());

    // in nakamoto, tx fees are rewarded by the next tenure, so the
    // scheduled rewards come 1 tenure after the coinbase reward matures
    let miner = p2pkh_from(&stx_miner_key);
    let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
    let sort_db = peer.sortdb.as_mut().unwrap();

    // this is sortition height 12, and this miner has earned all 12 of the coinbases
    // plus the initial per-block mining bonus of 2600 STX, but minus the last three rewards (since
    // the miner rewards take three sortitions to confirm).
    //
    // This is (1000 + 2600) * 10 + 1000 - (3600 * 2 + 1000)
    //            first 10          block    unmatured rewards
    //            blocks             11
    let mut expected_coinbase_rewards: u128 = 28800000000;
    let mut fees_so_far: u128 = 0;
    for (i, ch) in consensus_hashes.into_iter().enumerate() {
        let sn = SortitionDB::get_block_snapshot_consensus(sort_db.conn(), &ch)
            .unwrap()
            .unwrap();

        if !sn.sortition {
            continue;
        }
        let block_id = StacksBlockId(sn.winning_stacks_block_hash.0);

        let (chainstate_tx, clarity_instance) = chainstate.chainstate_tx_begin().unwrap();
        let sort_db_tx = sort_db.tx_begin_at_tip();

        let stx_balance = clarity_instance
            .read_only_connection(&block_id, &chainstate_tx, &sort_db_tx)
            .with_clarity_db_readonly(|db| db.get_account_stx_balance(&miner.clone().into()))
            .unwrap();

        // it's 1 * 10 because it's 1 uSTX per token-transfer, and 10 per tenure
        let block_fee = if i > 3 {
            fee_counts[i.saturating_sub(4)]
        } else {
            0
        };
        let expected_total_tx_fees = fees_so_far + block_fee;
        let expected_total_coinbase = expected_coinbase_rewards;
        fees_so_far += block_fee;

        if i == 0 {
            // first tenure awards the last of the initial mining bonus
            expected_coinbase_rewards += (1000 + 2600) * 1000000;
        } else {
            // subsequent tenures award normal coinbases
            expected_coinbase_rewards += 1000 * 1000000;
        }

        eprintln!(
            "Checking block #{} ({},{}): {} =?= {} + {}",
            i,
            &ch,
            &sn.block_height,
            stx_balance.amount_unlocked(),
            expected_total_coinbase,
            expected_total_tx_fees
        );
        assert_eq!(
            stx_balance.amount_unlocked(),
            expected_total_coinbase + expected_total_tx_fees
        );
    }

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        111
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &rc_blocks.last().unwrap().last().unwrap().header
    );

    // replay the blocks and sortitions in random order, and verify that we still reach the chain
    // tip
    let mut replay_peer = make_replay_peer(&mut peer);
    for (burn_ops, blocks) in rc_burn_ops.iter().zip(rc_blocks.iter()) {
        replay_reward_cycle(&mut replay_peer, burn_ops, blocks);
    }

    let tip = {
        let chainstate = &mut replay_peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = replay_peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        111
    );
    assert_eq!(
        tip.anchored_header.as_stacks_nakamoto().unwrap(),
        &rc_blocks.last().unwrap().last().unwrap().header
    );

    peer.check_nakamoto_migration();
    peer.check_malleablized_blocks(all_blocks, 2);
    return peer;
}

#[test]
fn test_nakamoto_coordinator_10_tenures_and_extensions_10_blocks() {
    simple_nakamoto_coordinator_10_extended_tenures_10_sortitions();
}

#[test]
fn process_next_nakamoto_block_deadlock() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::p2pkh(false, &StacksPublicKey::from_private(&private_key));

    let num_stackers: u32 = 4;
    let mut signing_key_seed = num_stackers.to_be_bytes().to_vec();
    signing_key_seed.extend_from_slice(&[1, 1, 1, 1]);
    let signing_key = StacksPrivateKey::from_seed(signing_key_seed.as_slice());
    let test_stackers = (0..num_stackers)
        .map(|index| TestStacker {
            signer_private_key: signing_key.clone(),
            stacker_private_key: StacksPrivateKey::from_seed(&index.to_be_bytes()),
            amount: u64::MAX as u128 - 10000,
            pox_addr: Some(PoxAddress::Standard(
                StacksAddress::new(
                    C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                    Hash160::from_data(&index.to_be_bytes()),
                )
                .unwrap(),
                Some(AddressHashMode::SerializeP2PKH),
            )),
            max_amount: None,
        })
        .collect::<Vec<_>>();
    let test_signers = TestSigners::new(vec![signing_key]);
    let mut pox_constants = TestPeerConfig::default().burnchain.pox_constants;
    pox_constants.reward_cycle_length = 10;
    pox_constants.v2_unlock_height = 21;
    pox_constants.pox_3_activation_height = 26;
    pox_constants.v3_unlock_height = 27;
    pox_constants.pox_4_activation_height = 28;

    let mut boot_plan = NakamotoBootPlan::new(function_name!())
        .with_test_stackers(test_stackers)
        .with_test_signers(test_signers)
        .with_private_key(private_key);
    boot_plan.pox_constants = pox_constants;

    info!("Creating peer");

    let mut peer = boot_plan.boot_into_nakamoto_peer(vec![], None);
    let mut sortition_db = peer.sortdb().reopen().unwrap();
    let (chainstate, _) = &mut peer
        .stacks_node
        .as_mut()
        .unwrap()
        .chainstate
        .reopen()
        .unwrap();

    enable_process_block_stall();

    let miner_thread = std::thread::spawn(move || {
        info!("  -------------------------------   MINING TENURE");
        let (block, burn_height, ..) =
            peer.single_block_tenure(&private_key, |_| {}, |_| {}, |_| true);
        info!("  -------------------------------   TENURE MINED");
    });

    // Wait a bit, to ensure the miner has reached the stall
    std::thread::sleep(std::time::Duration::from_secs(10));

    // Lock the sortdb
    info!("  -------------------------------   TRYING TO LOCK THE SORTDB");
    let sort_tx = sortition_db.tx_begin().unwrap();
    info!("  -------------------------------   SORTDB LOCKED");

    // Un-stall the block processing
    disable_process_block_stall();

    // Wait a bit, to ensure the tenure will have grabbed any locks it needs
    std::thread::sleep(std::time::Duration::from_secs(10));

    // Lock the chainstate db
    info!("  -------------------------------   TRYING TO LOCK THE CHAINSTATE");
    let chainstate_tx = chainstate.chainstate_tx_begin().unwrap();

    info!("  -------------------------------   SORTDB AND CHAINSTATE LOCKED");
    drop(chainstate_tx);
    drop(sort_tx);
    info!("  -------------------------------   MAIN THREAD FINISHED");

    // Wait for the blocker and miner threads to finish
    miner_thread.join().unwrap();
}

/// Test stacks-on-burnchain op discovery and usage
#[test]
fn test_stacks_on_burnchain_ops() {
    let private_key = StacksPrivateKey::from_seed(&[2]);
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&private_key)],
    )
    .unwrap();

    let recipient_private_key = StacksPrivateKey::from_seed(&[3]);
    let recipient_addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&recipient_private_key)],
    )
    .unwrap();

    let agg_private_key = StacksPrivateKey::from_seed(&[4]);
    let agg_addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&agg_private_key)],
    )
    .unwrap();

    // make enough signers and signing keys so we can create a block and a malleablized block that
    // are both valid
    let (mut test_signers, test_stackers) = TestStacker::multi_signing_set(&[
        0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3,
    ]);
    let observer = TestEventObserver::new();
    let mut peer = boot_nakamoto(
        function_name!(),
        vec![(addr.into(), 100_000_000)],
        &mut test_signers,
        &test_stackers,
        Some(&observer),
    );

    let mut all_blocks: Vec<NakamotoBlock> = vec![];
    let stx_miner_key = peer.miner.nakamoto_miner_key();

    let mut extra_burn_ops = vec![];
    let mut bitpatterns = HashMap::new(); // map consensus hash to txid bit pattern

    let cur_reward_cycle = peer
        .config
        .burnchain
        .block_height_to_reward_cycle(peer.get_burn_block_height())
        .unwrap();

    peer.refresh_burnchain_view();
    let first_stacks_height = peer.network.stacks_tip.height;

    for i in 0..10 {
        peer.refresh_burnchain_view();
        let block_height = peer.get_burn_block_height();

        // parent tip
        let stacks_tip_ch = peer.network.stacks_tip.consensus_hash.clone();
        let stacks_tip_bh = peer.network.stacks_tip.block_hash.clone();

        let (mut burn_ops, mut tenure_change, miner_key) =
            peer.begin_nakamoto_tenure(TenureChangeCause::BlockFound);

        let mut new_burn_ops = vec![
            BlockstackOperationType::DelegateStx(DelegateStxOp {
                sender: addr.clone(),
                delegate_to: recipient_addr.clone(),
                reward_addr: None,
                delegated_ustx: 1,
                until_burn_height: None,

                // mocked
                txid: Txid([i; 32]),
                vtxindex: 11,
                block_height: block_height + 1,
                burn_header_hash: BurnchainHeaderHash([0x00; 32]),
            }),
            BlockstackOperationType::StackStx(StackStxOp {
                sender: addr.clone(),
                reward_addr: PoxAddress::Standard(
                    recipient_addr.clone(),
                    Some(AddressHashMode::SerializeP2PKH),
                ),
                stacked_ustx: 1,
                num_cycles: 1,
                signer_key: Some(StacksPublicKeyBuffer::from_public_key(
                    &StacksPublicKey::from_private(&recipient_private_key),
                )),
                max_amount: Some(1),
                auth_id: Some(i as u32),

                // mocked
                txid: Txid([i | 0x80; 32]),
                vtxindex: 12,
                block_height: block_height + 1,
                burn_header_hash: BurnchainHeaderHash([0x00; 32]),
            }),
            BlockstackOperationType::TransferStx(TransferStxOp {
                sender: addr.clone(),
                recipient: recipient_addr.clone(),
                transfered_ustx: 1,
                memo: vec![0x2],

                // mocked
                txid: Txid([i | 0x40; 32]),
                vtxindex: 13,
                block_height: block_height + 1,
                burn_header_hash: BurnchainHeaderHash([0x00; 32]),
            }),
            BlockstackOperationType::VoteForAggregateKey(VoteForAggregateKeyOp {
                sender: addr.clone(),
                aggregate_key: StacksPublicKeyBuffer::from_public_key(
                    &StacksPublicKey::from_private(&agg_private_key),
                ),
                round: i as u32,
                reward_cycle: cur_reward_cycle + 1,
                signer_index: 1,
                signer_key: StacksPublicKeyBuffer::from_public_key(&StacksPublicKey::from_private(
                    &recipient_private_key,
                )),

                // mocked
                txid: Txid([i | 0xc0; 32]),
                vtxindex: 14,
                block_height: block_height + 1,
                burn_header_hash: BurnchainHeaderHash([0x00; 32]),
            }),
        ];

        extra_burn_ops.push(new_burn_ops.clone());
        burn_ops.append(&mut new_burn_ops);

        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
        let vrf_proof = peer.make_nakamoto_vrf_proof(miner_key);

        bitpatterns.insert(consensus_hash.clone(), i);

        tenure_change.tenure_consensus_hash = consensus_hash.clone();
        tenure_change.burn_view_consensus_hash = consensus_hash.clone();

        let tenure_change_tx = peer
            .miner
            .make_nakamoto_tenure_change(tenure_change.clone());
        let coinbase_tx = peer.miner.make_nakamoto_coinbase(None, vrf_proof);

        debug!("Next burnchain block: {}", &consensus_hash);

        // make sure all our burnchain ops are processed and stored.
        let burn_tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb().conn()).unwrap();
        let ancestor_burnchain_header_hashes = SortitionDB::get_ancestor_burnchain_header_hashes(
            peer.sortdb().conn(),
            &burn_tip.burn_header_hash,
            6,
        )
        .unwrap();
        let processed_burnchain_txids =
            NakamotoChainState::get_burnchain_txids_in_ancestor_tenures(
                &mut peer.chainstate().index_conn(),
                &stacks_tip_ch,
                &stacks_tip_bh,
                6,
            )
            .unwrap();

        let mut expected_burnchain_txids = HashSet::new();
        for j in i.saturating_sub(6)..i {
            expected_burnchain_txids.insert(Txid([j; 32]));
            expected_burnchain_txids.insert(Txid([j | 0x80; 32]));
            expected_burnchain_txids.insert(Txid([j | 0x40; 32]));
            expected_burnchain_txids.insert(Txid([j | 0xc0; 32]));
        }
        assert_eq!(processed_burnchain_txids, expected_burnchain_txids);

        // do a stx transfer in each block to a given recipient
        let recipient_addr =
            StacksAddress::from_string("ST2YM3J4KQK09V670TD6ZZ1XYNYCNGCWCVTASN5VM").unwrap();
        let blocks_and_sizes = peer.make_nakamoto_tenure(
            tenure_change_tx,
            coinbase_tx,
            &mut test_signers,
            |miner, chainstate, sortdb, blocks_so_far| {
                if blocks_so_far.len() < 10 {
                    let mut txs = vec![];

                    debug!("\n\nProduce block {}\n\n", blocks_so_far.len());

                    let account = get_account(chainstate, sortdb, &addr);

                    let stx_transfer = make_token_transfer(
                        chainstate,
                        sortdb,
                        &private_key,
                        account.nonce,
                        100,
                        1,
                        &recipient_addr,
                    );
                    txs.push(stx_transfer);

                    let last_block_opt = blocks_so_far
                        .last()
                        .as_ref()
                        .map(|(block, _size, _cost)| block.header.block_id());

                    let mut final_txs = vec![];
                    if let Some(last_block) = last_block_opt.as_ref() {
                        let tenure_extension = tenure_change.extend(
                            consensus_hash.clone(),
                            last_block.clone(),
                            blocks_so_far.len() as u32,
                        );
                        let tenure_extension_tx =
                            miner.make_nakamoto_tenure_change(tenure_extension);
                        final_txs.push(tenure_extension_tx);
                    }
                    final_txs.append(&mut txs);
                    final_txs
                } else {
                    vec![]
                }
            },
        );

        let fees = blocks_and_sizes
            .iter()
            .map(|(block, _, _)| {
                block
                    .txs
                    .iter()
                    .map(|tx| tx.get_tx_fee() as u128)
                    .sum::<u128>()
            })
            .sum::<u128>();

        let mut blocks: Vec<NakamotoBlock> = blocks_and_sizes
            .into_iter()
            .map(|(block, _, _)| block)
            .collect();

        // check that our tenure-extends have been getting applied
        let (highest_tenure, sort_tip) = {
            let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
            let sort_db = peer.sortdb.as_mut().unwrap();
            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let tenure = NakamotoChainState::get_ongoing_tenure(
                &mut chainstate.index_conn(),
                &sort_db
                    .index_handle_at_tip()
                    .get_nakamoto_tip_block_id()
                    .unwrap()
                    .unwrap(),
            )
            .unwrap()
            .unwrap();
            (tenure, tip)
        };

        let last_block = blocks.last().as_ref().cloned().unwrap();
        assert_eq!(
            highest_tenure.tenure_id_consensus_hash,
            last_block.header.consensus_hash
        );
        assert_eq!(
            highest_tenure.burn_view_consensus_hash,
            sort_tip.consensus_hash
        );
        assert!(last_block.header.consensus_hash == sort_tip.consensus_hash);
        assert_eq!(highest_tenure.coinbase_height, 12 + u64::from(i));
        assert_eq!(highest_tenure.cause, TenureChangeCause::Extended);
        assert_eq!(
            highest_tenure.num_blocks_confirmed,
            (blocks.len() as u32) - 1
        );

        all_blocks.append(&mut blocks);
    }

    // check receipts for burn ops
    let mut observed_burn_txids = HashSet::new();
    let observed_blocks = observer.get_blocks();
    for block in observed_blocks.into_iter() {
        let block_height = block.metadata.anchored_header.height();
        if block_height < first_stacks_height {
            continue;
        }

        let mut is_tenure_start = false;
        let mut block_burn_txids = HashSet::new();
        for receipt in block.receipts.into_iter() {
            match receipt.transaction {
                TransactionOrigin::Burn(op) => {
                    block_burn_txids.insert(op.txid().clone());
                }
                TransactionOrigin::Stacks(tx) => {
                    if let TransactionPayload::TenureChange(txp) = &tx.payload {
                        if txp.cause == TenureChangeCause::BlockFound {
                            is_tenure_start = true;
                        }
                    }
                }
            }
        }

        // no burnchain blocks processed for non-tenure-start blocks
        if !is_tenure_start {
            assert!(block_burn_txids.is_empty());
            continue;
        }

        // this tenure-start block only processed "new" burnchain ops
        let mut expected_burnchain_txids = HashSet::new();
        let bitpattern = *bitpatterns.get(&block.metadata.consensus_hash).unwrap();
        expected_burnchain_txids.insert(Txid([bitpattern; 32]));
        expected_burnchain_txids.insert(Txid([bitpattern | 0x80; 32]));
        expected_burnchain_txids.insert(Txid([bitpattern | 0x40; 32]));
        expected_burnchain_txids.insert(Txid([bitpattern | 0xc0; 32]));

        debug!("At block {}: {:?}", block_height, &block_burn_txids);
        debug!("Expected: {:?}", &expected_burnchain_txids);
        assert_eq!(block_burn_txids, expected_burnchain_txids);

        observed_burn_txids.extend(block_burn_txids.into_iter());
    }

    // all extra burn ops are represented
    for extra_burn_ops_per_block in extra_burn_ops.into_iter() {
        for extra_burn_op in extra_burn_ops_per_block.into_iter() {
            assert!(observed_burn_txids.contains(&extra_burn_op.txid()));
        }
    }

    let tip = {
        let chainstate = &mut peer.stacks_node.as_mut().unwrap().chainstate;
        let sort_db = peer.sortdb.as_mut().unwrap();
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sort_db)
            .unwrap()
            .unwrap()
    };

    assert_eq!(
        tip.anchored_header
            .as_stacks_nakamoto()
            .unwrap()
            .chain_length,
        111
    );

    peer.check_nakamoto_migration();
    peer.check_malleablized_blocks(all_blocks, 2);
}
