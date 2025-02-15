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

/// This test module is concerned with testing the behaviors of fees and block rewards under
/// various conditions, such as ensuring that the right principals get paid and ensuring that fees
/// are appropriately distributed.
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::{fs, io};

use clarity::vm::clarity::ClarityConnection;
use clarity::vm::costs::LimitedCostTracker;
use clarity::vm::types::*;
use rand::seq::SliceRandom;
use rand::{thread_rng, Rng};
use stacks_common::address::*;
use stacks_common::types::chainstate::SortitionId;
use stacks_common::util::hash::MerkleTree;
use stacks_common::util::sleep_ms;
use stacks_common::util::vrf::VRFProof;

use crate::burnchains::tests::*;
use crate::burnchains::*;
use crate::chainstate::burn::db::sortdb::*;
use crate::chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp,
};
use crate::chainstate::burn::*;
use crate::chainstate::coordinator::Error as CoordinatorError;
use crate::chainstate::stacks::db::blocks::test::store_staging_block;
use crate::chainstate::stacks::db::test::*;
use crate::chainstate::stacks::db::*;
use crate::chainstate::stacks::miner::*;
use crate::chainstate::stacks::tests::*;
use crate::chainstate::stacks::{
    Error as ChainstateError, C32_ADDRESS_VERSION_TESTNET_SINGLESIG, *,
};
use crate::core::*;
use crate::cost_estimates::metrics::UnitMetric;
use crate::cost_estimates::UnitEstimator;
use crate::net::test::*;
use crate::util_lib::boot::boot_code_addr;
use crate::util_lib::db::Error as db_error;

// test that the bad (pre 2.1) microblock fee payment still works.  we have to support it for
// eternity :(
#[test]
fn test_bad_microblock_fees_pre_v210() {
    let privk = StacksPrivateKey::from_hex(
        "42faca653724860da7a41bfcef7e6ba78db55146f6900de8cb2a9f760ffac70c01",
    )
    .unwrap();
    let privk_anchored = StacksPrivateKey::from_hex(
        "f67c7437f948ca1834602b28595c12ac744f287a4efaf70d437042a6afed81bc01",
    )
    .unwrap();

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();

    let addr_anchored = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_anchored)],
    )
    .unwrap();

    let mut peer_config = TestPeerConfig::new(function_name!(), 2018, 2019);
    peer_config.initial_balances = vec![
        (addr.to_account_principal(), 1000000000),
        (addr_anchored.to_account_principal(), 1000000000),
    ];

    let epochs = EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: STACKS_EPOCH_MAX,
            block_limit: ExecutionCost {
                write_length: 205205,
                write_count: 205205,
                read_length: 205205,
                read_count: 205205,
                runtime: 205205,
            },
            network_epoch: PEER_VERSION_EPOCH_2_05,
        },
    ]);
    peer_config.epochs = Some(epochs);
    let burnchain = peer_config.burnchain.clone();

    let num_blocks = 10;
    let mut anchored_sender_nonce = 0;

    let mut mblock_privks = vec![];
    for _ in 0..num_blocks {
        let mblock_privk = StacksPrivateKey::random();
        mblock_privks.push(mblock_privk);
    }

    let mut peer = TestPeer::new(peer_config);

    let chainstate_path = peer.chainstate_path.clone();

    let first_stacks_block_height = {
        let sn = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();
        sn.block_height
    };

    let recipient_addr_str = "ST1RFD5Q2QPK3E0F08HG9XDX7SSC7CNRS0QR0SGEV";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    let mut block_ids = vec![];
    for tenure_id in 0..num_blocks {
        // send transactions to the mempool
        let tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();

        let acct = get_stacks_account(&mut peer, &addr.to_account_principal());

        let (mut burn_ops, stacks_block, microblocks) = peer.make_tenure(
            |ref mut miner,
             ref mut sortdb,
             ref mut chainstate,
             vrf_proof,
             ref parent_opt,
             ref parent_microblock_header_opt| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &block.block_hash(),
                        )
                        .unwrap()
                        .unwrap(); // succeeds because we don't fork
                        StacksChainState::get_anchored_block_header_info(
                            chainstate.db(),
                            &snapshot.consensus_hash,
                            &snapshot.winning_stacks_block_hash,
                        )
                        .unwrap()
                        .unwrap()
                    }
                };

                let parent_header_hash = parent_tip.anchored_header.block_hash();
                let parent_consensus_hash = parent_tip.consensus_hash.clone();
                let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_header_hash,
                );

                let coinbase_tx =
                    // alternate between the miner and a random key, so you can look at the DBs
                    // and logs and see that the parent miner gets the produced streamed tx
                    // fees and the child miner gets the confirmed streamed tx fees.
                    if tenure_id % 2 == 0 {
                        make_coinbase(miner, tenure_id / 2)
                    }
                    else {
                        let pk = StacksPrivateKey::random();
                        let mut tx_coinbase = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            TransactionAuth::from_p2pkh(&pk).unwrap(),
                            TransactionPayload::Coinbase(CoinbasePayload([0x00; 32]), None, None),
                        );
                        tx_coinbase.chain_id = 0x80000000;
                        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
                        tx_coinbase.auth.set_origin_nonce(0);

                        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
                        tx_signer.sign_origin(&pk).unwrap();
                        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
                        tx_coinbase_signed
                    };

                let mut anchored_txs = vec![coinbase_tx];

                // send an anchored tx
                if tenure_id > 0 {
                    let fee = 2000 + (1000 * tenure_id as u64);
                    let stx_transfer = make_user_stacks_transfer(
                        &privk_anchored,
                        anchored_sender_nonce,
                        fee,
                        &recipient.to_account_principal(),
                        1,
                    );
                    anchored_sender_nonce += 1;
                    anchored_txs.push(stx_transfer);
                }

                let sort_ic = sortdb.index_handle_at_tip();
                let (parent_mblock_stream, mblock_pubkey_hash) = {
                    if tenure_id > 0 {
                        chainstate
                            .reload_unconfirmed_state(&sort_ic, parent_index_hash.clone())
                            .unwrap();

                        let parent_microblock_privkey = mblock_privks[tenure_id - 1].clone();
                        // produce the microblock stream for the parent, which this tenure's anchor
                        // block will confirm.
                        let mut microblock_builder = StacksMicroblockBuilder::new(
                            parent_header_hash.clone(),
                            parent_consensus_hash.clone(),
                            chainstate,
                            &sort_ic,
                            BlockBuilderSettings::max_value(),
                        )
                        .unwrap();

                        let mut microblocks = vec![];

                        // different fee each time
                        let fee = 200 + (100 * tenure_id as u64);
                        let mblock_tx = make_user_stacks_transfer(
                            &privk,
                            acct.nonce,
                            fee,
                            &recipient.to_account_principal(),
                            1,
                        );

                        let mblock_tx_len = {
                            let mut bytes = vec![];
                            mblock_tx.consensus_serialize(&mut bytes).unwrap();
                            bytes.len() as u64
                        };

                        test_debug!(
                            "Make microblock parent stream for block in tenure {}",
                            tenure_id
                        );
                        let mblock = microblock_builder
                            .mine_next_microblock_from_txs(
                                vec![(mblock_tx, mblock_tx_len)],
                                &parent_microblock_privkey,
                            )
                            .unwrap();
                        microblocks.push(mblock);

                        let microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&microblock_privkey),
                        );
                        (microblocks, mblock_pubkey_hash)
                    } else {
                        let parent_microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&parent_microblock_privkey),
                        );
                        (vec![], mblock_pubkey_hash)
                    }
                };

                test_debug!("Store parent microblocks for tenure {}", tenure_id);
                for mblock in parent_mblock_stream.iter() {
                    let stored = chainstate
                        .preprocess_streamed_microblock(
                            &parent_consensus_hash,
                            &parent_header_hash,
                            mblock,
                        )
                        .unwrap();
                    assert!(stored);
                }

                let builder = StacksBlockBuilder::make_block_builder(
                    &burnchain,
                    chainstate.mainnet,
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    mblock_pubkey_hash,
                )
                .unwrap();

                let anchored_block = StacksBlockBuilder::make_anchored_block_from_txs(
                    builder,
                    chainstate,
                    &sort_ic,
                    anchored_txs,
                )
                .unwrap();

                // coinbase
                (anchored_block.0, parent_mblock_stream)
            },
        );

        test_debug!("Process tenure {}", tenure_id);

        // make each block-commit unique
        for burn_op in burn_ops.iter_mut() {
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = burn_op {
                op.burn_fee += tenure_id as u64;
            }
        }

        // should always succeed
        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
        peer.process_stacks_epoch_at_tip_checked(&stacks_block, &[])
            .unwrap();

        block_ids.push(StacksBlockHeader::make_index_block_hash(
            &consensus_hash,
            &stacks_block.block_hash(),
        ));
    }

    // derived from manual inspection of the chainstate, without the fix applied
    let expected_rewards: Vec<u128> = vec![
        3600003000, 3600004240, 3600005460, 3600006560, 3600007660, 3600008760,
    ];

    for i in 1..num_blocks {
        let parent_block_id = block_ids[i - 1].clone();
        let block_id = block_ids[i].clone();

        let matured_reward_opt = StacksChainState::get_matured_miner_payment(
            peer.chainstate().db(),
            &parent_block_id.into(),
            &block_id.into(),
        )
        .unwrap();

        if i > 0 && i < num_blocks - (MINER_REWARD_MATURITY as usize) - 1 {
            // expect a reward
            let matured_reward = matured_reward_opt.unwrap();
            eprintln!("total = {}", matured_reward.total());
            assert_eq!(expected_rewards[i - 1], matured_reward.total());
        } else {
            assert!(matured_reward_opt.is_none());
        }
    }
}

// test the transition to epoch 2.1 with the fixed microblock fees
#[test]
fn test_bad_microblock_fees_fix_transition() {
    let privk = StacksPrivateKey::from_hex(
        "42faca653724860da7a41bfcef7e6ba78db55146f6900de8cb2a9f760ffac70c01",
    )
    .unwrap();
    let privk_anchored = StacksPrivateKey::from_hex(
        "f67c7437f948ca1834602b28595c12ac744f287a4efaf70d437042a6afed81bc01",
    )
    .unwrap();

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();

    let addr_anchored = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_anchored)],
    )
    .unwrap();

    let mut peer_config = TestPeerConfig::new(function_name!(), 2020, 2021);
    peer_config.initial_balances = vec![
        (addr.to_account_principal(), 1000000000),
        (addr_anchored.to_account_principal(), 1000000000),
    ];
    let burnchain = peer_config.burnchain.clone();

    let epochs = EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 30,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 30,
            end_height: STACKS_EPOCH_MAX,
            block_limit: ExecutionCost {
                write_length: 205205,
                write_count: 205205,
                read_length: 205205,
                read_count: 205205,
                runtime: 205205,
            },
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]);
    peer_config.epochs = Some(epochs);

    let num_blocks = 10;
    let mut anchored_sender_nonce = 0;

    let mut mblock_privks = vec![];
    for _ in 0..num_blocks {
        let mblock_privk = StacksPrivateKey::random();
        mblock_privks.push(mblock_privk);
    }

    let mut peer = TestPeer::new(peer_config);

    let chainstate_path = peer.chainstate_path.clone();

    let first_stacks_block_height = {
        let sn = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();
        sn.block_height
    };

    let recipient_addr_str = "ST1RFD5Q2QPK3E0F08HG9XDX7SSC7CNRS0QR0SGEV";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    let mut block_ids = vec![];
    for tenure_id in 0..num_blocks {
        // send transactions to the mempool
        let tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();

        let acct = get_stacks_account(&mut peer, &addr.to_account_principal());

        let (mut burn_ops, stacks_block, microblocks) = peer.make_tenure(
            |ref mut miner,
             ref mut sortdb,
             ref mut chainstate,
             vrf_proof,
             ref parent_opt,
             ref parent_microblock_header_opt| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &block.block_hash(),
                        )
                        .unwrap()
                        .unwrap(); // succeeds because we don't fork
                        StacksChainState::get_anchored_block_header_info(
                            chainstate.db(),
                            &snapshot.consensus_hash,
                            &snapshot.winning_stacks_block_hash,
                        )
                        .unwrap()
                        .unwrap()
                    }
                };

                let parent_header_hash = parent_tip.anchored_header.block_hash();
                let parent_consensus_hash = parent_tip.consensus_hash.clone();
                let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_header_hash,
                );

                let coinbase_tx =
                    // alternate between the miner and a random key, so you can look at the DBs
                    // and logs and see that the parent miner gets the produced streamed tx
                    // fees and the child miner gets the confirmed streamed tx fees.
                    if tenure_id % 2 == 0 {
                        make_coinbase(miner, tenure_id / 2)
                    }
                    else {
                        let pk = StacksPrivateKey::random();
                        let mut tx_coinbase = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            TransactionAuth::from_p2pkh(&pk).unwrap(),
                            TransactionPayload::Coinbase(CoinbasePayload([0x00; 32]), None, None),
                        );
                        tx_coinbase.chain_id = 0x80000000;
                        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
                        tx_coinbase.auth.set_origin_nonce(0);

                        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
                        tx_signer.sign_origin(&pk).unwrap();
                        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
                        tx_coinbase_signed
                    };

                let mut anchored_txs = vec![coinbase_tx];

                // send an anchored tx
                if tenure_id > 0 {
                    let fee = 2000 + (1000 * tenure_id as u64);
                    let stx_transfer = make_user_stacks_transfer(
                        &privk_anchored,
                        anchored_sender_nonce,
                        fee,
                        &recipient.to_account_principal(),
                        1,
                    );
                    anchored_sender_nonce += 1;
                    anchored_txs.push(stx_transfer);
                }

                let sort_ic = sortdb.index_handle_at_tip();
                let (parent_mblock_stream, mblock_pubkey_hash) = {
                    if tenure_id > 0 {
                        chainstate
                            .reload_unconfirmed_state(&sort_ic, parent_index_hash.clone())
                            .unwrap();

                        let parent_microblock_privkey = mblock_privks[tenure_id - 1].clone();
                        // produce the microblock stream for the parent, which this tenure's anchor
                        // block will confirm.
                        let mut microblock_builder = StacksMicroblockBuilder::new(
                            parent_header_hash.clone(),
                            parent_consensus_hash.clone(),
                            chainstate,
                            &sort_ic,
                            BlockBuilderSettings::max_value(),
                        )
                        .unwrap();

                        let mut microblocks = vec![];

                        // different fee each time
                        let fee = 200 + (100 * tenure_id as u64);
                        let mblock_tx = make_user_stacks_transfer(
                            &privk,
                            acct.nonce,
                            fee,
                            &recipient.to_account_principal(),
                            1,
                        );

                        let mblock_tx_len = {
                            let mut bytes = vec![];
                            mblock_tx.consensus_serialize(&mut bytes).unwrap();
                            bytes.len() as u64
                        };

                        test_debug!(
                            "Make microblock parent stream for block in tenure {}",
                            tenure_id
                        );
                        let mblock = microblock_builder
                            .mine_next_microblock_from_txs(
                                vec![(mblock_tx, mblock_tx_len)],
                                &parent_microblock_privkey,
                            )
                            .unwrap();
                        microblocks.push(mblock);

                        let microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&microblock_privkey),
                        );
                        (microblocks, mblock_pubkey_hash)
                    } else {
                        let parent_microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&parent_microblock_privkey),
                        );
                        (vec![], mblock_pubkey_hash)
                    }
                };

                test_debug!("Store parent microblocks for tenure {}", tenure_id);
                for mblock in parent_mblock_stream.iter() {
                    let stored = chainstate
                        .preprocess_streamed_microblock(
                            &parent_consensus_hash,
                            &parent_header_hash,
                            mblock,
                        )
                        .unwrap();
                    assert!(stored);
                }

                let builder = StacksBlockBuilder::make_block_builder(
                    &burnchain,
                    chainstate.mainnet,
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    mblock_pubkey_hash,
                )
                .unwrap();

                let anchored_block = StacksBlockBuilder::make_anchored_block_from_txs(
                    builder,
                    chainstate,
                    &sort_ic,
                    anchored_txs,
                )
                .unwrap();

                // coinbase
                (anchored_block.0, parent_mblock_stream)
            },
        );

        test_debug!("Process tenure {}", tenure_id);

        // make each block-commit unique
        for burn_op in burn_ops.iter_mut() {
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = burn_op {
                op.burn_fee += tenure_id as u64;
            }
        }

        // should always succeed
        let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
        peer.process_stacks_epoch_at_tip_checked(&stacks_block, &[])
            .unwrap();

        block_ids.push(StacksBlockHeader::make_index_block_hash(
            &consensus_hash,
            &stacks_block.block_hash(),
        ));
    }

    // derived from manual inspection of the chainstate, without the fix applied
    let bad_expected_rewards: Vec<u128> = vec![
        3600003000, 3600004240, 3600005460, 3600006560, 3600007660, 3600008760,
    ];

    for i in 1..num_blocks {
        let parent_block_id = block_ids[i - 1].clone();
        let block_id = block_ids[i].clone();

        let matured_reward_opt = StacksChainState::get_matured_miner_payment(
            peer.chainstate().db(),
            &parent_block_id.into(),
            &block_id.into(),
        )
        .unwrap();

        if i < num_blocks - (MINER_REWARD_MATURITY as usize) - 1 {
            // expect a reward
            let matured_reward = matured_reward_opt.unwrap();

            let good_expected_reward = {
                let coinbase = 3600000000;
                let tx_fees_anchored = if i > 1 { 2000 + 1000 * i as u128 } else { 0 };
                let tx_fees_streamed_produced = if i > 2 {
                    (2 * (200 + 100 * i) / 5) as u128
                } else {
                    0
                };
                let tx_fees_streamed_confirmed = if i > 2 {
                    (3 * (200 + 100 * i) / 5) as u128
                } else {
                    0
                };

                coinbase + tx_fees_anchored + tx_fees_streamed_produced + tx_fees_streamed_confirmed
            };

            let expected_reward = match i.cmp(&5) {
                Ordering::Less => bad_expected_rewards[i - 1],
                Ordering::Equal => {
                    // epoch transition boundary, so no microblock reward at all
                    3600000000 + (2000 + 1000 * i as u128)
                }
                Ordering::Greater => good_expected_reward,
            };

            eprintln!(
                "i = {i}, {block_id}, total = {t}, good = {good_expected_reward}, bad = {b}, expected = {expected_reward}",
                t=matured_reward.total(),
                b=bad_expected_rewards[i - 1],
            );
            assert_eq!(expected_reward, matured_reward.total());
        } else {
            assert!(matured_reward_opt.is_none());
        }
    }
}

#[test]
fn test_get_block_info_v210() {
    let privk = StacksPrivateKey::from_hex(
        "42faca653724860da7a41bfcef7e6ba78db55146f6900de8cb2a9f760ffac70c01",
    )
    .unwrap();
    let privk_anchored = StacksPrivateKey::from_hex(
        "f67c7437f948ca1834602b28595c12ac744f287a4efaf70d437042a6afed81bc01",
    )
    .unwrap();

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();

    let addr_anchored = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_anchored)],
    )
    .unwrap();

    let mut peer_config = TestPeerConfig::new(function_name!(), 2022, 2023);
    peer_config.initial_balances = vec![
        (addr.to_account_principal(), 1000000000),
        (addr_anchored.to_account_principal(), 1000000000),
    ];
    let burnchain = peer_config.burnchain.clone();

    let epochs = EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2, // effectively already in 2.1
            end_height: STACKS_EPOCH_MAX,
            block_limit: ExecutionCost {
                write_length: 205205,
                write_count: 205205,
                read_length: 205205,
                read_count: 205205,
                runtime: 205205,
            },
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]);
    peer_config.epochs = Some(epochs);

    let num_blocks = 10;
    let mut anchored_sender_nonce = 0;

    let mut mblock_privks = vec![];
    for _ in 0..num_blocks {
        let mblock_privk = StacksPrivateKey::random();
        mblock_privks.push(mblock_privk);
    }

    let mut peer = TestPeer::new(peer_config);

    let chainstate_path = peer.chainstate_path.clone();

    let first_stacks_block_height = {
        let sn = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();
        sn.block_height
    };

    let recipient_addr_str = "ST1RFD5Q2QPK3E0F08HG9XDX7SSC7CNRS0QR0SGEV";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    for tenure_id in 0..num_blocks {
        // send transactions to the mempool
        let tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();

        let acct = get_stacks_account(&mut peer, &addr.to_account_principal());

        let (mut burn_ops, stacks_block, microblocks) = peer.make_tenure(
            |ref mut miner,
             ref mut sortdb,
             ref mut chainstate,
             vrf_proof,
             ref parent_opt,
             ref parent_microblock_header_opt| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &block.block_hash(),
                        )
                        .unwrap()
                        .unwrap(); // succeeds because we don't fork
                        StacksChainState::get_anchored_block_header_info(
                            chainstate.db(),
                            &snapshot.consensus_hash,
                            &snapshot.winning_stacks_block_hash,
                        )
                        .unwrap()
                        .unwrap()
                    }
                };

                let parent_header_hash = parent_tip.anchored_header.block_hash();
                let parent_consensus_hash = parent_tip.consensus_hash.clone();
                let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_header_hash,
                );

                let coinbase_tx =
                    // alternate between the miner and a random key, so you can look at the DBs
                    // and logs and see that the parent miner gets the produced streamed tx
                    // fees and the child miner gets the confirmed streamed tx fees.
                    if tenure_id % 2 == 0 {
                        make_coinbase(miner, tenure_id / 2)
                    }
                    else {
                        let pk = StacksPrivateKey::random();
                        let mut tx_coinbase = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            TransactionAuth::from_p2pkh(&pk).unwrap(),
                            TransactionPayload::Coinbase(CoinbasePayload([0x00; 32]), None, None),
                        );
                        tx_coinbase.chain_id = 0x80000000;
                        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
                        tx_coinbase.auth.set_origin_nonce(0);

                        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
                        tx_signer.sign_origin(&pk).unwrap();
                        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
                        tx_coinbase_signed
                    };

                let mut anchored_txs = vec![coinbase_tx];

                // send an anchored tx
                if tenure_id > 0 {
                    let fee = 2000 + (1000 * tenure_id as u64);
                    let stx_transfer = make_user_stacks_transfer(
                        &privk_anchored,
                        anchored_sender_nonce,
                        fee,
                        &recipient.to_account_principal(),
                        1,
                    );
                    anchored_sender_nonce += 1;
                    anchored_txs.push(stx_transfer);
                }

                let sort_ic = sortdb.index_handle_at_tip();
                let (parent_mblock_stream, mblock_pubkey_hash) = {
                    if tenure_id > 0 {
                        chainstate
                            .reload_unconfirmed_state(&sort_ic, parent_index_hash.clone())
                            .unwrap();

                        let parent_microblock_privkey = mblock_privks[tenure_id - 1].clone();
                        // produce the microblock stream for the parent, which this tenure's anchor
                        // block will confirm.
                        let mut microblock_builder = StacksMicroblockBuilder::new(
                            parent_header_hash.clone(),
                            parent_consensus_hash.clone(),
                            chainstate,
                            &sort_ic,
                            BlockBuilderSettings::max_value(),
                        )
                        .unwrap();

                        let mut microblocks = vec![];

                        // different fee each time
                        let fee = 200 + (100 * tenure_id as u64);
                        let mblock_tx = make_user_stacks_transfer(
                            &privk,
                            acct.nonce,
                            fee,
                            &recipient.to_account_principal(),
                            1,
                        );

                        let mblock_tx_len = {
                            let mut bytes = vec![];
                            mblock_tx.consensus_serialize(&mut bytes).unwrap();
                            bytes.len() as u64
                        };

                        test_debug!(
                            "Make microblock parent stream for block in tenure {}",
                            tenure_id
                        );
                        let mblock = microblock_builder
                            .mine_next_microblock_from_txs(
                                vec![(mblock_tx, mblock_tx_len)],
                                &parent_microblock_privkey,
                            )
                            .unwrap();
                        microblocks.push(mblock);

                        let microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&microblock_privkey),
                        );
                        (microblocks, mblock_pubkey_hash)
                    } else {
                        let parent_microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&parent_microblock_privkey),
                        );
                        (vec![], mblock_pubkey_hash)
                    }
                };

                test_debug!("Store parent microblocks for tenure {}", tenure_id);
                for mblock in parent_mblock_stream.iter() {
                    let stored = chainstate
                        .preprocess_streamed_microblock(
                            &parent_consensus_hash,
                            &parent_header_hash,
                            mblock,
                        )
                        .unwrap();
                    assert!(stored);
                }

                let builder = StacksBlockBuilder::make_block_builder(
                    &burnchain,
                    chainstate.mainnet,
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    mblock_pubkey_hash,
                )
                .unwrap();

                let anchored_block = StacksBlockBuilder::make_anchored_block_from_txs(
                    builder,
                    chainstate,
                    &sort_ic,
                    anchored_txs,
                )
                .unwrap();

                // coinbase
                (anchored_block.0, parent_mblock_stream)
            },
        );

        test_debug!("Process tenure {}", tenure_id);

        // make each block-commit unique
        for burn_op in burn_ops.iter_mut() {
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = burn_op {
                op.burn_fee += tenure_id as u64;
            }
        }

        // should always succeed
        peer.next_burnchain_block(burn_ops.clone());
        peer.process_stacks_epoch_at_tip_checked(&stacks_block, &[])
            .unwrap();
    }

    for i in 0..num_blocks {
        let sortdb = peer.sortdb.take().unwrap();
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);

        peer
            .chainstate()
            .with_read_only_clarity_tx(
                &sortdb.index_handle_at_tip(),
                &stacks_block_id,
                |clarity_tx| {
                    let list_val = clarity_tx.with_readonly_clarity_env(
                        false,
                        CHAIN_ID_TESTNET,
                        ClarityVersion::Clarity2,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        None,
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw(&format!("(list
                            (get-block-info? block-reward u{})
                            (get-block-info? miner-spend-winner u{})
                            (get-block-info? miner-spend-total u{})
                        )", i, i, i))
                    )
                    .unwrap();

                    let list = list_val.expect_list().unwrap();
                    let block_reward_opt = list.get(0).cloned().unwrap().expect_optional().unwrap();
                    let miner_spend_winner = list.get(1).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();
                    let miner_spend_total = list.get(2).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();

                    eprintln!("i = {}, block_reward = {:?}, miner_spend_winner = {:?}, miner_spend_total = {:?}", i, &block_reward_opt, &miner_spend_winner, &miner_spend_total);

                    if i >= 1 {
                        assert_eq!(miner_spend_winner, (1000 + i - 1) as u128);
                        assert_eq!(miner_spend_total, (1000 + i - 1) as u128);
                    }
                    else {
                        // genesis
                        assert_eq!(miner_spend_winner, 0);
                        assert_eq!(miner_spend_total, 0);
                    }

                    if i > 0 && i < num_blocks - (MINER_REWARD_MATURITY as usize) - 1 {
                        let coinbase = 3600000000;
                        let tx_fees_anchored =
                            if i > 1 {
                                2000 + 1000 * (i - 1) as u128
                            }
                            else {
                                0
                            };
                        let tx_fees_streamed_produced =
                            if i > 2 {
                                (2 * (200 + 100 * (i - 1)) / 5) as u128
                            }
                            else {
                                0
                            };
                        let tx_fees_streamed_confirmed =
                            if i > 2 {
                                (3 * (200 + 100 * (i - 1)) / 5) as u128
                            }
                            else {
                                0
                            };

                        eprintln!("i = {}, {} + {} + {} + {}", i, coinbase, tx_fees_anchored, tx_fees_streamed_produced, tx_fees_streamed_confirmed);
                        assert_eq!(block_reward_opt.unwrap().expect_u128().unwrap(), coinbase + tx_fees_anchored + tx_fees_streamed_produced + tx_fees_streamed_confirmed);
                    }
                    else {
                        // genesis, or not yet mature
                        assert!(block_reward_opt.is_none());
                    }
                }
            )
            .unwrap();

        peer.sortdb = Some(sortdb);
    }
}

#[test]
fn test_get_block_info_v210_no_microblocks() {
    let privk = StacksPrivateKey::from_hex(
        "42faca653724860da7a41bfcef7e6ba78db55146f6900de8cb2a9f760ffac70c01",
    )
    .unwrap();
    let privk_anchored = StacksPrivateKey::from_hex(
        "f67c7437f948ca1834602b28595c12ac744f287a4efaf70d437042a6afed81bc01",
    )
    .unwrap();

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();

    let addr_anchored = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_anchored)],
    )
    .unwrap();

    let mut peer_config = TestPeerConfig::new(function_name!(), 2022, 2023);
    peer_config.initial_balances = vec![
        (addr.to_account_principal(), 1000000000),
        (addr_anchored.to_account_principal(), 1000000000),
    ];
    let burnchain = peer_config.burnchain.clone();

    let epochs = EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2, // effectively already in 2.1
            end_height: STACKS_EPOCH_MAX,
            block_limit: ExecutionCost {
                write_length: 205205,
                write_count: 205205,
                read_length: 205205,
                read_count: 205205,
                runtime: 205205,
            },
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]);
    peer_config.epochs = Some(epochs);

    let num_blocks = 10;
    let mut anchored_sender_nonce = 0;

    let mut mblock_privks = vec![];
    for _ in 0..num_blocks {
        let mblock_privk = StacksPrivateKey::random();
        mblock_privks.push(mblock_privk);
    }

    let mut peer = TestPeer::new(peer_config);

    let chainstate_path = peer.chainstate_path.clone();

    let first_stacks_block_height = {
        let sn = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();
        sn.block_height
    };

    let recipient_addr_str = "ST1RFD5Q2QPK3E0F08HG9XDX7SSC7CNRS0QR0SGEV";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    for tenure_id in 0..num_blocks {
        // send transactions to the mempool
        let tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();

        let acct = get_stacks_account(&mut peer, &addr.to_account_principal());

        let (mut burn_ops, stacks_block, microblocks) = peer.make_tenure(
            |ref mut miner,
             ref mut sortdb,
             ref mut chainstate,
             vrf_proof,
             ref parent_opt,
             ref parent_microblock_header_opt| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &block.block_hash(),
                        )
                        .unwrap()
                        .unwrap(); // succeeds because we don't fork
                        StacksChainState::get_anchored_block_header_info(
                            chainstate.db(),
                            &snapshot.consensus_hash,
                            &snapshot.winning_stacks_block_hash,
                        )
                        .unwrap()
                        .unwrap()
                    }
                };

                let parent_header_hash = parent_tip.anchored_header.block_hash();
                let parent_consensus_hash = parent_tip.consensus_hash.clone();
                let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_header_hash,
                );

                let coinbase_tx =
                    // alternate between the miner and a random key, so you can look at the DBs
                    // and logs and see that the parent miner gets the produced streamed tx
                    // fees and the child miner gets the confirmed streamed tx fees.
                    if tenure_id % 2 == 0 {
                        make_coinbase(miner, tenure_id / 2)
                    }
                    else {
                        let pk = StacksPrivateKey::random();
                        let mut tx_coinbase = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            TransactionAuth::from_p2pkh(&pk).unwrap(),
                            TransactionPayload::Coinbase(CoinbasePayload([0x00; 32]), None, None),
                        );
                        tx_coinbase.chain_id = 0x80000000;
                        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
                        tx_coinbase.auth.set_origin_nonce(0);

                        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
                        tx_signer.sign_origin(&pk).unwrap();
                        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
                        tx_coinbase_signed
                    };

                let mut anchored_txs = vec![coinbase_tx];

                // send an anchored tx
                if tenure_id > 0 {
                    let fee = 2000 + (1000 * tenure_id as u64);
                    let stx_transfer = make_user_stacks_transfer(
                        &privk_anchored,
                        anchored_sender_nonce,
                        fee,
                        &recipient.to_account_principal(),
                        1,
                    );
                    anchored_sender_nonce += 1;
                    anchored_txs.push(stx_transfer);
                }

                let mblock_pubkey_hash = {
                    let parent_microblock_privkey = mblock_privks[tenure_id].clone();
                    let mblock_pubkey_hash = Hash160::from_node_public_key(
                        &StacksPublicKey::from_private(&parent_microblock_privkey),
                    );
                    mblock_pubkey_hash
                };
                let builder = StacksBlockBuilder::make_block_builder(
                    &burnchain,
                    chainstate.mainnet,
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    mblock_pubkey_hash,
                )
                .unwrap();

                let sort_ic = sortdb.index_handle_at_tip();
                let anchored_block = StacksBlockBuilder::make_anchored_block_from_txs(
                    builder,
                    chainstate,
                    &sort_ic,
                    anchored_txs,
                )
                .unwrap();

                (anchored_block.0, vec![])
            },
        );

        test_debug!("Process tenure {}", tenure_id);

        // make each block-commit unique
        for burn_op in burn_ops.iter_mut() {
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = burn_op {
                op.burn_fee += tenure_id as u64;
            }
        }

        // should always succeed
        peer.next_burnchain_block(burn_ops.clone());
        peer.process_stacks_epoch_at_tip_checked(&stacks_block, &[])
            .unwrap();
    }

    for i in 0..num_blocks {
        let sortdb = peer.sortdb.take().unwrap();
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);

        peer
            .chainstate()
            .with_read_only_clarity_tx(
                &sortdb.index_handle_at_tip(),
                &stacks_block_id,
                |clarity_tx| {
                    let list_val = clarity_tx.with_readonly_clarity_env(
                        false,
                        CHAIN_ID_TESTNET,
                        ClarityVersion::Clarity2,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        None,
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw(&format!("(list
                            (get-block-info? block-reward u{})
                            (get-block-info? miner-spend-winner u{})
                            (get-block-info? miner-spend-total u{})
                        )", i, i, i))
                    )
                    .unwrap();

                    let list = list_val.expect_list().unwrap();
                    let block_reward_opt = list.get(0).cloned().unwrap().expect_optional().unwrap();
                    let miner_spend_winner = list.get(1).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();
                    let miner_spend_total = list.get(2).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();

                    eprintln!("i = {}, block_reward = {:?}, miner_spend_winner = {:?}, miner_spend_total = {:?}", i, &block_reward_opt, &miner_spend_winner, &miner_spend_total);

                    if i >= 1 {
                        assert_eq!(miner_spend_winner, (1000 + i - 1) as u128);
                        assert_eq!(miner_spend_total, (1000 + i - 1) as u128);
                    }
                    else {
                        // genesis
                        assert_eq!(miner_spend_winner, 0);
                        assert_eq!(miner_spend_total, 0);
                    }

                    if i > 0 && i < num_blocks - (MINER_REWARD_MATURITY as usize) - 1 {
                        let coinbase = 3600000000;
                        let tx_fees_anchored =
                            if i > 1 {
                                2000 + 1000 * (i - 1) as u128
                            }
                            else {
                                0
                            };
                        let tx_fees_streamed_produced = 0;
                        let tx_fees_streamed_confirmed = 0;

                        eprintln!("i = {}, {} + {} + {} + {}", i, coinbase, tx_fees_anchored, tx_fees_streamed_produced, tx_fees_streamed_confirmed);
                        assert_eq!(block_reward_opt.unwrap().expect_u128().unwrap(), coinbase + tx_fees_anchored + tx_fees_streamed_produced + tx_fees_streamed_confirmed);
                    }
                    else {
                        // genesis, or not yet mature
                        assert!(block_reward_opt.is_none());
                    }
                }
            )
            .unwrap();

        peer.sortdb = Some(sortdb);
    }
}

#[test]
fn test_coinbase_pay_to_contract_v210() {
    test_coinbase_pay_to_alt_recipient_v210(true)
}

#[test]
fn test_coinbase_pay_to_alt_principal_v210() {
    test_coinbase_pay_to_alt_recipient_v210(false)
}

fn test_coinbase_pay_to_alt_recipient_v210(pay_to_contract: bool) {
    let privk = StacksPrivateKey::from_hex(
        "42faca653724860da7a41bfcef7e6ba78db55146f6900de8cb2a9f760ffac70c01",
    )
    .unwrap();
    let privk_anchored = StacksPrivateKey::from_hex(
        "f67c7437f948ca1834602b28595c12ac744f287a4efaf70d437042a6afed81bc01",
    )
    .unwrap();
    let privk_recipient = StacksPrivateKey::random();

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();

    let addr_anchored = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_anchored)],
    )
    .unwrap();

    let addr_recipient = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk_recipient)],
    )
    .unwrap();

    let mut peer_config = TestPeerConfig::new(
        &format!(
            "test_coinbase_pay_to_alt_recipient_{}_v210",
            if pay_to_contract {
                "contract"
            } else {
                "principal"
            }
        ),
        2024,
        2025,
    );
    peer_config.initial_balances = vec![
        (addr.to_account_principal(), 1000000000),
        (addr_anchored.to_account_principal(), 1000000000),
    ];

    let epochs = EpochList::new(&[
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch10,
            start_height: 0,
            end_height: 0,
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_1_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch20,
            start_height: 0,
            end_height: 1, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch2_05,
            start_height: 1,
            end_height: 2, // NOTE: the first 25 burnchain blocks have no sortition
            block_limit: ExecutionCost::max_value(),
            network_epoch: PEER_VERSION_EPOCH_2_0,
        },
        StacksEpoch {
            epoch_id: StacksEpochId::Epoch21,
            start_height: 2, // effectively already in 2.1
            end_height: STACKS_EPOCH_MAX,
            block_limit: ExecutionCost {
                write_length: 205205000,
                write_count: 205205000,
                read_length: 205205000,
                read_count: 205205000,
                runtime: 205205000000000,
            },
            network_epoch: PEER_VERSION_EPOCH_2_1,
        },
    ]);
    peer_config.epochs = Some(epochs);
    let burnchain = peer_config.burnchain.clone();

    let num_blocks = 10;
    let mut anchored_sender_nonce = 0;

    let mut mblock_privks = vec![];
    for _ in 0..num_blocks {
        let mblock_privk = StacksPrivateKey::random();
        mblock_privks.push(mblock_privk);
    }

    let mut peer = TestPeer::new(peer_config);

    let chainstate_path = peer.chainstate_path.clone();

    let first_stacks_block_height = {
        let sn = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();
        sn.block_height
    };

    let recipient_addr_str = "ST1RFD5Q2QPK3E0F08HG9XDX7SSC7CNRS0QR0SGEV";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    let contract_src = r#"(begin (print "hello world"))"#;
    let contract_name = "hello-world";
    let contract_fee = (2 * contract_src.len()) as u64;

    let mut coinbase_addresses = vec![];

    for tenure_id in 0..num_blocks {
        // send transactions to the mempool
        let tip = SortitionDB::get_canonical_burn_chain_tip(peer.sortdb.as_ref().unwrap().conn())
            .unwrap();

        let acct = get_stacks_account(&mut peer, &addr.to_account_principal());

        let (mut burn_ops, stacks_block, microblocks) = peer.make_tenure(
            |ref mut miner,
             ref mut sortdb,
             ref mut chainstate,
             vrf_proof,
             ref parent_opt,
             ref parent_microblock_header_opt| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &block.block_hash(),
                        )
                        .unwrap()
                        .unwrap(); // succeeds because we don't fork
                        StacksChainState::get_anchored_block_header_info(
                            chainstate.db(),
                            &snapshot.consensus_hash,
                            &snapshot.winning_stacks_block_hash,
                        )
                        .unwrap()
                        .unwrap()
                    }
                };

                let parent_header_hash = parent_tip.anchored_header.block_hash();
                let parent_consensus_hash = parent_tip.consensus_hash.clone();
                let parent_index_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_header_hash,
                );

                let coinbase_tx = {
                    // alternate between the miner and a random key, so you can look at the DBs
                    // and logs and see that the parent miner gets the produced streamed tx
                    // fees and the child miner gets the confirmed streamed tx fees.
                    // BUT, pay to the contract if it exists
                    let recipient_contract_id = if tenure_id > 1 {
                        Some(PrincipalData::Contract(
                            QualifiedContractIdentifier::parse(&format!(
                                "{}.{}",
                                &addr_anchored, contract_name
                            ))
                            .unwrap(),
                        ))
                    } else {
                        None
                    };

                    let alt_recipient_id = if tenure_id > 1 {
                        Some(addr_recipient.to_account_principal())
                    } else {
                        None
                    };

                    if tenure_id % 2 == 0 {
                        coinbase_addresses.push(miner.origin_address().unwrap());
                        if pay_to_contract {
                            if let Some(recipient_contract_id) = recipient_contract_id {
                                make_coinbase_with_nonce(
                                    miner,
                                    tenure_id,
                                    miner.get_nonce(),
                                    Some(recipient_contract_id),
                                )
                            } else {
                                make_coinbase(miner, tenure_id)
                            }
                        } else if let Some(alt_recipient) = alt_recipient_id {
                            make_coinbase_with_nonce(
                                miner,
                                tenure_id,
                                miner.get_nonce(),
                                Some(alt_recipient),
                            )
                        } else {
                            make_coinbase(miner, tenure_id)
                        }
                    } else {
                        let pk = StacksPrivateKey::random();
                        let addr = StacksAddress::from_public_keys(
                            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                            &AddressHashMode::SerializeP2PKH,
                            1,
                            &vec![StacksPublicKey::from_private(&pk)],
                        )
                        .unwrap();
                        coinbase_addresses.push(addr);

                        let mut tx_coinbase = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            TransactionAuth::from_p2pkh(&pk).unwrap(),
                            TransactionPayload::Coinbase(
                                CoinbasePayload([0x00; 32]),
                                if pay_to_contract {
                                    recipient_contract_id
                                } else {
                                    alt_recipient_id
                                },
                                None,
                            ),
                        );
                        tx_coinbase.chain_id = 0x80000000;
                        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
                        tx_coinbase.auth.set_origin_nonce(0);

                        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
                        tx_signer.sign_origin(&pk).unwrap();
                        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
                        tx_coinbase_signed
                    }
                };

                let mut anchored_txs = vec![coinbase_tx];

                // send an anchored tx
                if tenure_id > 0 {
                    if tenure_id == 1 {
                        // make the contract to recieve payments
                        let contract_publish = make_user_contract_publish(
                            &privk_anchored,
                            anchored_sender_nonce,
                            contract_fee,
                            contract_name,
                            contract_src,
                        );
                        anchored_sender_nonce += 1;
                        anchored_txs.push(contract_publish);
                    }

                    let fee = 2000 + (1000 * tenure_id as u64);
                    let stx_transfer = make_user_stacks_transfer(
                        &privk_anchored,
                        anchored_sender_nonce,
                        fee,
                        &recipient.to_account_principal(),
                        1,
                    );
                    anchored_sender_nonce += 1;
                    anchored_txs.push(stx_transfer);
                }

                let sort_ic = sortdb.index_handle_at_tip();
                let (parent_mblock_stream, mblock_pubkey_hash) = {
                    if tenure_id > 0 {
                        chainstate
                            .reload_unconfirmed_state(&sort_ic, parent_index_hash.clone())
                            .unwrap();

                        let parent_microblock_privkey = mblock_privks[tenure_id - 1].clone();
                        // produce the microblock stream for the parent, which this tenure's anchor
                        // block will confirm.
                        let mut microblock_builder = StacksMicroblockBuilder::new(
                            parent_header_hash.clone(),
                            parent_consensus_hash.clone(),
                            chainstate,
                            &sort_ic,
                            BlockBuilderSettings::max_value(),
                        )
                        .unwrap();

                        let mut microblocks = vec![];

                        // different fee each time
                        let fee = 200 + (100 * tenure_id as u64);
                        let mblock_tx = make_user_stacks_transfer(
                            &privk,
                            acct.nonce,
                            fee,
                            &recipient.to_account_principal(),
                            1,
                        );

                        let mblock_tx_len = {
                            let mut bytes = vec![];
                            mblock_tx.consensus_serialize(&mut bytes).unwrap();
                            bytes.len() as u64
                        };

                        test_debug!(
                            "Make microblock parent stream for block in tenure {}",
                            tenure_id
                        );
                        let mblock = microblock_builder
                            .mine_next_microblock_from_txs(
                                vec![(mblock_tx, mblock_tx_len)],
                                &parent_microblock_privkey,
                            )
                            .unwrap();
                        microblocks.push(mblock);

                        let microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&microblock_privkey),
                        );
                        (microblocks, mblock_pubkey_hash)
                    } else {
                        let parent_microblock_privkey = mblock_privks[tenure_id].clone();
                        let mblock_pubkey_hash = Hash160::from_node_public_key(
                            &StacksPublicKey::from_private(&parent_microblock_privkey),
                        );
                        (vec![], mblock_pubkey_hash)
                    }
                };

                test_debug!("Store parent microblocks for tenure {}", tenure_id);
                for mblock in parent_mblock_stream.iter() {
                    let stored = chainstate
                        .preprocess_streamed_microblock(
                            &parent_consensus_hash,
                            &parent_header_hash,
                            mblock,
                        )
                        .unwrap();
                    assert!(stored);
                }

                let builder = StacksBlockBuilder::make_block_builder(
                    &burnchain,
                    chainstate.mainnet,
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    mblock_pubkey_hash,
                )
                .unwrap();

                let anchored_block = StacksBlockBuilder::make_anchored_block_from_txs(
                    builder,
                    chainstate,
                    &sort_ic,
                    anchored_txs,
                )
                .unwrap();

                // coinbase
                (anchored_block.0, parent_mblock_stream)
            },
        );

        test_debug!("Process tenure {}", tenure_id);

        // make each block-commit unique
        for burn_op in burn_ops.iter_mut() {
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = burn_op {
                op.burn_fee += tenure_id as u64;
            }
        }

        // should always succeed
        peer.next_burnchain_block(burn_ops.clone());
        peer.process_stacks_epoch_at_tip_checked(&stacks_block, &[])
            .unwrap();
    }

    let mut recipient_total_reward = 0;
    for i in 0..num_blocks {
        let sortdb = peer.sortdb.take().unwrap();
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);

        // despite the block reward going to an alt. recipient address, the block reward is still
        // reported correctly.
        peer
            .chainstate()
            .with_read_only_clarity_tx(
                &sortdb.index_handle_at_tip(),
                &stacks_block_id,
                |clarity_tx| {
                    let list_val = clarity_tx.with_readonly_clarity_env(
                        false,
                        CHAIN_ID_TESTNET,
                        ClarityVersion::Clarity2,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        None,
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw(&format!("(list
                            (get-block-info? block-reward u{})
                            (get-block-info? miner-spend-winner u{})
                            (get-block-info? miner-spend-total u{})
                        )", i, i, i))
                    )
                    .unwrap();

                    let list = list_val.expect_list().unwrap();
                    let block_reward_opt = list.get(0).cloned().unwrap().expect_optional().unwrap();
                    let miner_spend_winner = list.get(1).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();
                    let miner_spend_total = list.get(2).cloned().unwrap().expect_optional().unwrap().unwrap().expect_u128().unwrap();

                    if i >= 1 {
                        assert_eq!(miner_spend_winner, (1000 + i - 1) as u128);
                        assert_eq!(miner_spend_total, (1000 + i - 1) as u128);
                    }
                    else {
                        // genesis
                        assert_eq!(miner_spend_winner, 0);
                        assert_eq!(miner_spend_total, 0);
                    }

                    if i >= 1 {
                        let miner_val = clarity_tx.with_readonly_clarity_env(
                            false,
                            CHAIN_ID_TESTNET,
                            ClarityVersion::Clarity2,
                            PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                            None,
                            LimitedCostTracker::new_free(),
                            |env| env.eval_raw(&format!("(get-block-info? miner-address u{})", i))
                        )
                        .unwrap();
                        let miner_address = miner_val.expect_optional().unwrap().unwrap().expect_principal().unwrap();

                        eprintln!("i = {}, block_reward = {:?}, miner_spend_winner = {:?}, miner_spend_total = {:?}, miner address = {}", i, &block_reward_opt, &miner_spend_winner, &miner_spend_total, miner_address);
                        assert_eq!(miner_address, coinbase_addresses[i - 1].to_account_principal());
                    }

                    if i > 0 && i < num_blocks - (MINER_REWARD_MATURITY as usize) - 1 {
                        let coinbase = 3600000000;
                        let mut tx_fees_anchored =
                            if i > 1 {
                                2000 + 1000 * (i - 1) as u128
                            }
                            else {
                                0
                            };
                        let tx_fees_streamed_produced =
                            if i > 2 {
                                (2 * (200 + 100 * (i - 1)) / 5) as u128
                            }
                            else {
                                0
                            };
                        let tx_fees_streamed_confirmed =
                            if i > 2 {
                                (3 * (200 + 100 * (i - 1)) / 5) as u128
                            }
                            else {
                                0
                            };

                        if i == 2 {
                            // mined the contract in this one
                            tx_fees_anchored += contract_fee as u128;
                        }

                        eprintln!("i = {}, {} + {} + {} + {}", i, coinbase, tx_fees_anchored, tx_fees_streamed_produced, tx_fees_streamed_confirmed);
                        assert_eq!(block_reward_opt.clone().unwrap().expect_u128().unwrap(), coinbase + tx_fees_anchored + tx_fees_streamed_produced + tx_fees_streamed_confirmed);

                        if i > 2 {
                            eprintln!("recipient_total_reward: {} = {} + {}", recipient_total_reward + block_reward_opt.clone().unwrap().expect_u128().unwrap(), recipient_total_reward, block_reward_opt.clone().unwrap().expect_u128().unwrap());
                            recipient_total_reward += block_reward_opt.unwrap().expect_u128().unwrap();
                        }
                    }
                    else {
                        // genesis, or not yet mature
                        assert!(block_reward_opt.is_none());
                    }
                }
            )
            .unwrap();

        peer.sortdb = Some(sortdb);
    }

    // finally, verify that the alt. recipient got all the coinbases except the first one
    let sortdb = peer.sortdb.take().unwrap();
    let (consensus_hash, block_bhh) =
        SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
    let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);

    // despite the block reward going to an alt. recipient address, the block reward is still
    // reported correctly.
    let recipient_balance = peer
        .chainstate()
        .with_read_only_clarity_tx(
            &sortdb.index_handle_at_tip(),
            &stacks_block_id,
            |clarity_tx| {
                let recipient_balance_val = clarity_tx
                    .with_readonly_clarity_env(
                        false,
                        CHAIN_ID_TESTNET,
                        ClarityVersion::Clarity2,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        None,
                        LimitedCostTracker::new_free(),
                        |env| {
                            if pay_to_contract {
                                env.eval_raw(&format!(
                                    "(stx-get-balance '{}.{})",
                                    &addr_anchored, contract_name
                                ))
                            } else {
                                env.eval_raw(&format!("(stx-get-balance '{})", &addr_recipient))
                            }
                        },
                    )
                    .unwrap();
                recipient_balance_val.expect_u128().unwrap()
            },
        )
        .unwrap();

    // N.B. `stx-get-balance` will reflect one more block-reward than `get-block-info?
    // miner-reward`, so account for that.  This is because `get-block-info?` only reports data
    // as of the parent block, whereas `stx-get-balance` looks in the MARF directly as it is.
    let additional_reward = 3600000000
        + 8000  // 2000 + (1000 * (7 - 1))
        + 480   // 3 * (200 + 100 * (7 - 1)) / 5
        + 320; // 2 * (200 + 100 * (7 - 1)) / 5

    // N.B. the alt. recipient will not have received the tx fees from the stream produced in tenure
    // 2, since tenures 0, 1, and 2 do not pay to the alt. recipient.
    let extra_tx_fees = 160; // 2 * (200 + 100 * (3 - 1)) / 5
    assert_eq!(
        recipient_balance,
        recipient_total_reward + additional_reward - extra_tx_fees
    );
}
