// Copyright (C) 2024 Stacks Open Internet Foundation
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

use std::fs;
use std::net::{Ipv4Addr, SocketAddrV4};
use std::time::{Duration, SystemTime};

use blockstack_lib::chainstate::nakamoto::{NakamotoBlock, NakamotoBlockHeader};
use blockstack_lib::chainstate::stacks::db::StacksBlockHeaderTypes;
use blockstack_lib::chainstate::stacks::{
    CoinbasePayload, SinglesigHashMode, SinglesigSpendingCondition, StacksTransaction,
    TenureChangeCause, TenureChangePayload, TransactionAnchorMode, TransactionAuth,
    TransactionPayload, TransactionPostConditionMode, TransactionPublicKeyEncoding,
    TransactionSpendingCondition, TransactionVersion,
};
use blockstack_lib::net::api::get_tenures_fork_info::TenureForkingInfo;
use blockstack_lib::net::api::getsortition::SortitionInfo;
use clarity::types::chainstate::{BurnchainHeaderHash, SortitionId};
use clarity::util::vrf::VRFProof;
use libsigner::v0::messages::RejectReason;
use libsigner::{BlockProposal, BlockProposalData};
use slog::slog_info;
use stacks_common::bitvec::BitVec;
use stacks_common::consts::CHAIN_ID_TESTNET;
use stacks_common::info;
use stacks_common::types::chainstate::{
    ConsensusHash, StacksBlockId, StacksPrivateKey, StacksPublicKey, TrieHash,
};
use stacks_common::util::get_epoch_time_secs;
use stacks_common::util::hash::{Hash160, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::MessageSignature;

use crate::chainstate::{ProposalEvalConfig, SortitionMinerStatus, SortitionState, SortitionsView};
use crate::client::tests::MockServerClient;
use crate::client::StacksClient;
use crate::signerdb::{BlockInfo, SignerDb};

fn setup_test_environment(
    fn_name: &str,
) -> (
    StacksClient,
    SignerDb,
    StacksPublicKey,
    SortitionsView,
    NakamotoBlock,
) {
    let block_sk = StacksPrivateKey::from_seed(&[0, 1]);
    let block_pk = StacksPublicKey::from_private(&block_sk);
    let block_pkh = Hash160::from_node_public_key(&block_pk);

    let cur_sortition = SortitionState {
        miner_pkh: block_pkh,
        miner_pubkey: None,
        prior_sortition: ConsensusHash([0; 20]),
        parent_tenure_id: ConsensusHash([0; 20]),
        consensus_hash: ConsensusHash([1; 20]),
        miner_status: SortitionMinerStatus::Valid,
        burn_header_timestamp: 2,
        burn_block_hash: BurnchainHeaderHash([1; 32]),
    };

    let last_sortition = Some(SortitionState {
        miner_pkh: block_pkh,
        miner_pubkey: None,
        prior_sortition: ConsensusHash([128; 20]),
        parent_tenure_id: ConsensusHash([128; 20]),
        consensus_hash: ConsensusHash([0; 20]),
        miner_status: SortitionMinerStatus::Valid,
        burn_header_timestamp: 1,
        burn_block_hash: BurnchainHeaderHash([0; 32]),
    });

    let view = SortitionsView {
        cur_sortition,
        last_sortition,
        config: ProposalEvalConfig {
            first_proposal_burn_block_timing: Duration::from_secs(30),
            block_proposal_timeout: Duration::from_secs(5),
            tenure_last_block_proposal_timeout: Duration::from_secs(30),
            tenure_idle_timeout: Duration::from_secs(300),
            tenure_idle_timeout_buffer: Duration::from_secs(2),
            reorg_attempts_activity_timeout: Duration::from_secs(3),
        },
    };

    let stacks_client = StacksClient::new(
        StacksPrivateKey::random(),
        SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 10000).to_string(),
        "FOO".into(),
        false,
        CHAIN_ID_TESTNET,
    );

    let signer_db_dir = "/tmp/stacks-node-tests/signer-units/";
    let signer_db_path = format!("{signer_db_dir}/{fn_name}.{}.sqlite", get_epoch_time_secs());
    fs::create_dir_all(signer_db_dir).unwrap();
    let signer_db = SignerDb::new(signer_db_path).unwrap();

    let block = NakamotoBlock {
        header: NakamotoBlockHeader {
            version: 1,
            chain_length: 10,
            burn_spent: 10,
            consensus_hash: ConsensusHash([15; 20]),
            parent_block_id: StacksBlockId([0; 32]),
            tx_merkle_root: Sha512Trunc256Sum([0; 32]),
            state_index_root: TrieHash([0; 32]),
            timestamp: 3,
            miner_signature: MessageSignature::empty(),
            signer_signature: vec![],
            pox_treatment: BitVec::ones(1).unwrap(),
        },
        txs: vec![],
    };

    (stacks_client, signer_db, block_pk, view, block)
}

#[test]
fn check_proposal_units() {
    let (stacks_client, mut signer_db, block_pk, mut view, block) =
        setup_test_environment("check_proposal_units");

    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect_err("Proposal should not validate");

    view.last_sortition = None;

    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect_err("Proposal should not validate");
}

#[test]
fn check_proposal_miner_pkh_mismatch() {
    let (stacks_client, mut signer_db, _block_pk, mut view, mut block) =
        setup_test_environment("miner_pkh_mismatch");
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    let different_block_pk = StacksPublicKey::from_private(&StacksPrivateKey::from_seed(&[2, 3]));
    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &block,
        &different_block_pk,
        false,
    )
    .expect_err("Proposal should not validate");

    block.header.consensus_hash = view.last_sortition.as_ref().unwrap().consensus_hash;
    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &block,
        &different_block_pk,
        false,
    )
    .expect_err("Proposal should not validate");
}

fn reorg_timing_testing(
    test_name: &str,
    first_proposal_burn_block_timing_secs: u64,
    sortition_timing_secs: u64,
) -> Result<(), RejectReason> {
    let (_stacks_client, mut signer_db, block_pk, mut view, mut block) =
        setup_test_environment(test_name);
    view.config.first_proposal_burn_block_timing =
        Duration::from_secs(first_proposal_burn_block_timing_secs);

    view.cur_sortition.parent_tenure_id = view.last_sortition.as_ref().unwrap().parent_tenure_id;
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    block.txs.push(StacksTransaction::new(
        TransactionVersion::Testnet,
        TransactionAuth::Standard(TransactionSpendingCondition::new_initial_sighash()),
        TransactionPayload::TenureChange(TenureChangePayload {
            tenure_consensus_hash: view.cur_sortition.consensus_hash,
            prev_tenure_consensus_hash: view.cur_sortition.parent_tenure_id,
            burn_view_consensus_hash: view.cur_sortition.consensus_hash,
            previous_tenure_end: block.header.parent_block_id,
            previous_tenure_blocks: 10,
            cause: TenureChangeCause::BlockFound,
            pubkey_hash: Hash160::from_node_public_key(&block_pk),
        }),
    ));
    block.txs.push(StacksTransaction::new(
        TransactionVersion::Testnet,
        TransactionAuth::Standard(TransactionSpendingCondition::new_initial_sighash()),
        TransactionPayload::Coinbase(CoinbasePayload([0; 32]), None, Some(VRFProof::empty())),
    ));

    let last_sortition = view.last_sortition.as_ref().unwrap();

    let expected_result = vec![
        TenureForkingInfo {
            burn_block_hash: last_sortition.burn_block_hash,
            burn_block_height: 2,
            sortition_id: SortitionId([2; 32]),
            parent_sortition_id: SortitionId([1; 32]),
            consensus_hash: last_sortition.consensus_hash,
            was_sortition: true,
            first_block_mined: Some(StacksBlockId([1; 32])),
        },
        TenureForkingInfo {
            burn_block_hash: BurnchainHeaderHash([128; 32]),
            burn_block_height: 1,
            sortition_id: SortitionId([1; 32]),
            parent_sortition_id: SortitionId([0; 32]),
            consensus_hash: view.cur_sortition.parent_tenure_id,
            was_sortition: true,
            first_block_mined: Some(StacksBlockId([2; 32])),
        },
    ];

    let block_proposal_1 = BlockProposal {
        block: NakamotoBlock {
            header: NakamotoBlockHeader {
                version: 1,
                chain_length: 10,
                burn_spent: 10,
                consensus_hash: last_sortition.consensus_hash,
                parent_block_id: StacksBlockId([0; 32]),
                tx_merkle_root: Sha512Trunc256Sum([0; 32]),
                state_index_root: TrieHash([0; 32]),
                timestamp: 11,
                miner_signature: MessageSignature::empty(),
                signer_signature: vec![],
                pox_treatment: BitVec::ones(1).unwrap(),
            },
            txs: vec![],
        },
        burn_height: 2,
        reward_cycle: 1,
        block_proposal_data: BlockProposalData::empty(),
    };
    let mut header_clone = block_proposal_1.block.header.clone();
    let mut block_info_1 = BlockInfo::from(block_proposal_1);
    block_info_1.mark_locally_accepted(false).unwrap();
    signer_db.insert_block(&block_info_1).unwrap();

    let sortition_time = SystemTime::UNIX_EPOCH
        + Duration::from_secs(block_info_1.proposed_time + sortition_timing_secs);
    signer_db
        .insert_burn_block(&view.cur_sortition.burn_block_hash, 3, &sortition_time)
        .unwrap();

    let MockServerClient {
        mut server,
        client,
        config,
    } = MockServerClient::new();
    let h = std::thread::spawn(move || {
        view.check_proposal(&client, &mut signer_db, &block, &block_pk, false)
    });
    header_clone.chain_length -= 1;
    let response = crate::client::tests::build_get_tenure_tip_response(
        &StacksBlockHeaderTypes::Nakamoto(header_clone),
    );
    crate::client::tests::write_response(server, response.as_bytes());
    server = crate::client::tests::mock_server_from_config(&config);

    crate::client::tests::write_response(
        server,
        format!("HTTP/1.1 200 Ok\n\n{}", serde_json::json!(expected_result)).as_bytes(),
    );

    let result = h.join().unwrap();
    info!("Result: {result:?}");
    result
}

#[test]
fn check_proposal_reorg_timing_bad() {
    let result = reorg_timing_testing("reorg_timing_bad", 30, 31);
    result.expect_err("Proposal should not validate, because the reorg occurred in a block whose proposed time was long enough before the sortition");
}

#[test]
fn check_proposal_reorg_timing_ok() {
    let result = reorg_timing_testing("reorg_timing_okay", 30, 30);
    result.expect("Proposal should validate okay, because the reorg occurred in a block whose proposed time was close to the sortition");
}

#[test]
fn check_proposal_invalid_status() {
    let (stacks_client, mut signer_db, block_pk, mut view, mut block) =
        setup_test_environment("invalid_status");
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect("Proposal should validate");
    view.cur_sortition.miner_status = SortitionMinerStatus::InvalidatedAfterFirstBlock;
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect_err("Proposal should not validate");

    block.header.consensus_hash = view.last_sortition.as_ref().unwrap().consensus_hash;
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect_err("Proposal should not validate");

    view.cur_sortition.miner_status = SortitionMinerStatus::InvalidatedBeforeFirstBlock;
    block.header.consensus_hash = view.last_sortition.as_ref().unwrap().consensus_hash;
    // this block passes the signer state checks, even though it doesn't have a tenure change tx.
    // this is because the signer state does not perform the tenure change logic checks: it needs
    // the stacks-node to do that (because the stacks-node actually knows whether or not their
    // parent blocks have been seen before, while the signer state checks are only reasoning about
    // stacks blocks seen by the signer, which may be a subset)
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect("Proposal should validate");
}

fn make_tenure_change_payload() -> TenureChangePayload {
    TenureChangePayload {
        tenure_consensus_hash: ConsensusHash([0; 20]),
        prev_tenure_consensus_hash: ConsensusHash([0; 20]),
        burn_view_consensus_hash: ConsensusHash([0; 20]),
        previous_tenure_end: StacksBlockId([0; 32]),
        previous_tenure_blocks: 1,
        cause: TenureChangeCause::Extended,
        pubkey_hash: Hash160([0; 20]),
    }
}

fn make_tenure_change_tx(payload: TenureChangePayload) -> StacksTransaction {
    StacksTransaction {
        version: TransactionVersion::Testnet,
        chain_id: 1,
        auth: TransactionAuth::Standard(TransactionSpendingCondition::Singlesig(
            SinglesigSpendingCondition {
                hash_mode: SinglesigHashMode::P2PKH,
                signer: Hash160([0; 20]),
                nonce: 0,
                tx_fee: 0,
                key_encoding: TransactionPublicKeyEncoding::Compressed,
                signature: MessageSignature([0; 65]),
            },
        )),
        anchor_mode: TransactionAnchorMode::Any,
        post_condition_mode: TransactionPostConditionMode::Allow,
        post_conditions: vec![],
        payload: TransactionPayload::TenureChange(payload),
    }
}

#[test]
fn check_proposal_tenure_extend_invalid_conditions() {
    let (stacks_client, mut signer_db, block_pk, mut view, mut block) =
        setup_test_environment("tenure_extend");
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    let mut extend_payload = make_tenure_change_payload();
    extend_payload.burn_view_consensus_hash = view.cur_sortition.consensus_hash;
    extend_payload.tenure_consensus_hash = block.header.consensus_hash;
    extend_payload.prev_tenure_consensus_hash = block.header.consensus_hash;
    let tx = make_tenure_change_tx(extend_payload);
    block.txs = vec![tx];
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect_err("Proposal should not validate");

    let mut extend_payload = make_tenure_change_payload();
    extend_payload.burn_view_consensus_hash = ConsensusHash([64; 20]);
    extend_payload.tenure_consensus_hash = block.header.consensus_hash;
    extend_payload.prev_tenure_consensus_hash = block.header.consensus_hash;
    let tx = make_tenure_change_tx(extend_payload);
    block.txs = vec![tx];
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect("Proposal should validate");
}

#[test]
fn check_block_proposal_timeout() {
    let (stacks_client, mut signer_db, block_pk, mut view, mut curr_sortition_block) =
        setup_test_environment("block_proposal_timeout");
    curr_sortition_block.header.consensus_hash = view.cur_sortition.consensus_hash;
    let mut last_sortition_block = curr_sortition_block.clone();
    last_sortition_block.header.consensus_hash =
        view.last_sortition.as_ref().unwrap().consensus_hash;

    // Ensure we have a burn height to compare against
    let burn_hash = view.cur_sortition.burn_block_hash;
    let burn_height = 1;
    let received_time = SystemTime::now();
    signer_db
        .insert_burn_block(&burn_hash, burn_height, &received_time)
        .unwrap();

    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &curr_sortition_block,
        &block_pk,
        false,
    )
    .expect("Proposal should validate");

    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &last_sortition_block,
        &block_pk,
        false,
    )
    .expect_err("Proposal should not validate");

    // Sleep a bit to time out the block proposal
    std::thread::sleep(Duration::from_secs(5));
    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &curr_sortition_block,
        &block_pk,
        false,
    )
    .expect_err("Proposal should not validate");

    view.check_proposal(
        &stacks_client,
        &mut signer_db,
        &last_sortition_block,
        &block_pk,
        false,
    )
    .expect("Proposal should validate");
}

#[test]
fn check_sortition_timeout() {
    let signer_db_dir = "/tmp/stacks-node-tests/signer-units/";
    let signer_db_path = format!(
        "{signer_db_dir}/sortition_timeout.{}.sqlite",
        get_epoch_time_secs()
    );
    fs::create_dir_all(signer_db_dir).unwrap();
    let mut signer_db = SignerDb::new(signer_db_path).unwrap();

    let block_sk = StacksPrivateKey::from_seed(&[0, 1]);
    let block_pk = StacksPublicKey::from_private(&block_sk);
    let block_pkh = Hash160::from_node_public_key(&block_pk);

    let mut sortition = SortitionState {
        miner_pkh: block_pkh,
        miner_pubkey: None,
        prior_sortition: ConsensusHash([0; 20]),
        parent_tenure_id: ConsensusHash([0; 20]),
        consensus_hash: ConsensusHash([1; 20]),
        miner_status: SortitionMinerStatus::Valid,
        burn_header_timestamp: 2,
        burn_block_hash: BurnchainHeaderHash([1; 32]),
    };
    // Ensure we have a burn height to compare against
    let burn_hash = sortition.burn_block_hash;
    let burn_height = 1;
    let received_time = SystemTime::now();
    signer_db
        .insert_burn_block(&burn_hash, burn_height, &received_time)
        .unwrap();

    std::thread::sleep(Duration::from_secs(1));
    // We have not yet timed out
    assert!(!sortition
        .is_timed_out(Duration::from_secs(10), &signer_db)
        .unwrap());
    // We are a valid sortition, have an empty tenure, and have now timed out
    assert!(sortition
        .is_timed_out(Duration::from_secs(1), &signer_db)
        .unwrap());
    // This will not be marked as timed out as the status is no longer valid
    sortition.miner_status = SortitionMinerStatus::InvalidatedAfterFirstBlock;
    assert!(!sortition
        .is_timed_out(Duration::from_secs(1), &signer_db)
        .unwrap());

    // Revert the status to continue other checks
    sortition.miner_status = SortitionMinerStatus::Valid;
    // Insert a signed over block so its no longer an empty tenure
    let block_proposal = BlockProposal {
        block: NakamotoBlock {
            header: NakamotoBlockHeader {
                version: 1,
                chain_length: 10,
                burn_spent: 10,
                consensus_hash: sortition.consensus_hash,
                parent_block_id: StacksBlockId([0; 32]),
                tx_merkle_root: Sha512Trunc256Sum([0; 32]),
                state_index_root: TrieHash([0; 32]),
                timestamp: 11,
                miner_signature: MessageSignature::empty(),
                signer_signature: vec![],
                pox_treatment: BitVec::ones(1).unwrap(),
            },
            txs: vec![],
        },
        burn_height: 2,
        reward_cycle: 1,
        block_proposal_data: BlockProposalData::empty(),
    };

    let mut block_info = BlockInfo::from(block_proposal);
    block_info.signed_over = true;
    signer_db.insert_block(&block_info).unwrap();

    // This will no longer be timed out as we have a non-empty tenure
    assert!(!sortition
        .is_timed_out(Duration::from_secs(1), &signer_db)
        .unwrap());
}

/// Test that the sortition info is refreshed once
/// when `check_proposal` is called with a sortition view
/// that doesn't match the block proposal
#[test]
fn check_proposal_refresh() {
    let (stacks_client, mut signer_db, block_pk, mut view, mut block) =
        setup_test_environment("check_proposal_refresh");
    block.header.consensus_hash = view.cur_sortition.consensus_hash;
    view.check_proposal(&stacks_client, &mut signer_db, &block, &block_pk, false)
        .expect("Proposal should validate");

    let MockServerClient {
        server,
        client,
        config: _,
    } = MockServerClient::new();

    let last_sortition = view.last_sortition.as_ref().unwrap();

    let expected_result = vec![
        SortitionInfo {
            burn_block_hash: last_sortition.burn_block_hash,
            burn_block_height: 2,
            sortition_id: SortitionId([2; 32]),
            parent_sortition_id: SortitionId([1; 32]),
            consensus_hash: block.header.consensus_hash,
            was_sortition: true,
            burn_header_timestamp: 2,
            miner_pk_hash160: Some(view.cur_sortition.miner_pkh),
            stacks_parent_ch: Some(view.cur_sortition.parent_tenure_id),
            last_sortition_ch: Some(view.cur_sortition.parent_tenure_id),
            committed_block_hash: None,
            vrf_seed: None,
        },
        SortitionInfo {
            burn_block_hash: BurnchainHeaderHash([128; 32]),
            burn_block_height: 1,
            sortition_id: SortitionId([1; 32]),
            parent_sortition_id: SortitionId([0; 32]),
            consensus_hash: view.cur_sortition.parent_tenure_id,
            was_sortition: true,
            burn_header_timestamp: 1,
            miner_pk_hash160: Some(view.cur_sortition.miner_pkh),
            stacks_parent_ch: Some(view.cur_sortition.parent_tenure_id),
            last_sortition_ch: Some(view.cur_sortition.parent_tenure_id),
            committed_block_hash: None,
            vrf_seed: None,
        },
    ];

    view.cur_sortition.consensus_hash = ConsensusHash([128; 20]);
    let h = std::thread::spawn(move || {
        view.check_proposal(&client, &mut signer_db, &block, &block_pk, true)
    });
    crate::client::tests::write_response(
        server,
        format!("HTTP/1.1 200 Ok\n\n{}", serde_json::json!(expected_result)).as_bytes(),
    );
    let result = h.join().unwrap();
    result.expect("Proposal should validate");
}
