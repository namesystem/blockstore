use std::collections::HashMap;
use std::{env, thread};

use clarity::vm::types::PrincipalData;
use clarity::vm::ClarityVersion;
use stacks::burnchains::{Burnchain, PoxConstants};
use stacks::chainstate::stacks::address::PoxAddress;
use stacks::chainstate::stacks::db::StacksChainState;
use stacks::chainstate::stacks::miner::{signal_mining_blocked, signal_mining_ready};
use stacks::clarity_cli::vm_execute as execute;
use stacks::config::{EventKeyType, EventObserverConfig, InitialBalance};
use stacks::core::{self, EpochList, STACKS_EPOCH_MAX};
use stacks::util_lib::boot::boot_code_id;
use stacks_common::types::chainstate::{StacksAddress, StacksBlockId};
use stacks_common::types::PrivateKey;
use stacks_common::util::hash::Hash160;
use stacks_common::util::secp256k1::Secp256k1PublicKey;
use stacks_common::util::sleep_ms;

use super::neon_integrations::get_account;
use crate::neon_node::StacksNode;
use crate::stacks_common::types::Address;
use crate::stacks_common::util::hash::bytes_to_hex;
use crate::tests::bitcoin_regtest::BitcoinCoreController;
use crate::tests::epoch_21::wait_pox_stragglers;
use crate::tests::neon_integrations::*;
use crate::tests::*;
use crate::{neon, BitcoinRegtestController, BurnchainController};

#[test]
#[ignore]
/// Verify that it is acceptable to launch PoX-2 at the end of a reward cycle, and set v1 unlock
/// height to be at the start of the subsequent reward cycle.
///
/// Verify that PoX-1 stackers continue to receive PoX payouts after v1 unlock height, and that
/// PoX-2 stackers only begin receiving rewards at the start of the reward cycle following the one
/// that contains v1 unlock height.
///
/// Verify that both of the above work even if miners do not mine in the same block as the PoX-2
/// start height or v1 unlock height (e.g. suppose there's a delay).
///
/// Verify the (buggy) stacks-increase behavior in PoX-2, and then verify that Epoch-2.2
///  **disables** PoX after it activates.
///
/// Verification works using expected number of slots for burn and various PoX addresses.
///
fn disable_pox() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let reward_cycle_len = 10;
    let prepare_phase_len = 3;
    let epoch_2_05 = 215;
    let epoch_2_1 = 230;
    let v1_unlock_height = 231;
    let epoch_2_2 = 255; // two blocks before next prepare phase.

    let stacked = 100_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let increase_by = 10_000_000 * (core::MICROSTACKS_PER_STACKS as u64);

    let spender_sk = StacksPrivateKey::random();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let spender_2_sk = StacksPrivateKey::random();
    let spender_2_addr: PrincipalData = to_addr(&spender_2_sk).into();

    let spender_3_sk = StacksPrivateKey::random();
    let spender_3_addr: PrincipalData = to_addr(&spender_3_sk).into();

    let mut initial_balances = vec![];

    initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: stacked + increase_by + 100_000,
    });

    initial_balances.push(InitialBalance {
        address: spender_2_addr,
        amount: stacked + 100_000,
    });

    // // create a third initial balance so that there's more liquid ustx than the stacked amount bug.
    // //  otherwise, it surfaces the DoS vector.
    initial_balances.push(InitialBalance {
        address: spender_3_addr,
        amount: stacked + 100_000,
    });

    let pox_pubkey_1 = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash_1 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_1).to_bytes());

    let pox_pubkey_2 = Secp256k1PublicKey::from_hex(
        "03cd91307e16c10428dd0120d0a4d37f14d4e0097b3b2ea1651d7bd0fb109cd44b",
    )
    .unwrap();
    let pox_pubkey_hash_2 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_2).to_bytes());

    let pox_pubkey_3 = Secp256k1PublicKey::from_hex(
        "0317782e663c77fb02ebf46a3720f41a70f5678ad185974a456d35848e275fe56b",
    )
    .unwrap();
    let pox_pubkey_hash_3 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_3).to_bytes());

    let (mut conf, _) = neon_integration_test_conf();

    // we'll manually post a forked stream to the node
    conf.node.mine_microblocks = false;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 1_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.node.wait_time_for_blocks = 1_000;
    conf.miner.wait_for_block_download = false;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();
    test_observer::register_any(&mut conf);
    conf.initial_balances.append(&mut initial_balances);

    let mut epochs = EpochList::new(&*core::STACKS_EPOCHS_REGTEST);
    epochs[StacksEpochId::Epoch20].end_height = epoch_2_05;
    epochs[StacksEpochId::Epoch2_05].start_height = epoch_2_05;
    epochs[StacksEpochId::Epoch2_05].end_height = epoch_2_1;
    epochs[StacksEpochId::Epoch21].start_height = epoch_2_1;
    epochs[StacksEpochId::Epoch21].end_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].start_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].end_height = STACKS_EPOCH_MAX;
    epochs.truncate_after(StacksEpochId::Epoch22);
    conf.burnchain.epochs = Some(epochs);

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        4 * prepare_phase_len / 5,
        5,
        15,
        u64::MAX - 2,
        u64::MAX - 1,
        v1_unlock_height as u32,
        epoch_2_2 as u32 + 1,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants.clone();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let runloop_burnchain = burnchain_config.clone();

    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(runloop_burnchain), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // push us to block 205
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // stack right away
    let sort_height = channel.get_sortitions_processed();
    let pox_addr_tuple_1 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_1}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();

    let pox_addr_tuple_3 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_3}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();

    let tx = make_contract_call(
        &spender_sk,
        0,
        3000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_1,
            Value::UInt(sort_height as u128),
            Value::UInt(12),
        ],
    );

    info!("Submit 2.05 stacking tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // wait until just before epoch 2.1
    loop {
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height >= epoch_2_1 - 2 {
            break;
        }
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }

    // skip a couple sortitions
    btc_regtest_controller.bootstrap_chain(4);
    sleep_ms(5000);

    let sort_height = channel.get_sortitions_processed();
    assert!(sort_height > epoch_2_1);
    assert!(sort_height > v1_unlock_height);

    // *now* advance to 2.1
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Test passed processing 2.1");

    let sort_height = channel.get_sortitions_processed();
    let pox_addr_tuple_2 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_2}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();
    let tx = make_contract_call(
        &spender_sk,
        1,
        3000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_2,
            Value::UInt(sort_height as u128),
            Value::UInt(12),
        ],
    );

    info!("Submit 2.1 stacking tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    let tx = make_contract_call(
        &spender_2_sk,
        0,
        3000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_3,
            Value::UInt(sort_height as u128),
            Value::UInt(10),
        ],
    );

    info!("Submit 2.1 stacking tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // that it can mine _at all_ is a success criterion
    let mut last_block_height = get_chain_info(&conf).burn_block_height;
    for _i in 0..5 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height > last_block_height {
            last_block_height = tip_info.burn_block_height;
        } else {
            panic!("FATAL: failed to mine");
        }
    }

    // invoke stack-increase
    let tx = make_contract_call(
        &spender_sk,
        2,
        3000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-increase",
        &[Value::UInt(increase_by.into())],
    );

    info!("Submit 2.1 stack-increase tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    for _i in 0..15 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height > last_block_height {
            last_block_height = tip_info.burn_block_height;
        } else {
            panic!("FATAL: failed to mine");
        }
    }

    // invoke stack-increase again, in Epoch-2.2, it should
    //  runtime abort
    let aborted_increase_nonce = 3;
    let tx = make_contract_call(
        &spender_sk,
        aborted_increase_nonce,
        3000,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-increase",
        &[Value::UInt(5000)],
    );

    info!("Submit 2.1 stack-increase tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // finish the cycle after the 2.2 transition,
    //  and mine two more cycles
    for _i in 0..25 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height > last_block_height {
            last_block_height = tip_info.burn_block_height;
        } else {
            panic!("FATAL: failed to mine");
        }
    }

    let tip_info = get_chain_info(&conf);
    let tip = StacksBlockId::new(&tip_info.stacks_tip_consensus_hash, &tip_info.stacks_tip);

    let (mut chainstate, _) = StacksChainState::open(
        false,
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();
    let sortdb = btc_regtest_controller.sortdb_mut();

    let mut reward_cycle_pox_addrs = HashMap::new();

    info!("Last tip height = {}", tip_info.burn_block_height);

    for height in 211..tip_info.burn_block_height {
        let reward_cycle = pox_constants
            .block_height_to_reward_cycle(burnchain_config.first_block_height, height)
            .unwrap();

        reward_cycle_pox_addrs
            .entry(reward_cycle)
            .or_insert_with(HashMap::new);

        let iconn = sortdb.index_handle_at_block(&chainstate, &tip).unwrap();
        let pox_addrs = chainstate
            .clarity_eval_read_only(
                &iconn,
                &tip,
                &boot_code_id("pox-2", false),
                &format!("(get-burn-block-info? pox-addrs u{height})"),
            )
            .expect_optional()
            .unwrap()
            .unwrap()
            .expect_tuple()
            .unwrap()
            .get_owned("addrs")
            .unwrap()
            .expect_list()
            .unwrap();

        debug!("Test burnchain height {height}");
        if !burnchain_config.is_in_prepare_phase(height) && !pox_addrs.is_empty() {
            assert_eq!(pox_addrs.len(), 2);
            let pox_addr_0 = PoxAddress::try_from_pox_tuple(false, &pox_addrs[0]).unwrap();
            let pox_addr_1 = PoxAddress::try_from_pox_tuple(false, &pox_addrs[1]).unwrap();

            if let Some(pox_slot_count) = reward_cycle_pox_addrs
                .get_mut(&reward_cycle)
                .unwrap()
                .get_mut(&pox_addr_0)
            {
                *pox_slot_count += 1;
            } else {
                reward_cycle_pox_addrs
                    .get_mut(&reward_cycle)
                    .unwrap()
                    .insert(pox_addr_0, 1);
            }

            if let Some(pox_slot_count) = reward_cycle_pox_addrs
                .get_mut(&reward_cycle)
                .unwrap()
                .get_mut(&pox_addr_1)
            {
                *pox_slot_count += 1;
            } else {
                reward_cycle_pox_addrs
                    .get_mut(&reward_cycle)
                    .unwrap()
                    .insert(pox_addr_1, 1);
            }
        }
    }

    let reward_cycle_min = *reward_cycle_pox_addrs.keys().min().unwrap();
    let reward_cycle_max = *reward_cycle_pox_addrs.keys().max().unwrap();

    let pox_addr_1 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_1).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let pox_addr_2 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_2).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let pox_addr_3 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_3).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let burn_pox_addr = PoxAddress::Standard(
        StacksAddress::new(
            26,
            Hash160::from_hex("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );

    let expected_slots = HashMap::from([
        (
            21u64,
            HashMap::from([(pox_addr_1.clone(), 13u64), (burn_pox_addr.clone(), 1)]),
        ),
        (
            22u64,
            HashMap::from([(pox_addr_1.clone(), 13u64), (burn_pox_addr.clone(), 1)]),
        ),
        (
            23u64,
            HashMap::from([(pox_addr_1, 13u64), (burn_pox_addr.clone(), 1)]),
        ),
        // cycle 24 is the first 2.1, it should have pox_2 and pox_3 with equal
        //  slots (because increase hasn't gone into effect yet) and 2 burn slots
        (
            24,
            HashMap::from([
                (pox_addr_2.clone(), 6u64),
                (pox_addr_3.clone(), 6),
                (burn_pox_addr.clone(), 2),
            ]),
        ),
        // stack-increase has been invoked, and so the reward set is skewed.
        //  pox_addr_2 should get the majority of slots (~ 67%)
        (
            25,
            HashMap::from([
                (pox_addr_2, 9u64),
                (pox_addr_3, 4),
                (burn_pox_addr.clone(), 1),
            ]),
        ),
        // Epoch 2.2 has started, so the reward set should be all burns.
        (26, HashMap::from([(burn_pox_addr.clone(), 14)])),
        (27, HashMap::from([(burn_pox_addr, 14)])),
    ]);

    for reward_cycle in reward_cycle_min..(reward_cycle_max + 1) {
        let cycle_counts = &reward_cycle_pox_addrs[&reward_cycle];
        assert_eq!(cycle_counts.len(), expected_slots[&reward_cycle].len(), "The number of expected PoX addresses in reward cycle {reward_cycle} is mismatched with the actual count.");
        for (pox_addr, slots) in cycle_counts.iter() {
            assert_eq!(
                *slots,
                expected_slots[&reward_cycle][pox_addr],
                "The number of expected slots for PoX address {pox_addr} in reward cycle {reward_cycle} is mismatched with the actual count."
            );
            info!("PoX payment received"; "cycle" => reward_cycle, "pox_addr" => %pox_addr, "slots" => slots);
        }
    }

    let mut abort_tested = false;
    let blocks = test_observer::get_blocks();
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed =
                StacksTransaction::consensus_deserialize(&mut tx_bytes.as_slice()).unwrap();
            let tx_sender = PrincipalData::from(parsed.auth.origin().address_testnet());
            if tx_sender == spender_addr && parsed.auth.get_origin_nonce() == aborted_increase_nonce
            {
                let contract_call = match &parsed.payload {
                    TransactionPayload::ContractCall(cc) => cc,
                    _ => panic!("Expected aborted_increase_nonce to be a contract call"),
                };
                assert_eq!(contract_call.contract_name.as_str(), "pox-2");
                assert_eq!(contract_call.function_name.as_str(), "stack-increase");
                let result = Value::try_deserialize_hex_untyped(
                    tx.get("raw_result").unwrap().as_str().unwrap(),
                )
                .unwrap();
                assert_eq!(result.to_string(), "(err none)");
                abort_tested = true;
            }
        }
    }

    assert!(abort_tested, "The stack-increase transaction must have been aborted, and it must have been tested in the tx receipts");

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
/// Verify that it is acceptable to launch PoX-2 at the end of a reward cycle, and set v1 unlock
/// height to be at the start of the subsequent reward cycle.
///
/// Verify that PoX-1 stackers continue to receive PoX payouts after v1 unlock height, and that
/// PoX-2 stackers only begin receiving rewards at the start of the reward cycle following the one
/// that contains v1 unlock height.
///
/// Verify that both of the above work even if miners do not mine in the same block as the PoX-2
/// start height or v1 unlock height (e.g. suppose there's a delay).
///
/// Verify that pox-2 locked funds unlock in Epoch-2.2
///
fn pox_2_unlock_all() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let reward_cycle_len = 5;
    let prepare_phase_len = 3;
    let epoch_2_05 = 215;
    let epoch_2_1 = 222;
    let v1_unlock_height = epoch_2_1 + 1;
    let epoch_2_2 = 239; // one block before a prepare phase

    let stacked = 100_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);

    let spender_sk = StacksPrivateKey::random();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let spender_2_sk = StacksPrivateKey::random();
    let spender_2_addr: PrincipalData = to_addr(&spender_2_sk).into();

    let spender_3_sk = StacksPrivateKey::random();
    let spender_3_addr: PrincipalData = to_addr(&spender_3_sk).into();

    let mut initial_balances = vec![];

    let spender_1_initial_balance = stacked + 100_000;
    let spender_2_initial_balance = stacked + 100_000;
    let tx_fee = 3000;

    initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: stacked + 100_000,
    });

    initial_balances.push(InitialBalance {
        address: spender_2_addr.clone(),
        amount: stacked + 100_000,
    });

    let pox_pubkey_1 = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash_1 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_1).to_bytes());

    let pox_pubkey_2 = Secp256k1PublicKey::from_hex(
        "03cd91307e16c10428dd0120d0a4d37f14d4e0097b3b2ea1651d7bd0fb109cd44b",
    )
    .unwrap();
    let pox_pubkey_hash_2 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_2).to_bytes());

    let pox_pubkey_3 = Secp256k1PublicKey::from_hex(
        "0317782e663c77fb02ebf46a3720f41a70f5678ad185974a456d35848e275fe56b",
    )
    .unwrap();
    let pox_pubkey_hash_3 = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey_3).to_bytes());

    let (mut conf, _) = neon_integration_test_conf();

    // we'll manually post a forked stream to the node
    conf.node.mine_microblocks = false;
    conf.burnchain.max_rbf = 1000000;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 1_000;
    conf.miner.first_attempt_time_ms = 2_000;
    conf.miner.subsequent_attempt_time_ms = 5_000;
    conf.node.wait_time_for_blocks = 1_000;
    conf.miner.wait_for_block_download = false;

    conf.miner.first_attempt_time_ms = i64::MAX as u64;
    conf.miner.subsequent_attempt_time_ms = i64::MAX as u64;

    test_observer::spawn();

    conf.events_observers.insert(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
        timeout_ms: 1000,
        lossy: false,
    });
    conf.initial_balances.append(&mut initial_balances);

    let mut epochs = EpochList::new(&*core::STACKS_EPOCHS_REGTEST);
    epochs[StacksEpochId::Epoch20].end_height = epoch_2_05;
    epochs[StacksEpochId::Epoch2_05].start_height = epoch_2_05;
    epochs[StacksEpochId::Epoch2_05].end_height = epoch_2_1;
    epochs[StacksEpochId::Epoch21].start_height = epoch_2_1;
    epochs[StacksEpochId::Epoch21].end_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].start_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].end_height = STACKS_EPOCH_MAX;
    epochs.truncate_after(StacksEpochId::Epoch22);
    conf.burnchain.epochs = Some(epochs);

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        4 * prepare_phase_len / 5,
        5,
        15,
        u64::MAX - 2,
        u64::MAX - 1,
        v1_unlock_height as u32,
        epoch_2_2 as u32 + 1,
        u32::MAX,
        u32::MAX,
    );
    burnchain_config.pox_constants = pox_constants.clone();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let runloop_burnchain = burnchain_config.clone();

    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(runloop_burnchain), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // push us to block 205
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // stack right away
    let sort_height = channel.get_sortitions_processed();
    let pox_addr_tuple_1 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_1}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();

    let pox_addr_tuple_3 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_3}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();

    let tx = make_contract_call(
        &spender_sk,
        0,
        tx_fee,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_1,
            Value::UInt(sort_height as u128),
            Value::UInt(12),
        ],
    );

    info!("Submit 2.05 stacking tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // wait until just before epoch 2.1
    loop {
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height >= epoch_2_1 - 2 {
            break;
        }
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }

    // skip a couple sortitions
    btc_regtest_controller.bootstrap_chain(4);
    sleep_ms(5000);

    let sort_height = channel.get_sortitions_processed();
    assert!(sort_height > epoch_2_1);
    assert!(sort_height > v1_unlock_height);

    // *now* advance to 2.1
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Test passed processing 2.1");

    let sort_height = channel.get_sortitions_processed();
    let pox_addr_tuple_2 = execute(
        &format!("{{ hashbytes: 0x{pox_pubkey_hash_2}, version: 0x00 }}"),
        ClarityVersion::Clarity2,
    )
    .unwrap()
    .unwrap();

    let tx = make_contract_publish(
        &spender_sk,
        1,
        tx_fee,
        conf.burnchain.chain_id,
        "unlock-height",
        "(define-public (unlock-height (x principal)) (ok (get unlock-height (stx-account x))))",
    );
    submit_tx(&http_origin, &tx);

    let tx = make_contract_call(
        &spender_sk,
        2,
        tx_fee,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_2,
            Value::UInt(sort_height as u128),
            Value::UInt(12),
        ],
    );

    info!("Submit 2.1 stacking tx to {http_origin:?}");
    sleep_ms(5_000);
    submit_tx(&http_origin, &tx);

    let tx = make_contract_call(
        &spender_2_sk,
        0,
        tx_fee,
        conf.burnchain.chain_id,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox-2",
        "stack-stx",
        &[
            Value::UInt(stacked.into()),
            pox_addr_tuple_3,
            Value::UInt(sort_height as u128),
            Value::UInt(10),
        ],
    );

    info!("Submit 2.1 stacking tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // that it can mine _at all_ is a success criterion
    let mut last_block_height = get_chain_info(&conf).burn_block_height;

    // advance to 3 blocks before 2.2 activation
    loop {
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height >= epoch_2_2 - 3 {
            break;
        }
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }

    let tx = make_contract_call(
        &spender_sk,
        3,
        tx_fee,
        conf.burnchain.chain_id,
        &to_addr(&spender_sk),
        "unlock-height",
        "unlock-height",
        &[spender_addr.clone().into()],
    );

    submit_tx(&http_origin, &tx);
    let nonce_of_2_1_unlock_ht_call = 3;
    // this mines bitcoin block epoch_2_2 - 2, and causes
    //  the stacks-node to mine the stacks block which will be included
    //  in bitcoin block epoch_2_2 - 1, so `nonce_of_2_1_unlock_ht_call`
    //  will be included in that bitcoin block.
    // this will build the last block before 2.2 activates
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let tx = make_contract_call(
        &spender_sk,
        4,
        tx_fee,
        conf.burnchain.chain_id,
        &to_addr(&spender_sk),
        "unlock-height",
        "unlock-height",
        &[spender_addr.clone().into()],
    );

    submit_tx(&http_origin, &tx);
    let nonce_of_2_2_unlock_ht_call = 4;

    // this mines bitcoin block epoch_2_2 - 1, and causes
    //  the stacks-node to mine the stacks block which will be included
    //  in bitcoin block epoch_2_2, so `nonce_of_2_2_unlock_ht_call`
    //  will be included in that bitcoin block.
    // this block activates 2.2
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // this *burn block* is when the unlock occurs
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // and this will mine the first block whose parent is the unlock block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let spender_1_account = get_account(&http_origin, &spender_addr);
    let spender_2_account = get_account(&http_origin, &spender_2_addr);

    info!("spender_1_account = {spender_1_account:?}");
    info!("spender_2_account = {spender_2_account:?}");

    assert_eq!(
        spender_1_account.balance as u64,
        spender_1_initial_balance - stacked - (5 * tx_fee),
        "Spender 1 should still be locked"
    );
    assert_eq!(
        spender_1_account.locked as u64, stacked,
        "Spender 1 should still be locked"
    );
    assert_eq!(
        spender_1_account.nonce, 5,
        "Spender 1 should have 4 accepted transactions"
    );

    assert_eq!(
        spender_2_account.balance as u64,
        spender_2_initial_balance - stacked - tx_fee,
        "Spender 2 should still be locked"
    );
    assert_eq!(
        spender_2_account.locked as u64, stacked,
        "Spender 2 should still be locked"
    );
    assert_eq!(
        spender_2_account.nonce, 1,
        "Spender 2 should have two accepted transactions"
    );

    // and this will mice the bitcoin block containing the first block whose parent has >= unlock burn block
    //  (which is the criterion for the unlock)
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let spender_1_account = get_account(&http_origin, &spender_addr);
    let spender_2_account = get_account(&http_origin, &spender_2_addr);

    info!("spender_1_account = {spender_1_account:?}");
    info!("spender_2_account = {spender_2_account:?}");

    assert_eq!(
        spender_1_account.balance,
        spender_1_initial_balance as u128 - (5 * tx_fee as u128),
        "Spender 1 should be unlocked"
    );
    assert_eq!(spender_1_account.locked, 0, "Spender 1 should be unlocked");
    assert_eq!(
        spender_1_account.nonce, 5,
        "Spender 1 should have 5 accepted transactions"
    );

    assert_eq!(
        spender_2_account.balance,
        spender_2_initial_balance as u128 - tx_fee as u128,
        "Spender 2 should be unlocked"
    );
    assert_eq!(spender_2_account.locked, 0, "Spender 2 should be unlocked");
    assert_eq!(
        spender_2_account.nonce, 1,
        "Spender 2 should have two accepted transactions"
    );

    // perform a transfer
    let tx = make_stacks_transfer(
        &spender_sk,
        5,
        tx_fee,
        conf.burnchain.chain_id,
        &spender_3_addr,
        1_000_000,
    );

    info!("Submit stack transfer tx to {http_origin:?}");
    submit_tx(&http_origin, &tx);

    // this wakes up the node to mine the transaction
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this block selects the previously mined block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let spender_1_account = get_account(&http_origin, &spender_addr);
    let spender_2_account = get_account(&http_origin, &spender_2_addr);
    let spender_3_account = get_account(&http_origin, &spender_3_addr);

    info!("spender_1_account = {spender_1_account:?}");
    info!("spender_2_account = {spender_2_account:?}");

    assert_eq!(
        spender_3_account.balance, 1_000_000,
        "Recipient account should have funds"
    );
    assert_eq!(
        spender_3_account.locked, 0,
        "Burn account should be unlocked"
    );
    assert_eq!(
        spender_3_account.nonce, 0,
        "Burn should have no accepted transactions"
    );

    assert_eq!(
        spender_1_account.balance,
        spender_1_initial_balance as u128 - (6 * tx_fee as u128) - 1_000_000,
        "Spender 1 should be unlocked"
    );
    assert_eq!(spender_1_account.locked, 0, "Spender 1 should be unlocked");
    assert_eq!(
        spender_1_account.nonce, 6,
        "Spender 1 should have three accepted transactions"
    );

    assert_eq!(
        spender_2_account.balance,
        spender_2_initial_balance as u128 - tx_fee as u128,
        "Spender 2 should be unlocked"
    );
    assert_eq!(spender_2_account.locked, 0, "Spender 2 should be unlocked");
    assert_eq!(
        spender_2_account.nonce, 1,
        "Spender 2 should have two accepted transactions"
    );

    // finish the cycle after the 2.2 transition,
    //  and mine two more cycles
    for _i in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        let tip_info = get_chain_info(&conf);
        if tip_info.burn_block_height > last_block_height {
            last_block_height = tip_info.burn_block_height;
        } else {
            panic!("FATAL: failed to mine");
        }
    }

    let tip_info = get_chain_info(&conf);
    let tip = StacksBlockId::new(&tip_info.stacks_tip_consensus_hash, &tip_info.stacks_tip);

    let (mut chainstate, _) = StacksChainState::open(
        false,
        conf.burnchain.chain_id,
        &conf.get_chainstate_path_str(),
        None,
    )
    .unwrap();
    let sortdb = btc_regtest_controller.sortdb_mut();

    let mut reward_cycle_pox_addrs = HashMap::new();

    info!("Last tip height = {}", tip_info.burn_block_height);

    for height in 211..tip_info.burn_block_height {
        let reward_cycle = pox_constants
            .block_height_to_reward_cycle(burnchain_config.first_block_height, height)
            .unwrap();

        reward_cycle_pox_addrs
            .entry(reward_cycle)
            .or_insert_with(HashMap::new);

        let iconn = sortdb.index_handle_at_block(&chainstate, &tip).unwrap();
        let pox_addrs = chainstate
            .clarity_eval_read_only(
                &iconn,
                &tip,
                &boot_code_id("pox-2", false),
                &format!("(get-burn-block-info? pox-addrs u{height})"),
            )
            .expect_optional()
            .unwrap()
            .unwrap()
            .expect_tuple()
            .unwrap()
            .get_owned("addrs")
            .unwrap()
            .expect_list()
            .unwrap();

        debug!("Test burnchain height {height}");
        if !burnchain_config.is_in_prepare_phase(height) && !pox_addrs.is_empty() {
            assert_eq!(pox_addrs.len(), 2);
            let pox_addr_0 = PoxAddress::try_from_pox_tuple(false, &pox_addrs[0]).unwrap();
            let pox_addr_1 = PoxAddress::try_from_pox_tuple(false, &pox_addrs[1]).unwrap();

            if let Some(pox_slot_count) = reward_cycle_pox_addrs
                .get_mut(&reward_cycle)
                .unwrap()
                .get_mut(&pox_addr_0)
            {
                *pox_slot_count += 1;
            } else {
                reward_cycle_pox_addrs
                    .get_mut(&reward_cycle)
                    .unwrap()
                    .insert(pox_addr_0, 1);
            }

            if let Some(pox_slot_count) = reward_cycle_pox_addrs
                .get_mut(&reward_cycle)
                .unwrap()
                .get_mut(&pox_addr_1)
            {
                *pox_slot_count += 1;
            } else {
                reward_cycle_pox_addrs
                    .get_mut(&reward_cycle)
                    .unwrap()
                    .insert(pox_addr_1, 1);
            }
        }
    }

    let reward_cycle_min = *reward_cycle_pox_addrs.keys().min().unwrap();
    let reward_cycle_max = *reward_cycle_pox_addrs.keys().max().unwrap();

    let pox_addr_1 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_1).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let pox_addr_2 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_2).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let pox_addr_3 = PoxAddress::Standard(
        StacksAddress::new(26, Hash160::from_hex(&pox_pubkey_hash_3).unwrap()).unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );
    let burn_pox_addr = PoxAddress::Standard(
        StacksAddress::new(
            26,
            Hash160::from_hex("0000000000000000000000000000000000000000").unwrap(),
        )
        .unwrap(),
        Some(AddressHashMode::SerializeP2PKH),
    );

    let expected_slots = HashMap::from([
        (42u64, HashMap::from([(pox_addr_1.clone(), 4u64)])),
        (43, HashMap::from([(pox_addr_1.clone(), 4)])),
        (44, HashMap::from([(pox_addr_1, 4)])),
        // cycle 45 is the first 2.1, and in the setup of this test, there's not
        //  enough time for the stackers to begin in this cycle
        (45, HashMap::from([(burn_pox_addr.clone(), 4)])),
        (46, HashMap::from([(burn_pox_addr.clone(), 4)])),
        (47, HashMap::from([(pox_addr_2, 2), (pox_addr_3, 2)])),
        // Now 2.2 is active, everything should be a burn.
        (48, HashMap::from([(burn_pox_addr.clone(), 4)])),
        (49, HashMap::from([(burn_pox_addr.clone(), 4)])),
        (50, HashMap::from([(burn_pox_addr, 4)])),
    ]);

    for reward_cycle in reward_cycle_min..(reward_cycle_max + 1) {
        let cycle_counts = match reward_cycle_pox_addrs.get(&reward_cycle) {
            Some(x) => x,
            None => {
                info!("No reward cycle entry = {reward_cycle}");
                continue;
            }
        };
        assert_eq!(cycle_counts.len(), expected_slots[&reward_cycle].len(), "The number of expected PoX addresses in reward cycle {reward_cycle} is mismatched with the actual count.");
        for (pox_addr, slots) in cycle_counts.iter() {
            assert_eq!(
                *slots,
                expected_slots[&reward_cycle][pox_addr],
                "The number of expected slots for PoX address {pox_addr} in reward cycle {reward_cycle} is mismatched with the actual count."
            );
            info!("PoX payment received"; "cycle" => reward_cycle, "pox_addr" => %pox_addr, "slots" => slots);
        }
    }

    let mut unlock_ht_22_tested = false;
    let mut unlock_ht_21_tested = false;

    let blocks = test_observer::get_blocks();
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed =
                StacksTransaction::consensus_deserialize(&mut tx_bytes.as_slice()).unwrap();
            let tx_sender = PrincipalData::from(parsed.auth.origin().address_testnet());
            if tx_sender == spender_addr
                && parsed.auth.get_origin_nonce() == nonce_of_2_2_unlock_ht_call
            {
                let contract_call = match &parsed.payload {
                    TransactionPayload::ContractCall(cc) => cc,
                    _ => panic!("Expected aborted_increase_nonce to be a contract call"),
                };
                assert_eq!(contract_call.contract_name.as_str(), "unlock-height");
                assert_eq!(contract_call.function_name.as_str(), "unlock-height");
                let result = Value::try_deserialize_hex_untyped(
                    tx.get("raw_result").unwrap().as_str().unwrap(),
                )
                .unwrap();
                assert_eq!(result.to_string(), format!("(ok u{})", epoch_2_2 + 1));
                unlock_ht_22_tested = true;
            }
            if tx_sender == spender_addr
                && parsed.auth.get_origin_nonce() == nonce_of_2_1_unlock_ht_call
            {
                let contract_call = match &parsed.payload {
                    TransactionPayload::ContractCall(cc) => cc,
                    _ => panic!("Expected aborted_increase_nonce to be a contract call"),
                };
                assert_eq!(contract_call.contract_name.as_str(), "unlock-height");
                assert_eq!(contract_call.function_name.as_str(), "unlock-height");
                let result = Value::try_deserialize_hex_untyped(
                    tx.get("raw_result").unwrap().as_str().unwrap(),
                )
                .unwrap();
                assert_eq!(result.to_string(), format!("(ok u{})", 230 + 60));
                unlock_ht_21_tested = true;
            }
        }
    }

    assert!(unlock_ht_21_tested);
    assert!(unlock_ht_22_tested);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

/// PoX reorg with just one flap. Epoch 2.2 activates during bootup
/// Miner 0 mines and hides the anchor block for cycle 22.
/// Miner 1 mines and hides the anchor block for cycle 23, causing a PoX reorg in miner 0.
/// At the very end, miners stop hiding their blocks, and the test verifies that both miners
/// converge on having anchor blocks for cycles 22 and 24, but not 23.
#[test]
#[ignore]
fn test_pox_reorg_one_flap() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let num_miners = 2;

    let reward_cycle_len = 10;
    let prepare_phase_len = 3;
    let v1_unlock_height = 152;
    let epoch_2_2 = 175;
    let v2_unlock_height = epoch_2_2 + 1;

    let (mut conf_template, _) = neon_integration_test_conf();
    let block_time_ms = 10_000;
    conf_template.node.mine_microblocks = true;
    conf_template.miner.microblock_attempt_time_ms = 2_000;
    conf_template.node.wait_time_for_microblocks = 0;
    conf_template.node.microblock_frequency = 0;
    conf_template.miner.first_attempt_time_ms = 2_000;
    conf_template.miner.subsequent_attempt_time_ms = 5_000;
    conf_template.burnchain.max_rbf = 1000000;
    conf_template.node.wait_time_for_blocks = 1_000;
    conf_template.burnchain.pox_2_activation = Some(v1_unlock_height);

    conf_template.node.require_affirmed_anchor_blocks = false;

    // make epoch 2.1 and 2.2 start in the middle of boot-up
    let mut epochs = EpochList::new(&*core::STACKS_EPOCHS_REGTEST);
    epochs[StacksEpochId::Epoch20].end_height = 101;
    epochs[StacksEpochId::Epoch2_05].start_height = 101;
    epochs[StacksEpochId::Epoch2_05].end_height = 151;
    epochs[StacksEpochId::Epoch21].start_height = 151;
    epochs[StacksEpochId::Epoch21].end_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].start_height = epoch_2_2;
    epochs[StacksEpochId::Epoch22].end_height = STACKS_EPOCH_MAX;
    epochs.truncate_after(StacksEpochId::Epoch22);
    conf_template.burnchain.epochs = Some(epochs);

    let privks: Vec<_> = (0..5).map(|_| StacksPrivateKey::random()).collect();

    let stack_privks: Vec<_> = (0..5).map(|_| StacksPrivateKey::random()).collect();

    let balances: Vec<_> = privks
        .iter()
        .map(|privk| {
            let addr = to_addr(privk);
            InitialBalance {
                address: addr.into(),
                amount: 30_000_000,
            }
        })
        .collect();

    let stack_balances: Vec<_> = stack_privks
        .iter()
        .map(|privk| {
            let addr = to_addr(privk);
            InitialBalance {
                address: addr.into(),
                amount: 2_000_000_000_000_000,
            }
        })
        .collect();

    let mut confs = vec![];
    let mut burnchain_configs = vec![];
    let mut blocks_processed = vec![];
    let mut channels = vec![];
    let mut miner_status = vec![];

    for i in 0..num_miners {
        let seed = StacksPrivateKey::random().to_bytes();
        let (mut conf, _) = neon_integration_test_conf_with_seed(seed);

        conf.initial_balances.clear();
        conf.initial_balances.append(&mut balances.clone());
        conf.initial_balances.append(&mut stack_balances.clone());

        conf.node.mine_microblocks = conf_template.node.mine_microblocks;
        conf.miner.microblock_attempt_time_ms = conf_template.miner.microblock_attempt_time_ms;
        conf.node.wait_time_for_microblocks = conf_template.node.wait_time_for_microblocks;
        conf.node.microblock_frequency = conf_template.node.microblock_frequency;
        conf.miner.first_attempt_time_ms = conf_template.miner.first_attempt_time_ms;
        conf.miner.subsequent_attempt_time_ms = conf_template.miner.subsequent_attempt_time_ms;
        conf.node.wait_time_for_blocks = conf_template.node.wait_time_for_blocks;
        conf.burnchain.max_rbf = conf_template.burnchain.max_rbf;
        conf.burnchain.epochs = conf_template.burnchain.epochs.clone();
        conf.burnchain.pox_2_activation = conf_template.burnchain.pox_2_activation;
        conf.node.require_affirmed_anchor_blocks =
            conf_template.node.require_affirmed_anchor_blocks;

        // multiple nodes so they must download from each other
        conf.miner.wait_for_block_download = true;

        // nodes will selectively hide blocks from one another
        conf.node.fault_injection_hide_blocks = true;

        let rpc_port = 41063 + 10 * i;
        let p2p_port = 41063 + 10 * i + 1;
        conf.node.rpc_bind = format!("127.0.0.1:{rpc_port}");
        conf.node.data_url = format!("http://127.0.0.1:{rpc_port}");
        conf.node.p2p_bind = format!("127.0.0.1:{p2p_port}");

        confs.push(conf);
    }

    let node_privkey_1 =
        StacksNode::make_node_private_key_from_seed(&confs[0].node.local_peer_seed);
    let chain_id = confs[0].burnchain.chain_id;
    let peer_version = confs[0].burnchain.peer_version;
    let p2p_bind = confs[0].node.p2p_bind.clone();
    for conf in confs.iter_mut().skip(1) {
        conf.node.set_bootstrap_nodes(
            format!(
                "{}@{p2p_bind}",
                &StacksPublicKey::from_private(&node_privkey_1).to_hex()
            ),
            chain_id,
            peer_version,
        );
    }

    // use short reward cycles
    for conf in &confs {
        let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());
        let pox_constants = PoxConstants::new(
            reward_cycle_len,
            prepare_phase_len,
            4 * prepare_phase_len / 5,
            5,
            15,
            (1600 * reward_cycle_len - 1).into(),
            (1700 * reward_cycle_len).into(),
            v1_unlock_height,
            v2_unlock_height.try_into().unwrap(),
            u32::MAX,
            u32::MAX,
        );
        burnchain_config.pox_constants = pox_constants.clone();

        burnchain_configs.push(burnchain_config);
    }

    let mut btcd_controller = BitcoinCoreController::new(confs[0].clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        confs[0].clone(),
        None,
        Some(burnchain_configs[0].clone()),
        None,
    );

    btc_regtest_controller.bootstrap_chain(1);

    // make sure all miners have BTC
    for conf in confs.iter().skip(1) {
        let old_mining_pubkey = btc_regtest_controller.get_mining_pubkey().unwrap();
        btc_regtest_controller
            .set_mining_pubkey(conf.burnchain.local_mining_public_key.clone().unwrap());
        btc_regtest_controller.bootstrap_chain(1);
        btc_regtest_controller.set_mining_pubkey(old_mining_pubkey);
    }

    btc_regtest_controller.bootstrap_chain((199 - num_miners) as u64);

    eprintln!("Chain bootstrapped...");

    for (i, burnchain_config) in burnchain_configs.into_iter().enumerate() {
        let mut run_loop = neon::RunLoop::new(confs[i].clone());
        let blocks_processed_arc = run_loop.get_blocks_processed_arc();
        let channel = run_loop.get_coordinator_channel().unwrap();
        let this_miner_status = run_loop.get_miner_status();

        blocks_processed.push(blocks_processed_arc);
        channels.push(channel);
        miner_status.push(this_miner_status);

        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));
    }

    let http_origin = format!("http://{}", &confs[0].node.rpc_bind);

    // give the run loops some time to start up!
    for bp in &blocks_processed {
        wait_for_runloop(bp);
    }

    // activate miners
    eprintln!("\n\nBoot miner 0\n\n");
    loop {
        let tip_info_opt = get_chain_info_opt(&confs[0]);
        if let Some(tip_info) = tip_info_opt {
            eprintln!("\n\nMiner 0: {tip_info:?}\n\n");
            if tip_info.stacks_tip_height > 0 {
                break;
            }
        } else {
            eprintln!("\n\nWaiting for miner 0...\n\n");
        }
        next_block_and_iterate(
            &mut btc_regtest_controller,
            &blocks_processed[0],
            block_time_ms,
        );
    }

    for (i, conf) in confs.iter().enumerate().skip(1) {
        eprintln!("\n\nBoot miner {i}\n\n");
        loop {
            let tip_info_opt = get_chain_info_opt(conf);
            if let Some(tip_info) = tip_info_opt {
                eprintln!("\n\nMiner {i}: {tip_info:?}\n\n");
                if tip_info.stacks_tip_height > 0 {
                    break;
                }
            } else {
                eprintln!("\n\nWaiting for miner {i}...\n\n");
            }
            next_block_and_iterate(&mut btc_regtest_controller, &blocks_processed[i], 5_000);
        }
    }

    eprintln!("\n\nBegin transactions\n\n");

    let pox_pubkey = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash = bytes_to_hex(&Hash160::from_node_public_key(&pox_pubkey).to_bytes());

    let sort_height = channels[0].get_sortitions_processed();

    // make everyone stack
    let stacking_txs: Vec<_> = stack_privks
        .iter()
        .map(|pk| {
            make_contract_call(
                pk,
                0,
                1360,
                conf_template.burnchain.chain_id,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "pox-2",
                "stack-stx",
                &[
                    Value::UInt(2_000_000_000_000_000 - 30_000_000),
                    execute(
                        &format!("{{ hashbytes: 0x{pox_pubkey_hash}, version: 0x00 }}"),
                        ClarityVersion::Clarity1,
                    )
                    .unwrap()
                    .unwrap(),
                    Value::UInt((sort_height + 1) as u128),
                    Value::UInt(12),
                ],
            )
        })
        .collect();

    // keeps the mempool full, and makes it so miners will spend a nontrivial amount of time
    // building blocks
    let all_txs: Vec<_> = privks
        .iter()
        .enumerate()
        .map(|(i, pk)| {
            make_random_tx_chain(pk, (25 * i) as u64, conf_template.burnchain.chain_id, false)
        })
        .collect();

    // everyone locks up
    for (cnt, tx) in stacking_txs.iter().enumerate() {
        eprintln!("\n\nSubmit stacking tx {cnt}\n\n");
        submit_tx(&http_origin, tx);
    }

    // run a reward cycle
    let mut at_220 = false;
    while !at_220 {
        btc_regtest_controller.build_next_block(1);
        sleep_ms(block_time_ms);

        for (i, c) in confs.iter().enumerate() {
            let tip_info = get_chain_info(c);
            info!("Tip for miner {i}: {tip_info:?}");
            if tip_info.burn_block_height == 220 {
                at_220 = true;
            }
        }
    }

    // blast out the rest
    let mut cnt = 0;
    for tx_chain in all_txs {
        for tx in tx_chain {
            eprintln!("\n\nSubmit tx {cnt}\n\n");
            submit_tx(&http_origin, &tx);
            cnt += 1;
        }
    }

    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Tip for miner {i}: {tip_info:?}");
        assert!(tip_info.burn_block_height <= 220);
    }

    eprintln!("\n\nBegin mining\n\n");

    info!("####################### end of cycle ##############################");
    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Tip for miner {i}: {tip_info:?}");
    }
    info!("####################### end of cycle ##############################");

    // prevent Stacks at these heights from propagating
    env::set_var(
        "STACKS_HIDE_BLOCKS_AT_HEIGHT",
        "[226,227,228,229,230,236,237,238,239,240,246,247,248,249,250,256,257,258,259,260,266,267,268,269,270,276,277,278,279,280,286,287,288,289,290]"
    );

    // miner 0 mines a prepare phase and confirms a hidden anchor block.
    // miner 1 is disabled for these prepare phases
    for i in 0..10 {
        eprintln!("\n\nBuild block {i}\n\n");
        btc_regtest_controller.build_next_block(1);
        sleep_ms(block_time_ms);

        for (i, c) in confs.iter().enumerate() {
            let tip_info = get_chain_info(c);
            info!("Tip for miner {i}: {tip_info:?}");
        }

        if i >= reward_cycle_len - prepare_phase_len - 2 {
            signal_mining_blocked(miner_status[1].clone());
        }
    }
    signal_mining_ready(miner_status[1].clone());

    info!("####################### end of cycle ##############################");
    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Tip for miner {i}: {tip_info:?}");
    }
    info!("####################### end of cycle ##############################");

    // miner 1 mines a prepare phase and confirms a hidden anchor block.
    // miner 0 is disabled for this prepare phase
    for i in 0..10 {
        eprintln!("\n\nBuild block {i}\n\n");
        btc_regtest_controller.build_next_block(1);
        sleep_ms(block_time_ms);

        for (i, c) in confs.iter().enumerate() {
            let tip_info = get_chain_info(c);
            info!("Tip for miner {i}: {tip_info:?}");
        }

        if i >= reward_cycle_len - prepare_phase_len - 2 {
            signal_mining_blocked(miner_status[0].clone());
        }
    }
    signal_mining_ready(miner_status[0].clone());

    info!("####################### end of cycle ##############################");
    let mut max_stacks_tip = 0;
    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Tip for miner {i}: {tip_info:?}");

        // miner 1's history overtakes miner 0's.
        // Miner 1 didn't see cycle 22's anchor block, but it just mined an anchor block for cycle
        // 23 and affirmed cycle 22's anchor block's absence.
        max_stacks_tip = std::cmp::max(tip_info.stacks_tip_height, max_stacks_tip);
    }
    info!("####################### end of cycle ##############################");

    // advance to start of next reward cycle
    eprintln!("\n\nBuild final block\n\n");
    btc_regtest_controller.build_next_block(1);
    sleep_ms(block_time_ms);

    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Tip for miner {i}: {tip_info:?}");
    }

    // resume block propagation
    env::set_var("STACKS_HIDE_BLOCKS_AT_HEIGHT", "[]");

    // wait for all blocks to propagate
    eprintln!("Wait for all blocks to propagate; stacks tip height is {max_stacks_tip}");
    wait_pox_stragglers(&confs, max_stacks_tip, block_time_ms);

    // nodes now agree on stacks affirmation map
    for (i, c) in confs.iter().enumerate() {
        let tip_info = get_chain_info(c);
        info!("Final tip for miner {i}: {tip_info:?}");
    }
}
