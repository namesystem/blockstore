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

use std::collections::HashMap;

use clarity::vm::ast::ASTRules;
use clarity::vm::clarity::TransactionConnection;
use clarity::vm::contexts::{
    AssetMap, AssetMapEntry, Environment, GlobalContext, OwnedEnvironment,
};
use clarity::vm::contracts::Contract;
use clarity::vm::costs::cost_functions::ClarityCostFunction;
use clarity::vm::costs::{ClarityCostFunctionReference, ExecutionCost, LimitedCostTracker};
use clarity::vm::database::{ClarityDatabase, MemoryBackingStore};
use clarity::vm::errors::{CheckErrors, Error, RuntimeErrorType};
use clarity::vm::events::StacksTransactionEvent;
use clarity::vm::functions::NativeFunctions;
use clarity::vm::representations::SymbolicExpression;
use clarity::vm::test_util::{
    execute, execute_on_network, symbols_from_values, TEST_BURN_STATE_DB, TEST_BURN_STATE_DB_21,
    TEST_HEADER_DB,
};
use clarity::vm::tests::test_only_mainnet_to_chain_id;
use clarity::vm::types::{
    AssetIdentifier, OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData, Value,
};
use clarity::vm::{ClarityVersion, ContractName};
use lazy_static::lazy_static;
use stacks_common::types::chainstate::{BlockHeaderHash, StacksBlockId};
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash::hex_bytes;

use crate::chainstate::stacks::index::storage::TrieFileStorage;
use crate::chainstate::stacks::index::ClarityMarfTrieId;
use crate::clarity_vm::clarity::ClarityInstance;
use crate::clarity_vm::database::marf::MarfedKV;
use crate::core::{FIRST_BURNCHAIN_CONSENSUS_HASH, FIRST_STACKS_BLOCK_HASH};
use crate::util_lib::boot::boot_code_id;

lazy_static! {
    static ref COST_VOTING_MAINNET_CONTRACT: QualifiedContractIdentifier =
        boot_code_id("cost-voting", true);
    static ref COST_VOTING_TESTNET_CONTRACT: QualifiedContractIdentifier =
        boot_code_id("cost-voting", false);
}

pub fn get_simple_test(function: &NativeFunctions) -> &'static str {
    use clarity::vm::functions::NativeFunctions::*;
    match function {
        Add => "(+ 1 1)",
        ToUInt => "(to-uint 1)",
        ToInt => "(to-int u1)",
        Subtract => "(- 1 1)",
        Multiply => "(* 1 1)",
        Divide => "(/ 1 1)",
        CmpGeq => "(>= 2 1)",
        CmpLeq => "(<= 2 1)",
        CmpLess => "(< 2 1)",
        CmpGreater => "(> 2 1)",
        Modulo => "(mod 2 1)",
        Power => "(pow 2 3)",
        Sqrti => "(sqrti 81)",
        Log2 => "(log2 8)",
        BitwiseXor => "(xor 1 2)",
        And => "(and true false)",
        Or => "(or true false)",
        Not => "(not true)",
        Equals => "(is-eq 1 2)",
        If => "(if true (+ 1 2) 2)",
        Let => "(let ((x 1)) x)",
        FetchVar => "(var-get var-foo)",
        SetVar => "(var-set var-foo 1)",
        Map => "(map not list-foo)",
        Filter => "(filter not list-foo)",
        BuffToIntLe => "(buff-to-int-le 0x00000000000000000000000000000001)",
        BuffToUIntLe => "(buff-to-uint-le 0x00000000000000000000000000000001)",
        BuffToIntBe => "(buff-to-int-be 0x00000000000000000000000000000001)",
        BuffToUIntBe => "(buff-to-uint-be 0x00000000000000000000000000000001)",
        IsStandard => "(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)",
        PrincipalDestruct => "(principal-destruct? 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)",
        PrincipalConstruct => "(principal-construct? 0x1a 0x164247d6f2b425ac5771423ae6c80c754f7172b0)",
        StringToInt => r#"(string-to-int? "-1")"#,
        StringToUInt => r#"(string-to-uint? "1")"#,
        IntToAscii => r#"(int-to-ascii 1)"#,
        IntToUtf8 => r#"(int-to-utf8 1)"#,
        Fold => "(fold + list-bar 0)",
        Append => "(append list-bar 1)",
        Concat => "(concat list-bar list-bar)",
        AsMaxLen => "(as-max-len? list-bar u3)",
        Len => "(len list-bar)",
        ElementAt => "(element-at list-bar u2)",
        ElementAtAlias => "(element-at? list-bar u2)",
        IndexOf => "(index-of list-bar 1)",
        IndexOfAlias => "(index-of? list-bar 1)",
        ListCons => "(list 1 2 3 4)",
        FetchEntry => "(map-get? map-foo {a: 1})",
        SetEntry => "(map-set map-foo {a: 1} {b: 2})",
        InsertEntry => "(map-insert map-foo {a: 2} {b: 2})",
        DeleteEntry => "(map-delete map-foo {a: 1})",
        TupleCons => "(tuple (a 1))",
        TupleGet => "(get a tuple-foo)",
        TupleMerge => "(merge {a: 1, b: 2} {b: 1})",
        Begin => "(begin 1)",
        Hash160 => "(hash160 1)",
        Sha256 => "(sha256 1)",
        Sha512 => "(sha512 1)",
        Sha512Trunc256 => "(sha512/256 1)",
        Keccak256 => "(keccak256 1)",
        Secp256k1Recover => "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",
        Secp256k1Verify => "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        Print => "(print 1)",
        ContractCall => "(contract-call? .contract-other foo-exec 1)",
        ContractOf => "(contract-of contract)",
        PrincipalOf => "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        AsContract => "(as-contract 1)",
        GetBlockInfo => "(get-block-info? time u1)",
        GetBurnBlockInfo => "(get-block-info? time u1)", // TODO: use get-burn-block-info here once API is settled enough to change the mocked burn state DB in this file
        ConsOkay => "(ok 1)",
        ConsError => "(err 1)",
        ConsSome => "(some 1)",
        DefaultTo => "(default-to 1 none)",
        Asserts => "(asserts! true (err 1))",
        UnwrapRet => "(unwrap! (ok 1) (err 1))",
        UnwrapErrRet => "(unwrap-err! (err 1) (ok 1))",
        Unwrap => "(unwrap-panic (ok 1))",
        UnwrapErr => "(unwrap-err-panic (err 1))",
        Match => "(match (some 1) x (+ x 1) 1)",
        TryRet => "(try! (if true (ok 1) (err 1)))",
        IsOkay => "(is-ok (ok 1))",
        IsNone => "(is-none none)",
        IsErr => "(is-err (err 1))",
        IsSome => "(is-some (some 1))",
        MintAsset => "(ft-mint? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        MintToken => "(nft-mint? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetTokenBalance => "(ft-get-balance ft-foo 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetAssetOwner => "(nft-get-owner? nft-foo 1)",
        TransferToken => "(ft-transfer? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        TransferAsset => "(nft-transfer? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        BurnToken => "(ft-burn? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        BurnAsset => "(nft-burn? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetTokenSupply => "(ft-get-supply ft-foo)",
        AtBlock => "(at-block 0x55c9861be5cff984a20ce6d99d4aa65941412889bdc665094136429b84f8c2ee 1)",   // first stacksblockid
        GetStxBalance => "(stx-get-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        StxTransfer => r#"(stx-transfer? u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)"#,
        StxTransferMemo => r#"(stx-transfer-memo? u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 0x89995432)"#,
        StxBurn => "(stx-burn? u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        StxGetAccount => "(stx-account 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        BitwiseAnd => "(bit-and 2 3)",
        BitwiseOr => "(bit-or 2 3)",
        BitwiseNot => "(bit-not 3)",
        BitwiseLShift => "(bit-shift-left 2 u1)",
        BitwiseRShift => "(bit-shift-right 2 u1)",
        BitwiseXor2 => "(bit-xor 1 2)",
        Slice => "(slice? str-foo u1 u1)",
        ToConsensusBuff => "(to-consensus-buff? u1)",
        FromConsensusBuff => "(from-consensus-buff? bool 0x03)",
        ReplaceAt => "(replace-at? list-bar u0 5)",
        GetStacksBlockInfo => "(get-block-info? time u1)",
        GetTenureInfo => "(get-block-info? time u1)",
    }
}

fn execute_transaction(
    env: &mut OwnedEnvironment,
    issuer: PrincipalData,
    contract_identifier: &QualifiedContractIdentifier,
    tx: &str,
    args: &[SymbolicExpression],
) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>), Error> {
    env.execute_transaction(issuer, None, contract_identifier.clone(), tx, args)
}

fn with_owned_env<F, R>(epoch: StacksEpochId, use_mainnet: bool, to_do: F) -> R
where
    F: Fn(OwnedEnvironment) -> R,
{
    let marf_kv = MarfedKV::temporary();
    let chain_id = test_only_mainnet_to_chain_id(use_mainnet);
    let mut clarity_instance = ClarityInstance::new(use_mainnet, chain_id, marf_kv);

    let first_block = StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH);
    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &first_block,
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB,
        )
        .commit_block();

    let mut tip = first_block.clone();

    if epoch >= StacksEpochId::Epoch2_05 {
        let next_block = StacksBlockId([1; 32]);
        let mut clarity_conn =
            clarity_instance.begin_block(&tip, &next_block, &TEST_HEADER_DB, &TEST_BURN_STATE_DB);
        clarity_conn.initialize_epoch_2_05().unwrap();
        clarity_conn.commit_block();
        tip = next_block.clone();
    }

    if epoch >= StacksEpochId::Epoch21 {
        let next_block = StacksBlockId([2; 32]);
        let mut clarity_conn =
            clarity_instance.begin_block(&tip, &next_block, &TEST_HEADER_DB, &TEST_BURN_STATE_DB);
        clarity_conn.initialize_epoch_2_1().unwrap();
        clarity_conn.commit_block();
        tip = next_block.clone();
    }

    let mut marf_kv = clarity_instance.destroy();

    let mut store = marf_kv.begin(&tip, &StacksBlockId([3; 32]));

    to_do(OwnedEnvironment::new_max_limit(
        store.as_clarity_db(&TEST_HEADER_DB, &TEST_BURN_STATE_DB),
        epoch,
        use_mainnet,
    ))
}

fn exec_cost(contract: &str, use_mainnet: bool, epoch: StacksEpochId) -> ExecutionCost {
    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let contract_id = QualifiedContractIdentifier::new(p1_principal.clone(), "self".into());

    with_owned_env(epoch, use_mainnet, |mut owned_env| {
        owned_env
            .initialize_contract(contract_id.clone(), contract, None, ASTRules::PrecheckSize)
            .unwrap();

        let cost_before = owned_env.get_cost_total();

        eprintln!("{}", &contract);
        execute_transaction(
            &mut owned_env,
            p1_principal.clone().into(),
            &contract_id,
            "execute",
            &[],
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();
        let mut cost_after = tracker.get_total();
        cost_after.sub(&cost_before).unwrap();
        cost_after
    })
}

/// Assert that the relative difference between `cost_small` and `cost_large`
///  grows in v205
fn check_cost_growth_200_v_205(
    cost_small_200: u64,
    cost_large_200: u64,
    cost_small_205: u64,
    cost_large_205: u64,
) {
    let growth_200 = (cost_large_200 - cost_small_200) as f64 / cost_small_200 as f64;
    let growth_205 = (cost_large_205 - cost_small_205) as f64 / cost_small_205 as f64;

    assert!(
        growth_205 > growth_200,
        "The difference between larger and smaller exec runtimes should grow in epoch 2.05"
    );
}

/*
hash160
sha256
sha512
sha512trunc256
keccak256
 */

fn test_input_size_epoch_200_205(
    large_input: &str,
    large_baseline: &str,
    small_input: &str,
    small_baseline: &str,
    use_mainnet: bool,
) {
    let large_epoch_200 = exec_cost(large_input, use_mainnet, StacksEpochId::Epoch20).runtime
        - exec_cost(large_baseline, use_mainnet, StacksEpochId::Epoch20).runtime;
    let large_epoch_205 = exec_cost(large_input, use_mainnet, StacksEpochId::Epoch2_05).runtime
        - exec_cost(large_baseline, use_mainnet, StacksEpochId::Epoch2_05).runtime;
    let small_epoch_200 = exec_cost(small_input, use_mainnet, StacksEpochId::Epoch20).runtime
        - exec_cost(small_baseline, use_mainnet, StacksEpochId::Epoch20).runtime;
    let small_epoch_205 = exec_cost(small_input, use_mainnet, StacksEpochId::Epoch2_05).runtime
        - exec_cost(small_baseline, use_mainnet, StacksEpochId::Epoch2_05).runtime;

    assert_eq!(
        large_epoch_200, small_epoch_200,
        "In epoch 2.00, both inputs should have the same runtime"
    );
    assert!(
        large_epoch_205 > small_epoch_205,
        "In epoch 2.05, runtime with a larger input should be greater"
    );
}

fn test_hash_fn_input_sizes_200_205(hash_function: &str, mainnet: bool) {
    let large_input = format!(
        "(define-public (execute) (begin ({} 0x1234567890) (ok 1)))",
        hash_function
    );
    let small_input = format!(
        "(define-public (execute) (begin ({} 0x1234) (ok 1)))",
        hash_function
    );
    let large_base = "(define-public (execute) (begin 0x1234567890 (ok 1)))";
    let small_base = "(define-public (execute) (begin 0x1234 (ok 1)))";

    test_input_size_epoch_200_205(&large_input, large_base, &small_input, small_base, mainnet);
}

fn epoch205_hash_fns_input_size(use_mainnet: bool) {
    test_hash_fn_input_sizes_200_205("hash160", use_mainnet);
    test_hash_fn_input_sizes_200_205("sha256", use_mainnet);
    test_hash_fn_input_sizes_200_205("sha512", use_mainnet);
    test_hash_fn_input_sizes_200_205("sha512/256", use_mainnet);
    test_hash_fn_input_sizes_200_205("keccak256", use_mainnet);
}

#[test]
fn epoch205_hash_fns_input_size_mainnet() {
    epoch205_hash_fns_input_size(true)
}

#[test]
fn epoch205_hash_fns_input_size_testnet() {
    epoch205_hash_fns_input_size(false)
}

fn epoch205_tuple_merge_input_size(use_mainnet: bool) {
    let tuple_merge_uint = "(define-public (execute)
                                   (begin (merge { a: 1 } { a: 1 }) (ok 1)))";
    let tuple_uint = "(define-public (execute)
                                   (begin { a: 1 } { a: 1 } (ok 1)))";
    let tuple_merge_bool = "(define-public (execute)
                                   (begin (merge { a: true } { a: true }) (ok 1)))";
    let tuple_bool = "(define-public (execute)
                                   (begin { a: true } { a: true } (ok 1)))";

    test_input_size_epoch_200_205(
        tuple_merge_uint,
        tuple_uint,
        tuple_merge_bool,
        tuple_bool,
        use_mainnet,
    );
}

#[test]
fn epoch205_tuple_merge_input_size_mainnet() {
    epoch205_tuple_merge_input_size(true)
}

#[test]
fn epoch205_tuple_merge_input_size_testnet() {
    epoch205_tuple_merge_input_size(false)
}

fn epoch205_index_of_input_size(use_mainnet: bool) {
    let index_of_list_6 = "(define-public (execute)
                              (begin (index-of (list u1 u1 u1 u1 u1 u1) u2) (ok 1)))";
    let list_6 = "(define-public (execute)
                              (begin (list u1 u1 u1 u1 u1 u1) (ok 1)))";

    let index_of_list_2 = "(define-public (execute)
                              (begin (index-of (list u1 u1) u2) (ok 1)))";
    let list_2 = "(define-public (execute)
                              (begin (list u1 u1) (ok 1)))";

    test_input_size_epoch_200_205(
        index_of_list_6,
        list_6,
        index_of_list_2,
        list_2,
        use_mainnet,
    );
}

#[test]
fn epoch205_index_of_input_size_mainnet() {
    epoch205_index_of_input_size(true)
}

#[test]
fn epoch205_index_of_input_size_testnet() {
    epoch205_index_of_input_size(false)
}

fn epoch205_eq_input_size(use_mainnet: bool) {
    let eq_with_uints = "(define-public (execute)
                          (begin (is-eq u1 u1 u1 u1 u1 u1) (ok 1)))";
    let uints_no_eq = "(define-public (execute)
                          (begin u1 u1 u1 u1 u1 u1 (ok 1)))";
    let eq_with_bools = "(define-public (execute)
                          (begin (is-eq true true true true true true) (ok 1)))";
    let bools_no_eq = "(define-public (execute)
                          (begin true true true true true true (ok 1)))";

    test_input_size_epoch_200_205(
        eq_with_uints,
        uints_no_eq,
        eq_with_bools,
        bools_no_eq,
        use_mainnet,
    );
}

#[test]
fn epoch205_eq_input_size_mainnet() {
    epoch205_eq_input_size(true)
}

#[test]
fn epoch205_eq_input_size_testnet() {
    epoch205_eq_input_size(false)
}

// Test the `concat` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are fed into `concat` from the datastore.
// Capture the cost of just the concat operation by measuring the cost of contracts that do everything but concat, and
//  ones that do the same and concat.
fn epoch205_concat(use_mainnet: bool) {
    let small_exec_without_concat = "(define-data-var db (list 500 int) (list 1 2 3 4 5))
        (define-public (execute)
               (begin (var-get db) (var-get db) (ok 1)))";
    let small_exec_with_concat = "(define-data-var db (list 500 int) (list 1 2 3 4 5))
        (define-public (execute)
               (begin (concat (var-get db) (var-get db)) (ok 1)))";
    let large_exec_without_concat = "(define-data-var db (list 500 int) (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
        (define-public (execute)
               (begin (var-get db) (var-get db) (ok 1)))";
    let large_exec_with_concat = "(define-data-var db (list 500 int) (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
        (define-public (execute)
               (begin (concat (var-get db) (var-get db)) (ok 1)))";

    let small_cost_epoch_200 =
        exec_cost(small_exec_with_concat, use_mainnet, StacksEpochId::Epoch20).runtime
            - exec_cost(
                small_exec_without_concat,
                use_mainnet,
                StacksEpochId::Epoch20,
            )
            .runtime;
    let small_cost_epoch_205 = exec_cost(
        small_exec_with_concat,
        use_mainnet,
        StacksEpochId::Epoch2_05,
    )
    .runtime
        - exec_cost(
            small_exec_without_concat,
            use_mainnet,
            StacksEpochId::Epoch2_05,
        )
        .runtime;
    let large_cost_epoch_200 =
        exec_cost(large_exec_with_concat, use_mainnet, StacksEpochId::Epoch20).runtime
            - exec_cost(
                large_exec_without_concat,
                use_mainnet,
                StacksEpochId::Epoch20,
            )
            .runtime;
    let large_cost_epoch_205 = exec_cost(
        large_exec_with_concat,
        use_mainnet,
        StacksEpochId::Epoch2_05,
    )
    .runtime
        - exec_cost(
            large_exec_without_concat,
            use_mainnet,
            StacksEpochId::Epoch2_05,
        )
        .runtime;

    check_cost_growth_200_v_205(
        small_cost_epoch_200,
        large_cost_epoch_200,
        small_cost_epoch_205,
        large_cost_epoch_205,
    );
}

#[test]
fn epoch205_concat_mainnet() {
    epoch205_concat(true)
}

#[test]
fn epoch205_concat_testnet() {
    epoch205_concat(false)
}

// Test the `var-get` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are fetched from the datastore.
fn epoch205_var_get(use_mainnet: bool) {
    let smaller_exec = "(define-data-var db (list 500 int) (list 1 2 3 4 5))
      (define-public (execute)
        (begin (var-get db)
               (ok 1)))";
    let larger_exec = "(define-data-var db (list 500 int) (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
      (define-public (execute)
        (begin (var-get db)
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_var_get_mainnet() {
    epoch205_var_get(true)
}

#[test]
fn epoch205_var_get_testnet() {
    epoch205_var_get(false)
}

// Test the `var-set` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are stored to the datastore.
fn epoch205_var_set(use_mainnet: bool) {
    let smaller_exec = "(define-data-var db (list 500 int) (list 1))
      (define-public (execute)
        (begin (var-set db (list 1 2 3 4 5))
               (ok 1)))";
    let larger_exec = "(define-data-var db (list 500 int) (list 1))
      (define-public (execute)
        (begin (var-set db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_var_set_mainnet() {
    epoch205_var_set(true)
}

#[test]
fn epoch205_var_set_testnet() {
    epoch205_var_set(false)
}

// Test the `map-get` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are fetched from the datastore.
fn epoch205_map_get(use_mainnet: bool) {
    let smaller_exec = "(define-map db int (list 500 int))
      (map-set db 0 (list 1 2 3 4 5))
      (define-public (execute)
        (begin (map-get? db 0)
               (ok 1)))";
    let larger_exec = "(define-map db int (list 500 int))
      (map-set db 0 (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
      (define-public (execute)
        (begin (map-get? db 0)
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_map_get_mainnet() {
    epoch205_map_get(true)
}

#[test]
fn epoch205_map_get_testnet() {
    epoch205_map_get(false)
}

// Test the `map-set` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are stored to the datastore.
fn epoch205_map_set(use_mainnet: bool) {
    let smaller_exec = "(define-map db int (list 500 int))
      (define-public (execute)
        (begin (map-set db 0 (list 1 2 3 4 5))
               (ok 1)))";
    let larger_exec = "(define-map db int (list 500 int))
      (define-public (execute)
        (begin (map-set db 0 (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_map_set_mainnet() {
    epoch205_map_set(true)
}

#[test]
fn epoch205_map_set_testnet() {
    epoch205_map_set(false)
}

// Test the `map-insert` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are stored to the datastore.
fn epoch205_map_insert(use_mainnet: bool) {
    let smaller_exec = "(define-map db int (list 500 int))
      (define-public (execute)
        (begin (map-insert db 0 (list 1 2 3 4 5))
               (ok 1)))";
    let larger_exec = "(define-map db int (list 500 int))
      (define-public (execute)
        (begin (map-insert db 0 (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_map_insert_mainnet() {
    epoch205_map_insert(true)
}

#[test]
fn epoch205_map_insert_testnet() {
    epoch205_map_insert(false)
}

// Test the `map-delete` changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are used as keys to the datastore.
fn epoch205_map_delete(use_mainnet: bool) {
    let smaller_exec = "(define-map db (list 500 int) int)
      (map-set db (list 1 2 3 4 5) 0)
      (define-public (execute)
        (begin (map-delete db (list 1 2 3 4 5))
               (ok 1)))";
    let larger_exec = "(define-map db (list 500 int) int)
      (map-set db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) 0)
      (define-public (execute)
        (begin (map-delete db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
               (ok 1)))";

    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_map_delete_mainnet() {
    epoch205_map_delete(true)
}

#[test]
fn epoch205_map_delete_testnet() {
    epoch205_map_delete(false)
}

// Test the nft changes in epoch 2.05. Using a dynamic input to the cost function will make the difference in runtime
// cost larger when larger objects are stored to the datastore.
fn epoch205_nfts(use_mainnet: bool) {
    // test nft-mint
    let smaller_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-mint? db (list 1 2 3 4 5) tx-sender)
               (ok 1)))";
    let larger_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-mint? db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) tx-sender)
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );

    // test nft-transfer
    //  these transfers fail, but the cost tabulation is still the same
    let smaller_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-transfer? db (list 1 2 3 4 5)
                             tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
               (ok 1)))";
    let larger_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-transfer? db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20)
                             tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );

    // test nft-burn
    //  these burns fail, but the cost tabulation is still the same
    let smaller_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-burn? db (list 1 2 3 4 5)
                             'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
               (ok 1)))";
    let larger_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-burn? db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20)
                             'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );

    // test nft-get-owner?
    //  these calls fail, but the cost tabulation is still the same
    let smaller_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-get-owner? db (list 1 2 3 4 5))
               (ok 1)))";
    let larger_exec = "(define-non-fungible-token db (list 500 int))
      (define-public (execute)
        (begin (nft-get-owner? db (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20))
               (ok 1)))";
    let smaller_cost_epoch_200 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch20);
    let smaller_cost_epoch_205 = exec_cost(smaller_exec, use_mainnet, StacksEpochId::Epoch2_05);
    let larger_cost_epoch_200 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch20);
    let larger_cost_epoch_205 = exec_cost(larger_exec, use_mainnet, StacksEpochId::Epoch2_05);

    check_cost_growth_200_v_205(
        smaller_cost_epoch_200.runtime,
        larger_cost_epoch_200.runtime,
        smaller_cost_epoch_205.runtime,
        larger_cost_epoch_205.runtime,
    );
}

#[test]
fn epoch205_nfts_mainnet() {
    epoch205_nfts(true)
}

#[test]
fn epoch205_nfts_testnet() {
    epoch205_nfts(false)
}

fn setup_cost_tracked_test(
    use_mainnet: bool,
    version: ClarityVersion,
    owned_env: &mut OwnedEnvironment,
) {
    let contract_trait = "(define-trait trait-1 (
                            (foo-exec (int) (response int int))
                          ))";
    let contract_other = "(impl-trait .contract-trait.trait-1)
                          (define-map map-foo { a: int } { b: int })
                          (define-public (foo-exec (a int)) (ok 1))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let other_contract_id =
        QualifiedContractIdentifier::new(p1_principal.clone(), "contract-other".into());
    let trait_contract_id =
        QualifiedContractIdentifier::new(p1_principal.clone(), "contract-trait".into());

    owned_env
        .initialize_versioned_contract(
            trait_contract_id.clone(),
            version,
            contract_trait,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    owned_env
        .initialize_versioned_contract(
            other_contract_id.clone(),
            version,
            contract_other,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
}

fn test_program_cost(
    prog: &str,
    version: ClarityVersion,
    owned_env: &mut OwnedEnvironment,
    prog_id: usize,
) -> ExecutionCost {
    let contract_self = format!(
        "(define-map map-foo {{ a: int }} {{ b: int }})
        (define-non-fungible-token nft-foo int)
        (define-fungible-token ft-foo)
        (define-data-var var-foo int 0)
        (define-constant tuple-foo (tuple (a 1)))
        (define-constant list-foo (list true))
        (define-constant list-bar (list 1))
        (define-constant str-foo \"foobar\")
        (use-trait trait-1 .contract-trait.trait-1)
        (define-public (execute (contract <trait-1>)) (ok {}))",
        prog
    );

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let self_contract_id = QualifiedContractIdentifier::new(
        p1_principal.clone(),
        ContractName::try_from(format!("self-{}", prog_id)).unwrap(),
    );
    let other_contract_id =
        QualifiedContractIdentifier::new(p1_principal.clone(), "contract-other".into());

    owned_env
        .initialize_versioned_contract(
            self_contract_id.clone(),
            version,
            &contract_self,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    let start = owned_env.get_cost_total();

    let target_contract = Value::from(PrincipalData::Contract(other_contract_id.clone()));
    eprintln!("{}", &contract_self);
    execute_transaction(
        owned_env,
        p2_principal.clone(),
        &self_contract_id,
        "execute",
        &symbols_from_values(vec![target_contract]),
    )
    .unwrap();

    let mut result = owned_env.get_cost_total();
    result.sub(&start).unwrap();
    result
}

// test each individual cost function can be correctly invoked as
//  Clarity code executes in Epoch 2.00
fn epoch_20_205_test_all(use_mainnet: bool, epoch: StacksEpochId) {
    with_owned_env(epoch, use_mainnet, |mut owned_env| {
        setup_cost_tracked_test(use_mainnet, ClarityVersion::Clarity1, &mut owned_env);

        let baseline = test_program_cost("1", ClarityVersion::Clarity1, &mut owned_env, 0);

        for (ix, f) in NativeFunctions::ALL.iter().enumerate() {
            // Note: The 2.0 and 2.05 test assumes Clarity1.
            if f.get_min_version() == ClarityVersion::Clarity1 {
                let test = get_simple_test(f);
                let cost =
                    test_program_cost(test, ClarityVersion::Clarity1, &mut owned_env, ix + 1);
                assert!(cost.exceeds(&baseline));
            }
        }
    })
}

#[test]
fn epoch_20_test_all_mainnet() {
    epoch_20_205_test_all(true, StacksEpochId::Epoch20)
}

#[test]
fn epoch_20_test_all_testnet() {
    epoch_20_205_test_all(false, StacksEpochId::Epoch20)
}

#[test]
fn epoch_205_test_all_mainnet() {
    epoch_20_205_test_all(true, StacksEpochId::Epoch2_05)
}

#[test]
fn epoch_205_test_all_testnet() {
    epoch_20_205_test_all(false, StacksEpochId::Epoch2_05)
}

// test each individual cost function can be correctly invoked as
//  Clarity code executes in Epoch 2.1
fn epoch_21_test_all(use_mainnet: bool) {
    with_owned_env(StacksEpochId::Epoch21, use_mainnet, |mut owned_env| {
        setup_cost_tracked_test(use_mainnet, ClarityVersion::Clarity2, &mut owned_env);

        let baseline = test_program_cost("1", ClarityVersion::Clarity2, &mut owned_env, 0);

        for (ix, f) in NativeFunctions::ALL.iter().enumerate() {
            // Note: Include Clarity2 functions for Epoch21.
            let test = get_simple_test(f);
            let cost = test_program_cost(test, ClarityVersion::Clarity2, &mut owned_env, ix + 1);
            assert!(cost.exceeds(&baseline));
        }
    })
}

#[test]
fn epoch_21_test_all_mainnet() {
    epoch_21_test_all(true)
}

#[test]
fn epoch_21_test_all_testnet() {
    epoch_21_test_all(false)
}

fn test_cost_contract_short_circuits(use_mainnet: bool, clarity_version: ClarityVersion) {
    let marf_kv = MarfedKV::temporary();
    let chain_id = test_only_mainnet_to_chain_id(use_mainnet);
    let mut clarity_instance = ClarityInstance::new(use_mainnet, chain_id, marf_kv);
    let burn_db = if clarity_version == ClarityVersion::Clarity2 {
        &TEST_BURN_STATE_DB_21
    } else {
        &TEST_BURN_STATE_DB
    };

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    let marf_kv = clarity_instance.destroy();

    let p1 = execute_on_network("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR", use_mainnet);
    let p2 = execute_on_network("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G", use_mainnet);

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "cost-definer".into());
    let intercepted = QualifiedContractIdentifier::new(p1_principal.clone(), "intercepted".into());
    let caller = QualifiedContractIdentifier::new(p1_principal.clone(), "caller".into());

    let mut marf_kv = {
        let mut clarity_inst = ClarityInstance::new(use_mainnet, chain_id, marf_kv);
        let mut block_conn = clarity_inst.begin_block(
            &StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let cost_definer_src = "
    (define-read-only (cost-definition (size uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let intercepted_src = "
    (define-read-only (intercepted-function (a uint))
       (if (>= a u10)
           (+ (+ a a) (+ a a)
              (+ a a) (+ a a))
           u0))
    ";

        let caller_src = "
    (define-public (execute (a uint))
       (ok (contract-call? .intercepted intercepted-function a)))
    ";

        for (contract_name, contract_src) in [
            (&cost_definer, cost_definer_src),
            (&intercepted, intercepted_src),
            (&caller, caller_src),
        ]
        .iter()
        {
            block_conn.as_transaction(|tx| {
                let (mut ast, analysis) = tx
                    .analyze_smart_contract(
                        contract_name,
                        clarity_version,
                        contract_src,
                        ASTRules::PrecheckSize,
                    )
                    .unwrap();
                tx.initialize_smart_contract(
                    contract_name,
                    clarity_version,
                    &mut ast,
                    &analysis,
                    contract_src,
                    None,
                    |_, _| false,
                )
                .unwrap();
                tx.save_analysis(contract_name, &analysis).unwrap();
            });
        }

        block_conn.commit_block();
        clarity_inst.destroy()
    };

    let without_interposing_5 = {
        let mut store = marf_kv.begin(&StacksBlockId([1; 32]), &StacksBlockId([2; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    let without_interposing_10 = {
        let mut store = marf_kv.begin(&StacksBlockId([2; 32]), &StacksBlockId([3; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(10)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    let voting_contract_to_use: &QualifiedContractIdentifier = if use_mainnet {
        &COST_VOTING_MAINNET_CONTRACT
    } else {
        &COST_VOTING_TESTNET_CONTRACT
    };

    {
        let mut store = marf_kv.begin(&StacksBlockId([3; 32]), &StacksBlockId([4; 32]));
        let mut db = store.as_clarity_db(&TEST_HEADER_DB, burn_db);
        db.begin();
        db.set_variable_unknown_descriptor(
            voting_contract_to_use,
            "confirmed-proposal-count",
            Value::UInt(1),
        )
        .unwrap();
        let value = format!(
            "{{  function-contract: '{},
                 function-name: {},
                 cost-function-contract: '{},
                 cost-function-name: {},
                 confirmed-height: u1 }}",
            intercepted, "\"intercepted-function\"", cost_definer, "\"cost-definition\""
        );
        let epoch = db.get_clarity_epoch_version().unwrap();
        db.set_entry_unknown_descriptor(
            voting_contract_to_use,
            "confirmed-proposals",
            execute_on_network("{ confirmed-id: u0 }", use_mainnet),
            execute_on_network(&value, use_mainnet),
            &epoch,
        )
        .unwrap();
        db.commit().unwrap();
        store.test_commit();
    }

    let with_interposing_5 = {
        let mut store = marf_kv.begin(&StacksBlockId([4; 32]), &StacksBlockId([5; 32]));

        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    let with_interposing_10 = {
        let mut store = marf_kv.begin(&StacksBlockId([5; 32]), &StacksBlockId([6; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(10)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        tracker.get_total()
    };

    assert!(without_interposing_5.exceeds(&with_interposing_5));
    assert!(without_interposing_10.exceeds(&with_interposing_10));

    assert_eq!(with_interposing_5, with_interposing_10);
    assert!(without_interposing_5 != without_interposing_10);
}

#[test]
fn test_cost_contract_short_circuits_mainnet() {
    test_cost_contract_short_circuits(true, ClarityVersion::Clarity1);
    test_cost_contract_short_circuits(true, ClarityVersion::Clarity2);
}

#[test]
fn test_cost_contract_short_circuits_testnet() {
    test_cost_contract_short_circuits(false, ClarityVersion::Clarity1);
    test_cost_contract_short_circuits(false, ClarityVersion::Clarity2);
}

fn test_cost_voting_integration(use_mainnet: bool, clarity_version: ClarityVersion) {
    let marf_kv = MarfedKV::temporary();
    let chain_id = test_only_mainnet_to_chain_id(use_mainnet);
    let mut clarity_instance = ClarityInstance::new(use_mainnet, chain_id, marf_kv);
    let burn_db = if clarity_version == ClarityVersion::Clarity2 {
        &TEST_BURN_STATE_DB_21
    } else {
        &TEST_BURN_STATE_DB
    };

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    let marf_kv = clarity_instance.destroy();

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "cost-definer".into());
    let bad_cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "bad-cost-definer".into());
    let bad_cost_args_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "bad-cost-args-definer".into());
    let intercepted = QualifiedContractIdentifier::new(p1_principal.clone(), "intercepted".into());
    let caller = QualifiedContractIdentifier::new(p1_principal.clone(), "caller".into());

    let mut marf_kv = {
        let mut clarity_inst = ClarityInstance::new(use_mainnet, chain_id, marf_kv);
        let mut block_conn = clarity_inst.begin_block(
            &StacksBlockId::new(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let cost_definer_src = "
    (define-read-only (cost-definition (size uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    (define-read-only (cost-definition-le (size uint))
       {
         runtime: u0, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })
    (define-read-only (cost-definition-multi-arg (a uint) (b uint) (c uint))
       {
         runtime: u1, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })

    ";

        let bad_cost_definer_src = "
    (define-data-var my-var uint u10)
    (define-read-only (cost-definition (size uint))
       {
         runtime: (var-get my-var), write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let bad_cost_args_definer_src = "
    (define-read-only (cost-definition (a uint) (b uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let intercepted_src = "
    (define-read-only (intercepted-function (a uint))
       (if (>= a u10)
           (+ (+ a a) (+ a a)
              (+ a a) (+ a a))
           u0))

    (define-read-only (intercepted-function2 (a uint) (b uint) (c uint))
       (- (+ a b) c))

    (define-public (non-read-only) (ok (+ 1 2 3)))
    ";

        let caller_src = "
    (define-public (execute (a uint))
       (ok (contract-call? .intercepted intercepted-function a)))
    (define-public (execute-2 (a uint))
       (ok (< a a)))
    ";

        for (contract_name, contract_src) in [
            (&cost_definer, cost_definer_src),
            (&intercepted, intercepted_src),
            (&caller, caller_src),
            (&bad_cost_definer, bad_cost_definer_src),
            (&bad_cost_args_definer, bad_cost_args_definer_src),
        ]
        .iter()
        {
            block_conn.as_transaction(|tx| {
                let (mut ast, analysis) = tx
                    .analyze_smart_contract(
                        contract_name,
                        clarity_version,
                        contract_src,
                        ASTRules::PrecheckSize,
                    )
                    .unwrap();
                tx.initialize_smart_contract(
                    contract_name,
                    clarity_version,
                    &mut ast,
                    &analysis,
                    contract_src,
                    None,
                    |_, _| false,
                )
                .unwrap();
                tx.save_analysis(contract_name, &analysis).unwrap();
            });
        }

        block_conn.commit_block();
        clarity_inst.destroy()
    };

    let bad_cases = vec![
        // non existent "replacement target"
        (
            PrincipalData::from(QualifiedContractIdentifier::local("non-existent").unwrap()),
            "non-existent-func",
            PrincipalData::from(cost_definer.clone()),
            "cost-definition",
        ),
        // replacement target isn't a contract principal
        (
            p1_principal.clone().into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract isn't a contract principal
        (
            intercepted.clone().into(),
            "intercepted-function",
            p1_principal.clone().into(),
            "cost-definition",
        ),
        // replacement function doesn't exist
        (
            intercepted.clone().into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // replacement function isn't read-only
        (
            intercepted.clone().into(),
            "non-read-only",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // "boot cost" function doesn't exist
        (
            boot_code_id("costs", false).into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract doesn't exist
        (
            intercepted.clone().into(),
            "intercepted-function",
            QualifiedContractIdentifier::local("non-existent")
                .unwrap()
                .into(),
            "cost-definition",
        ),
        // cost defining function doesn't exist
        (
            intercepted.clone().into(),
            "intercepted-function",
            cost_definer.clone().into(),
            "cost-definition-2",
        ),
        // cost defining contract isn't arithmetic-only
        (
            intercepted.clone().into(),
            "intercepted-function",
            bad_cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract has incorrect number of arguments
        (
            intercepted.clone().into(),
            "intercepted-function",
            bad_cost_args_definer.clone().into(),
            "cost-definition",
        ),
    ];

    let bad_proposals = bad_cases.len();

    let voting_contract_to_use: &QualifiedContractIdentifier = if use_mainnet {
        &COST_VOTING_MAINNET_CONTRACT
    } else {
        &COST_VOTING_TESTNET_CONTRACT
    };

    {
        let mut store = marf_kv.begin(&StacksBlockId([1; 32]), &StacksBlockId([2; 32]));

        let mut db = store.as_clarity_db(&TEST_HEADER_DB, burn_db);
        db.begin();

        db.set_variable_unknown_descriptor(
            voting_contract_to_use,
            "confirmed-proposal-count",
            Value::UInt(bad_proposals as u128),
        )
        .unwrap();

        for (ix, (intercepted_ct, intercepted_f, cost_ct, cost_f)) in
            bad_cases.into_iter().enumerate()
        {
            let value = format!(
                "{{  function-contract: '{},
                     function-name: \"{}\",
                     cost-function-contract: '{},
                     cost-function-name: \"{}\",
                     confirmed-height: u1 }}",
                intercepted_ct, intercepted_f, cost_ct, cost_f
            );
            let epoch = db.get_clarity_epoch_version().unwrap();
            db.set_entry_unknown_descriptor(
                voting_contract_to_use,
                "confirmed-proposals",
                execute(&format!("{{ confirmed-id: u{} }}", ix)),
                execute(&value),
                &epoch,
            )
            .unwrap();
        }
        db.commit().unwrap();
        store.test_commit();
    }

    let le_cost_without_interception = {
        let mut store = marf_kv.begin(&StacksBlockId([2; 32]), &StacksBlockId([3; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute-2",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        assert!(
            tracker.contract_call_circuits().is_empty(),
            "No contract call circuits should have been processed"
        );
        for (target, referenced_function) in tracker.cost_function_references().into_iter() {
            assert_eq!(
                &referenced_function.contract_id,
                &boot_code_id("costs", use_mainnet),
                "All cost functions should still point to the boot costs"
            );
            assert_eq!(
                &referenced_function.function_name,
                target.get_name_str(),
                "All cost functions should still point to the boot costs"
            );
        }
        store.test_commit();

        tracker.get_total()
    };

    let good_cases = vec![
        (
            intercepted.clone(),
            "intercepted-function",
            cost_definer.clone(),
            "cost-definition",
        ),
        (
            boot_code_id("costs", use_mainnet),
            "cost_le",
            cost_definer.clone(),
            "cost-definition-le",
        ),
        (
            intercepted.clone(),
            "intercepted-function2",
            cost_definer.clone(),
            "cost-definition-multi-arg",
        ),
    ];

    {
        let mut store = marf_kv.begin(&StacksBlockId([3; 32]), &StacksBlockId([4; 32]));

        let mut db = store.as_clarity_db(&TEST_HEADER_DB, burn_db);
        db.begin();

        let good_proposals = good_cases.len() as u128;
        db.set_variable_unknown_descriptor(
            voting_contract_to_use,
            "confirmed-proposal-count",
            Value::UInt(bad_proposals as u128 + good_proposals),
        )
        .unwrap();

        for (ix, (intercepted_ct, intercepted_f, cost_ct, cost_f)) in
            good_cases.into_iter().enumerate()
        {
            let value = format!(
                "{{ function-contract: '{},
                    function-name: \"{}\",
                    cost-function-contract: '{},
                    cost-function-name: \"{}\",
                    confirmed-height: u1 }}",
                intercepted_ct, intercepted_f, cost_ct, cost_f
            );
            let epoch = db.get_clarity_epoch_version().unwrap();
            db.set_entry_unknown_descriptor(
                voting_contract_to_use,
                "confirmed-proposals",
                execute(&format!("{{ confirmed-id: u{} }}", ix + bad_proposals)),
                execute(&value),
                &epoch,
            )
            .unwrap();
        }
        db.commit().unwrap();

        store.test_commit();
    }

    {
        let mut store = marf_kv.begin(&StacksBlockId([4; 32]), &StacksBlockId([5; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&TEST_HEADER_DB, burn_db),
            StacksEpochId::Epoch20,
            use_mainnet,
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute-2",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        // cost of `le` should be less now, because the proposal made it free
        assert!(le_cost_without_interception.exceeds(&tracker.get_total()));

        let circuits = tracker.contract_call_circuits();
        assert_eq!(circuits.len(), 2);

        let circuit1 = circuits.get(&(intercepted.clone(), "intercepted-function".into()));
        let circuit2 = circuits.get(&(intercepted.clone(), "intercepted-function2".into()));

        assert!(circuit1.is_some());
        assert!(circuit2.is_some());

        assert_eq!(circuit1.unwrap().contract_id, cost_definer);
        assert_eq!(circuit1.unwrap().function_name, "cost-definition");

        assert_eq!(circuit2.unwrap().contract_id, cost_definer);
        assert_eq!(circuit2.unwrap().function_name, "cost-definition-multi-arg");

        for (target, referenced_function) in tracker.cost_function_references().into_iter() {
            if target == &ClarityCostFunction::Le {
                assert_eq!(&referenced_function.contract_id, &cost_definer);
                assert_eq!(&referenced_function.function_name, "cost-definition-le");
            } else {
                assert_eq!(
                    &referenced_function.contract_id,
                    &boot_code_id("costs", use_mainnet),
                    "Cost function should still point to the boot costs"
                );
                assert_eq!(
                    &referenced_function.function_name,
                    target.get_name_str(),
                    "Cost function should still point to the boot costs"
                );
            }
        }
        store.test_commit();
    };
}

#[test]
fn test_cost_voting_integration_mainnet() {
    test_cost_voting_integration(true, ClarityVersion::Clarity1);
    test_cost_voting_integration(true, ClarityVersion::Clarity2);
}

#[test]
fn test_cost_voting_integration_testnet() {
    test_cost_voting_integration(false, ClarityVersion::Clarity1);
    test_cost_voting_integration(false, ClarityVersion::Clarity2);
}
