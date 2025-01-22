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

use clarity::vm::ast::stack_depth_checker::AST_CALL_STACK_DEPTH_BUFFER;
use clarity::vm::ast::{self, ASTRules};
use clarity::vm::clarity::{ClarityConnection, TransactionConnection};
use clarity::vm::contexts::{Environment, GlobalContext, OwnedEnvironment};
use clarity::vm::contracts::Contract;
use clarity::vm::costs::ExecutionCost;
use clarity::vm::database::{ClarityDatabase, HeadersDB};
use clarity::vm::errors::{CheckErrors, Error as InterpreterError, Error, RuntimeErrorType};
use clarity::vm::representations::SymbolicExpression;
use clarity::vm::test_util::*;
use clarity::vm::tests::{test_clarity_versions, BurnStateDB};
use clarity::vm::types::{
    OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData, StandardPrincipalData,
    TypeSignature, Value,
};
use clarity::vm::version::ClarityVersion;
use clarity::vm::{ContractContext, MAX_CALL_STACK_DEPTH};
#[cfg(test)]
use rstest::rstest;
#[cfg(test)]
use rstest_reuse::{self, *};
use stacks_common::consts::{CHAIN_ID_MAINNET, CHAIN_ID_TESTNET};
use stacks_common::types::chainstate::{BlockHeaderHash, StacksBlockId};
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash::hex_bytes;

use crate::chainstate::stacks::boot::{BOOT_CODE_COSTS, BOOT_CODE_COSTS_2, BOOT_CODE_COSTS_3};
use crate::chainstate::stacks::index::ClarityMarfTrieId;
use crate::clarity_vm::clarity::{ClarityBlockConnection, ClarityInstance, Error as ClarityError};
use crate::clarity_vm::database::marf::MarfedKV;
use crate::clarity_vm::database::MemoryBackingStore;
use crate::util_lib::boot::boot_code_id;

fn test_block_headers(n: u8) -> StacksBlockId {
    StacksBlockId([n; 32])
}

pub const TEST_BURN_STATE_DB_AST_PRECHECK: UnitTestBurnStateDB = UnitTestBurnStateDB {
    epoch_id: StacksEpochId::Epoch20,
    ast_rules: ast::ASTRules::PrecheckSize,
};

const SIMPLE_TOKENS: &str = "(define-map tokens { account: principal } { balance: uint })
         (define-read-only (my-get-token-balance (account principal))
            (default-to u0 (get balance (map-get? tokens (tuple (account account))))))
         (define-read-only (explode (account principal))
             (map-delete tokens (tuple (account account))))
         (define-private (token-credit! (account principal) (amount uint))
            (if (<= amount u0)
                (err \"must be positive\")
                (let ((current-amount (my-get-token-balance account)))
                  (begin
                    (map-set tokens (tuple (account account))
                                       (tuple (balance (+ amount current-amount))))
                    (ok 0)))))
         (define-public (token-transfer (to principal) (amount uint))
          (let ((balance (my-get-token-balance tx-sender)))
             (if (or (> amount balance) (<= amount u0))
                 (err \"not enough balance\")
                 (begin
                   (map-set tokens (tuple (account tx-sender))
                                      (tuple (balance (- balance amount))))
                   (token-credit! to amount)))))
         (define-public (faucet)
           (let ((original-sender tx-sender))
             (as-contract (print (token-transfer (print original-sender) u1)))))
         (define-public (mint-after (block-to-release uint))
           (if (>= block-height block-to-release)
               (faucet)
               (err \"must be in the future\")))
         (begin (token-credit! 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR u10000)
                (token-credit! 'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G u200)
                (token-credit! .tokens u4))";

/// Since setup_block is not called, we need to manually increment the tenure
/// height each time a new block is made.
fn new_block<'a, 'b>(
    clarity: &'a mut ClarityInstance,
    current: &StacksBlockId,
    next: &StacksBlockId,
    header_db: &'b dyn HeadersDB,
    burn_state_db: &'b dyn BurnStateDB,
) -> ClarityBlockConnection<'a, 'b> {
    let mut block = clarity.begin_block(current, next, header_db, burn_state_db);
    block.as_free_transaction(|tx_conn| {
        tx_conn
            .with_clarity_db(|db| {
                if db.get_clarity_epoch_version().unwrap() >= StacksEpochId::Epoch30 {
                    let tenure_height = db.get_tenure_height().unwrap_or(0);
                    db.set_tenure_height(tenure_height + 1).unwrap();
                }
                Ok(())
            })
            .unwrap();
    });
    block
}

#[apply(test_clarity_versions)]
fn test_simple_token_system(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {
    if epoch < StacksEpochId::Epoch2_05 || version > ClarityVersion::Clarity2 {
        return;
    }
    let mut clarity = ClarityInstance::new(false, CHAIN_ID_TESTNET, MarfedKV::temporary());
    let p1 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR")
            .unwrap(),
    );
    let p2 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G")
            .unwrap(),
    );
    let contract_identifier = QualifiedContractIdentifier::local("tokens").unwrap();
    let burn_db = &generate_test_burn_state_db(epoch);

    let mut gb = clarity.begin_test_genesis_block(
        &StacksBlockId::sentinel(),
        &StacksBlockId([0xfe; 32]),
        &TEST_HEADER_DB,
        burn_db,
    );

    gb.as_transaction(|tx| {
        tx.with_clarity_db(|db| {
            db.set_clarity_epoch_version(epoch).unwrap();
            Ok(())
        })
        .unwrap();

        match epoch {
            StacksEpochId::Epoch2_05 => {
                let (mut ast, analysis) = tx
                    .analyze_smart_contract(
                        &boot_code_id("costs-2", false),
                        ClarityVersion::Clarity1,
                        BOOT_CODE_COSTS_2,
                        ASTRules::PrecheckSize,
                    )
                    .unwrap();
                tx.initialize_smart_contract(
                    &boot_code_id("costs-2", false),
                    ClarityVersion::Clarity1,
                    &mut ast,
                    &analysis,
                    BOOT_CODE_COSTS_2,
                    None,
                    |_, _| false,
                )
                .unwrap();
            }
            StacksEpochId::Epoch21
            | StacksEpochId::Epoch22
            | StacksEpochId::Epoch23
            | StacksEpochId::Epoch24
            | StacksEpochId::Epoch25
            | StacksEpochId::Epoch30
            | StacksEpochId::Epoch31 => {
                let (mut ast, analysis) = tx
                    .analyze_smart_contract(
                        &boot_code_id("costs-3", false),
                        ClarityVersion::Clarity2,
                        BOOT_CODE_COSTS_3,
                        ASTRules::PrecheckSize,
                    )
                    .unwrap();
                tx.initialize_smart_contract(
                    &boot_code_id("costs-3", false),
                    ClarityVersion::Clarity2,
                    &mut ast,
                    &analysis,
                    BOOT_CODE_COSTS_3,
                    None,
                    |_, _| false,
                )
                .unwrap();
            }
            _ => panic!("Epoch {} not covered.", &epoch),
        }
    });

    gb.commit_block();

    {
        let mut block = new_block(
            &mut clarity,
            &StacksBlockId([0xfe; 32]),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let tokens_contract = SIMPLE_TOKENS;

        block.as_transaction(|tx| {
            let (mut contract_ast, contract_analysis) = tx
                .analyze_smart_contract(
                    &contract_identifier,
                    ClarityVersion::Clarity2,
                    tokens_contract,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            tx.initialize_smart_contract(
                &contract_identifier,
                version,
                &mut contract_ast,
                &contract_analysis,
                tokens_contract,
                None,
                |_, _| false,
            )
            .unwrap()
        });

        assert!(!is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p2,
                    None,
                    &contract_identifier,
                    "token-transfer",
                    &[p1.clone().into(), Value::UInt(210)],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));
        assert!(is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "token-transfer",
                    &[p2.clone().into(), Value::UInt(9000)],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert!(!is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "token-transfer",
                    &[p2.clone().into(), Value::UInt(1001)],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));
        assert!(is_committed(
            & // send to self!
            block.as_transaction(|tx| tx.run_contract_call(&p1, None, &contract_identifier, "token-transfer",
                                    &[p1.clone().into(), Value::UInt(1000)], |_, _| false)).unwrap().0
        ));

        assert_eq!(
            block
                .as_transaction(|tx| tx.eval_read_only(
                    &contract_identifier,
                    "(my-get-token-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)"
                ))
                .unwrap(),
            Value::UInt(1000)
        );
        assert_eq!(
            block
                .as_transaction(|tx| tx.eval_read_only(
                    &contract_identifier,
                    "(my-get-token-balance 'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G)"
                ))
                .unwrap(),
            Value::UInt(9200)
        );

        assert!(is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "faucet",
                    &[],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert!(is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "faucet",
                    &[],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert!(is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "faucet",
                    &[],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert_eq!(
            block
                .as_transaction(|tx| tx.eval_read_only(
                    &contract_identifier,
                    "(my-get-token-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)"
                ))
                .unwrap(),
            Value::UInt(1003)
        );

        assert!(!is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "mint-after",
                    &[Value::UInt(25)],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));
        block.commit_block();
    }

    for i in 0..25 {
        {
            let block = new_block(
                &mut clarity,
                &test_block_headers(i),
                &test_block_headers(i + 1),
                &TEST_HEADER_DB,
                burn_db,
            );
            block.commit_block();
        }
    }

    {
        let mut block = new_block(
            &mut clarity,
            &test_block_headers(25),
            &test_block_headers(26),
            &TEST_HEADER_DB,
            burn_db,
        );
        assert!(is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "mint-after",
                    &[Value::UInt(25)],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert!(!is_committed(
            &block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "faucet",
                    &[],
                    |_, _| false
                ))
                .unwrap()
                .0
        ));

        assert_eq!(
            block
                .as_transaction(|tx| tx.eval_read_only(
                    &contract_identifier,
                    "(my-get-token-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)"
                ))
                .unwrap(),
            Value::UInt(1004)
        );
        assert_eq!(
            block
                .as_transaction(|tx| tx.run_contract_call(
                    &p1,
                    None,
                    &contract_identifier,
                    "my-get-token-balance",
                    &[p1.clone().into()],
                    |_, _| false
                ))
                .unwrap()
                .0,
            Value::UInt(1004)
        );
    }
}

pub fn with_versioned_memory_environment<F>(f: F, version: ClarityVersion, top_level: bool)
where
    F: FnOnce(&mut OwnedEnvironment, ClarityVersion),
{
    let mut marf_kv = MemoryBackingStore::new();

    let mut owned_env = OwnedEnvironment::new(marf_kv.as_clarity_db(), StacksEpochId::latest());
    // start an initial transaction.
    if !top_level {
        owned_env.begin();
    }

    f(&mut owned_env, version)
}

#[apply(test_clarity_versions)]
fn test_simple_naming_system(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {
    with_versioned_memory_environment(inner_test_simple_naming_system, version, false);
}

fn inner_test_simple_naming_system(owned_env: &mut OwnedEnvironment, version: ClarityVersion) {
    let tokens_contract = SIMPLE_TOKENS;

    let names_contract = "(define-constant burn-address 'SP000000000000000000002Q6VF78)
         (define-private (price-function (name int))
           (if (< name 100000) u1000 u100))

         (define-map name-map
           { name: int } { owner: principal })
         (define-map preorder-map
           { name-hash: (buff 20) }
           { buyer: principal, paid: uint })

         (define-public (preorder
                        (name-hash (buff 20))
                        (name-price uint))
           (let ((xfer-result (contract-call? .tokens token-transfer
                                  burn-address name-price)))
            (if (is-ok xfer-result)
               (if
                 (map-insert preorder-map
                   (tuple (name-hash name-hash))
                   (tuple (paid name-price)
                          (buyer tx-sender)))
                 (ok 0) (err 2))
               (if (is-eq (unwrap-err! xfer-result (err (- 1)))
                        \"not enough balance\")
                   (err 1) (err 3)))))

         (define-public (register
                        (recipient-principal principal)
                        (name int)
                        (salt int))
           (let ((preorder-entry
                   ;; preorder entry must exist!
                   (unwrap! (map-get? preorder-map
                                  (tuple (name-hash (hash160 (xor name salt))))) (err 5)))
                 (name-entry
                   (map-get? name-map (tuple (name name)))))
             (if (and
                  (is-none name-entry)
                  ;; preorder must have paid enough
                  (<= (price-function name)
                      (get paid preorder-entry))
                  ;; preorder must have been the current principal
                  (is-eq tx-sender
                       (get buyer preorder-entry)))
                  (if (and
                    (map-insert name-map
                      (tuple (name name))
                      (tuple (owner recipient-principal)))
                    (map-delete preorder-map
                      (tuple (name-hash (hash160 (xor name salt))))))
                    (ok 0)
                    (err 3))
                  (err 4))))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let name_hash_expensive_0 = execute("(hash160 1)");
    let name_hash_expensive_1 = execute("(hash160 2)");
    let name_hash_cheap_0 = execute("(hash160 100001)");
    let placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity1,
    );

    {
        let mut env = owned_env.get_exec_environment(None, None, &placeholder_context);

        let contract_identifier = QualifiedContractIdentifier::local("tokens").unwrap();
        env.initialize_contract(contract_identifier, tokens_contract, ASTRules::PrecheckSize)
            .unwrap();

        let contract_identifier = QualifiedContractIdentifier::local("names").unwrap();
        env.initialize_contract(contract_identifier, names_contract, ASTRules::PrecheckSize)
            .unwrap();
    }

    {
        let mut env = owned_env.get_exec_environment(
            Some(p2.clone().expect_principal().unwrap()),
            None,
            &placeholder_context,
        );

        assert!(is_err_code_i128(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_0.clone(), Value::UInt(1000)]),
                false
            )
            .unwrap(),
            1
        ));
    }

    {
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone().expect_principal().unwrap()),
            None,
            &placeholder_context,
        );
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_0.clone(), Value::UInt(1000)]),
                false
            )
            .unwrap()
        ));
        assert!(is_err_code_i128(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_0.clone(), Value::UInt(1000)]),
                false
            )
            .unwrap(),
            2
        ));
    }

    {
        // shouldn't be able to register a name you didn't preorder!
        let mut env = owned_env.get_exec_environment(
            Some(p2.clone().expect_principal().unwrap()),
            None,
            &placeholder_context,
        );
        assert!(is_err_code_i128(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2.clone(), Value::Int(1), Value::Int(0)]),
                false
            )
            .unwrap(),
            4
        ));
    }

    {
        // should work!
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone().expect_principal().unwrap()),
            None,
            &placeholder_context,
        );
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2.clone(), Value::Int(1), Value::Int(0)]),
                false
            )
            .unwrap()
        ));
    }

    {
        // try to underpay!
        let mut env = owned_env.get_exec_environment(
            Some(p2.clone().expect_principal().unwrap()),
            None,
            &placeholder_context,
        );
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_1.clone(), Value::UInt(100)]),
                false
            )
            .unwrap()
        ));
        assert!(is_err_code_i128(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2.clone(), Value::Int(2), Value::Int(0)]),
                false
            )
            .unwrap(),
            4
        ));

        // register a cheap name!
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_cheap_0.clone(), Value::UInt(100)]),
                false
            )
            .unwrap()
        ));
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2.clone(), Value::Int(100001), Value::Int(0)]),
                false
            )
            .unwrap()
        ));

        // preorder must exist!
        assert!(is_err_code_i128(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2.clone(), Value::Int(100001), Value::Int(0)]),
                false
            )
            .unwrap(),
            5
        ));
    }
}

/*
 * This test exhibits memory inflation --
 *   `(define-data-var var-x ...)` uses more than 1048576 bytes of memory.
 *      this is mainly due to using hex encoding in the sqlite storage.
 */
#[apply(test_clarity_versions)]
pub fn rollback_log_memory_test(
    #[case] clarity_version: ClarityVersion,
    #[case] epoch_id: StacksEpochId,
) {
    let marf = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, CHAIN_ID_TESTNET, marf);
    let EXPLODE_N = 100;
    let burn_db = &generate_test_burn_state_db(epoch_id);

    let contract_identifier = QualifiedContractIdentifier::local("foo").unwrap();
    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    {
        let mut conn = new_block(
            &mut clarity_instance,
            &StacksBlockId([0; 32]),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let define_data_var = "(define-data-var XZ (buff 1048576) 0x00)";

        let mut contract = define_data_var.to_string();
        for i in 0..20 {
            let cur_size = format!("{}", 2u32.pow(i));
            contract.push('\n');
            contract.push_str(&format!(
                "(var-set XZ (concat (unwrap-panic (as-max-len? (var-get XZ) u{}))
                                             (unwrap-panic (as-max-len? (var-get XZ) u{}))))",
                cur_size, cur_size
            ));
        }
        for i in 0..EXPLODE_N {
            let exploder = format!("(define-data-var var-{} (buff 1048576) (var-get XZ))", i);
            contract.push('\n');
            contract.push_str(&exploder);
        }

        conn.as_transaction(|conn| {
            let (mut ct_ast, ct_analysis) = conn
                .analyze_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &contract,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            assert!(format!(
                "{:?}",
                conn.initialize_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &mut ct_ast,
                    &ct_analysis,
                    &contract,
                    None,
                    |_, _| { false }
                )
                .unwrap_err()
            )
            .contains("MemoryBalanceExceeded"));
        });
    }
}

#[apply(test_clarity_versions)]
pub fn let_memory_test(#[case] clarity_version: ClarityVersion, #[case] epoch_id: StacksEpochId) {
    let marf = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, CHAIN_ID_TESTNET, marf);
    let EXPLODE_N = 100;
    let burn_db = &generate_test_burn_state_db(epoch_id);

    let contract_identifier = QualifiedContractIdentifier::local("foo").unwrap();

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    {
        let mut conn = new_block(
            &mut clarity_instance,
            &StacksBlockId([0; 32]),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let define_data_var = "(define-constant buff-0 0x00)";

        let mut contract = define_data_var.to_string();
        for i in 0..20 {
            contract.push('\n');
            contract.push_str(&format!(
                "(define-constant buff-{} (concat buff-{} buff-{}))",
                i + 1,
                i,
                i
            ));
        }

        contract.push('\n');
        contract.push_str("(let (");

        for i in 0..EXPLODE_N {
            let exploder = format!("(var-{} buff-20) ", i);
            contract.push_str(&exploder);
        }

        contract.push_str(") 1)");

        conn.as_transaction(|conn| {
            let (mut ct_ast, ct_analysis) = conn
                .analyze_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &contract,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            assert!(format!(
                "{:?}",
                conn.initialize_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &mut ct_ast,
                    &ct_analysis,
                    &contract,
                    None,
                    |_, _| { false }
                )
                .unwrap_err()
            )
            .contains("MemoryBalanceExceeded"));
        });
    }
}

#[apply(test_clarity_versions)]
pub fn argument_memory_test(
    #[case] clarity_version: ClarityVersion,
    #[case] epoch_id: StacksEpochId,
) {
    let marf = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, CHAIN_ID_TESTNET, marf);
    let EXPLODE_N = 100;

    let contract_identifier = QualifiedContractIdentifier::local("foo").unwrap();
    let burn_db = &generate_test_burn_state_db(epoch_id);

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    {
        let mut conn = new_block(
            &mut clarity_instance,
            &StacksBlockId([0; 32]),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let define_data_var = "(define-constant buff-0 0x00)";

        let mut contract = define_data_var.to_string();
        for i in 0..20 {
            contract.push('\n');
            contract.push_str(&format!(
                "(define-constant buff-{} (concat buff-{} buff-{}))",
                i + 1,
                i,
                i
            ));
        }

        contract.push('\n');
        contract.push_str("(is-eq ");

        for _i in 0..EXPLODE_N {
            let exploder = "buff-20 ";
            contract.push_str(exploder);
        }

        contract.push(')');

        conn.as_transaction(|conn| {
            let (mut ct_ast, ct_analysis) = conn
                .analyze_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &contract,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            assert!(format!(
                "{:?}",
                conn.initialize_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &mut ct_ast,
                    &ct_analysis,
                    &contract,
                    None,
                    |_, _| { false }
                )
                .unwrap_err()
            )
            .contains("MemoryBalanceExceeded"));
        });
    }
}

#[apply(test_clarity_versions)]
pub fn fcall_memory_test(#[case] clarity_version: ClarityVersion, #[case] epoch_id: StacksEpochId) {
    let marf = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, CHAIN_ID_TESTNET, marf);
    let COUNT_PER_FUNC = 10;
    let FUNCS = 10;
    let burn_db = &generate_test_burn_state_db(epoch_id);

    let contract_identifier = QualifiedContractIdentifier::local("foo").unwrap();

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    {
        let mut conn = new_block(
            &mut clarity_instance,
            &StacksBlockId([0; 32]),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let define_data_var = "(define-constant buff-0 0x00)";

        let mut contract = define_data_var.to_string();
        for i in 0..20 {
            contract.push('\n');
            contract.push_str(&format!(
                "(define-constant buff-{} (concat buff-{} buff-{}))",
                i + 1,
                i,
                i
            ));
        }

        contract.push('\n');

        for i in 0..FUNCS {
            contract.push_str(&format!("(define-private (call-{})\n", i));

            contract.push_str("(let (");

            for j in 0..COUNT_PER_FUNC {
                let exploder = format!("(var-{} buff-20) ", j);
                contract.push_str(&exploder);
            }

            if i == 0 {
                contract.push_str(") 1) )\n");
            } else {
                contract.push_str(&format!(") (call-{})) )\n", i - 1));
            }
        }

        let mut contract_ok = contract.clone();
        let mut contract_err = contract.clone();

        contract_ok.push_str("(call-0)");
        contract_err.push_str("(call-9)");

        eprintln!("{}", contract_ok);
        eprintln!("{}", contract_err);

        conn.as_transaction(|conn| {
            let (mut ct_ast, ct_analysis) = conn
                .analyze_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &contract_ok,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            assert!(match conn
                .initialize_smart_contract(
                    // initialize the ok contract without errs, but still abort.
                    &contract_identifier,
                    clarity_version,
                    &mut ct_ast,
                    &ct_analysis,
                    &contract_ok,
                    None,
                    |_, _| true
                )
                .unwrap_err()
            {
                ClarityError::AbortedByCallback(..) => true,
                _ => false,
            });
        });

        conn.as_transaction(|conn| {
            let (mut ct_ast, ct_analysis) = conn
                .analyze_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &contract_err,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            assert!(format!(
                "{:?}",
                conn.initialize_smart_contract(
                    &contract_identifier,
                    clarity_version,
                    &mut ct_ast,
                    &ct_analysis,
                    &contract_err,
                    None,
                    |_, _| false
                )
                .unwrap_err()
            )
            .contains("MemoryBalanceExceeded"));
        });
    }
}

#[apply(test_clarity_versions)]
pub fn ccall_memory_test(#[case] clarity_version: ClarityVersion, #[case] epoch_id: StacksEpochId) {
    let marf = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, CHAIN_ID_TESTNET, marf);
    let COUNT_PER_CONTRACT = 20;
    let CONTRACTS = 5;
    let burn_db = &generate_test_burn_state_db(epoch_id);

    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockId([0; 32]),
            &TEST_HEADER_DB,
            burn_db,
        )
        .commit_block();

    {
        let mut conn = new_block(
            &mut clarity_instance,
            &StacksBlockId([0; 32]),
            &StacksBlockId([1; 32]),
            &TEST_HEADER_DB,
            burn_db,
        );

        let define_data_var = "(define-constant buff-0 0x00)\n";

        let mut contract = define_data_var.to_string();
        for i in 0..20 {
            contract.push_str(&format!(
                "(define-constant buff-{} (concat buff-{} buff-{}))\n",
                i + 1,
                i,
                i
            ));
        }

        for i in 0..COUNT_PER_CONTRACT {
            contract.push_str(&format!("(define-constant var-{} buff-20)\n", i));
        }

        contract.push_str("(define-public (call)\n");

        let mut contracts = vec![];

        for i in 0..CONTRACTS {
            let mut my_contract = contract.clone();
            if i == 0 {
                my_contract.push_str("(ok 1))\n");
            } else {
                my_contract.push_str(&format!("(contract-call? .contract-{} call))\n", i - 1));
            }
            my_contract.push_str("(call)\n");
            contracts.push(my_contract);
        }

        for (i, contract) in contracts.into_iter().enumerate() {
            let contract_name = format!("contract-{}", i);
            let contract_identifier = QualifiedContractIdentifier::local(&contract_name).unwrap();

            if i < (CONTRACTS - 1) {
                conn.as_transaction(|conn| {
                    let (mut ct_ast, ct_analysis) = conn
                        .analyze_smart_contract(
                            &contract_identifier,
                            clarity_version,
                            &contract,
                            ASTRules::PrecheckSize,
                        )
                        .unwrap();
                    conn.initialize_smart_contract(
                        &contract_identifier,
                        clarity_version,
                        &mut ct_ast,
                        &ct_analysis,
                        &contract,
                        None,
                        |_, _| false,
                    )
                    .unwrap();
                    conn.save_analysis(&contract_identifier, &ct_analysis)
                        .unwrap();
                });
            } else {
                conn.as_transaction(|conn| {
                    let (mut ct_ast, ct_analysis) = conn
                        .analyze_smart_contract(
                            &contract_identifier,
                            clarity_version,
                            &contract,
                            ASTRules::PrecheckSize,
                        )
                        .unwrap();
                    assert!(format!(
                        "{:?}",
                        conn.initialize_smart_contract(
                            &contract_identifier,
                            clarity_version,
                            &mut ct_ast,
                            &ct_analysis,
                            &contract,
                            None,
                            |_, _| false
                        )
                        .unwrap_err()
                    )
                    .contains("MemoryBalanceExceeded"));
                });
            }
        }
    }
}

#[test]
fn test_deep_tuples() {
    let mut clarity = ClarityInstance::new(false, CHAIN_ID_TESTNET, MarfedKV::temporary());
    let p1 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR")
            .unwrap(),
    );
    let p2 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G")
            .unwrap(),
    );
    let contract_identifier = QualifiedContractIdentifier::local("tokens").unwrap();

    for (i, version) in [ClarityVersion::Clarity1, ClarityVersion::Clarity2]
        .iter()
        .enumerate()
    {
        let mut block = clarity.begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &test_block_headers(i as u8),
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB,
        );
        if *version == ClarityVersion::Clarity2 {
            block.set_epoch(StacksEpochId::Epoch21);
        } else {
            block.set_epoch(StacksEpochId::Epoch2_05);
        }

        let stack_limit =
            (AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1) as usize;

        let meets_stack_depth_tuple = format!("{}u1 {}", "{ a : ".repeat(31), "} ".repeat(31));
        let exceeds_stack_depth_tuple = format!("{}u1 {}", "{ a : ".repeat(32), "} ".repeat(32));

        let _res = block.as_transaction(|tx| {
            //  basically, without the new stack depth checks in the lexer/parser,
            //    and without the VaryStackDepthChecker, this next call will return a checkerror
            let analysis_resp = tx.analyze_smart_contract(
                &contract_identifier,
                *version,
                &meets_stack_depth_tuple,
                ASTRules::PrecheckSize,
            );
            eprintln!(
                "analyze_smart_contract() with meets_stack_depth_tuple: {}",
                analysis_resp.is_ok()
            );
            analysis_resp.unwrap()
        });

        let error = block.as_transaction(|tx| {
            if *version == ClarityVersion::Clarity2 {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch21);
            } else {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch2_05);
            }

            //  basically, without the new stack depth checks in the lexer/parser,
            //    and without the VaryStackDepthChecker, this next call will return a checkerror
            let analysis_resp = tx.analyze_smart_contract(
                &contract_identifier,
                *version,
                &exceeds_stack_depth_tuple,
                ASTRules::PrecheckSize,
            );
            analysis_resp.unwrap_err()
        });

        match error {
            ClarityError::Interpreter(InterpreterError::Runtime(r_e, _)) => {
                eprintln!("Runtime error: {:?}", r_e);
            }
            other => {
                eprintln!("Other error: {:?}", other);
            }
        }

        block.rollback_block();
    }
}

#[test]
fn test_deep_tuples_ast_precheck() {
    let mut clarity = ClarityInstance::new(false, CHAIN_ID_TESTNET, MarfedKV::temporary());
    let p1 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR")
            .unwrap(),
    );
    let p2 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G")
            .unwrap(),
    );
    let contract_identifier = QualifiedContractIdentifier::local("tokens").unwrap();

    for (i, version) in [ClarityVersion::Clarity1, ClarityVersion::Clarity2]
        .iter()
        .enumerate()
    {
        let mut block = clarity.begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &test_block_headers(i as u8),
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB_AST_PRECHECK,
        );
        if *version == ClarityVersion::Clarity2 {
            block.set_epoch(StacksEpochId::Epoch21);
        } else {
            block.set_epoch(StacksEpochId::Epoch2_05);
        }

        let stack_limit =
            (AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1) as usize;

        // absurdly deep tuple depth
        let exceeds_stack_depth_tuple = format!(
            "{}u1 {}",
            "{ a : ".repeat(stack_limit + 1024 * 128),
            "} ".repeat(stack_limit + 1024 * 128)
        );

        let error = block.as_transaction(|tx| {
            if *version == ClarityVersion::Clarity2 {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch21);
            } else {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch2_05);
            }
            //  basically, without the new stack depth checks in the lexer/parser,
            //    and without the VaryStackDepthChecker, this next call will return a checkerror
            let analysis_resp = tx.analyze_smart_contract(
                &contract_identifier,
                *version,
                &exceeds_stack_depth_tuple,
                ASTRules::PrecheckSize,
            );
            analysis_resp.unwrap_err()
        });

        match error {
            ClarityError::Interpreter(InterpreterError::Runtime(r_e, _)) => {
                eprintln!("Runtime error: {:?}", r_e);
            }
            other => {
                eprintln!("Other error: {:?}", other);
            }
        }

        block.rollback_block();
    }
}

#[test]
fn test_deep_type_nesting() {
    let mut clarity = ClarityInstance::new(false, CHAIN_ID_TESTNET, MarfedKV::temporary());
    let p1 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR")
            .unwrap(),
    );
    let p2 = PrincipalData::from(
        PrincipalData::parse_standard_principal("SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G")
            .unwrap(),
    );
    let contract_identifier = QualifiedContractIdentifier::local("tokens").unwrap();

    for (i, version) in [ClarityVersion::Clarity1, ClarityVersion::Clarity2]
        .iter()
        .enumerate()
    {
        let mut block = clarity.begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &test_block_headers(i as u8),
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB,
        );
        if *version == ClarityVersion::Clarity2 {
            block.set_epoch(StacksEpochId::Epoch21);
        } else {
            block.set_epoch(StacksEpochId::Epoch2_05);
        }

        let stack_limit =
            (AST_CALL_STACK_DEPTH_BUFFER + (MAX_CALL_STACK_DEPTH as u64) + 1) as usize;
        let mut parts = vec!["(a0 { a0 : u1 })".to_string()];
        for i in 1..1024 {
            parts.push(format!("(a{} {{ a{} : (print a{}) }})", i, i, i - 1));
        }

        let exceeds_type_depth = format!(
            "(let (
                {}
            )
                (print a31)
            )",
            &parts.join("\n")
        );

        let error = block.as_transaction(|tx| {
            if *version == ClarityVersion::Clarity2 {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch21);
            } else {
                assert_eq!(tx.get_epoch(), StacksEpochId::Epoch2_05);
            }
            //  basically, without the new stack depth checks in the lexer/parser,
            //    and without the VaryStackDepthChecker, this next call will return a checkerror
            let analysis_resp = tx.analyze_smart_contract(
                &contract_identifier,
                *version,
                &exceeds_type_depth,
                ASTRules::PrecheckSize,
            );
            analysis_resp.unwrap_err()
        });

        match error {
            ClarityError::Interpreter(InterpreterError::Runtime(r_e, _)) => {
                eprintln!("Runtime error: {:?}", r_e);
            }
            other => {
                eprintln!("Other error: {:?}", other);
            }
        }
        block.rollback_block();
    }
}
