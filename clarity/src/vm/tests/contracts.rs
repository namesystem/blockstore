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

#[cfg(any(test, feature = "testing"))]
use rstest::rstest;
use stacks_common::types::chainstate::BlockHeaderHash;
use stacks_common::types::StacksEpochId;

use crate::vm::ast::errors::ParseErrors;
use crate::vm::ast::ASTRules;
use crate::vm::contexts::Environment;
use crate::vm::errors::{CheckErrors, Error, RuntimeErrorType};
use crate::vm::tests::{
    env_factory, execute, is_committed, is_err_code_i128 as is_err_code, symbols_from_values,
    test_clarity_versions, test_epochs, tl_env_factory, MemoryEnvironmentGenerator,
    TopLevelMemoryEnvironmentGenerator,
};
use crate::vm::types::{
    OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData, StandardPrincipalData,
    TypeSignature, Value,
};
use crate::vm::{execute as vm_execute, ClarityVersion, ContractContext};

const FACTORIAL_CONTRACT: &str = "(define-map factorials { id: int } { current: int, index: int })
         (define-private (init-factorial (id int) (factorial int))
           (print (map-insert factorials (tuple (id id)) (tuple (current 1) (index factorial)))))
         (define-public (compute (id int))
           (let ((entry (unwrap! (map-get? factorials (tuple (id id)))
                                 (err false))))
                    (let ((current (get current entry))
                          (index   (get index entry)))
                         (if (<= index 1)
                             (ok true)
                             (begin
                               (map-set factorials (tuple (id id))
                                                      (tuple (current (* current index))
                                                             (index (- index 1))))
                               (ok false))))))
        (begin (init-factorial 1337 3)
               (init-factorial 8008 5))";

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

fn get_principal() -> Value {
    StandardPrincipalData::transient().into()
}

fn get_principal_as_principal_data() -> PrincipalData {
    StandardPrincipalData::transient().into()
}

#[apply(test_epochs)]
fn test_get_block_info_eval(
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let contracts = [
        "(define-private (test-func) (get-block-info? time u1))",
        "(define-private (test-func) (get-block-info? time block-height))",
        "(define-private (test-func) (get-block-info? time u100000))",
        "(define-private (test-func) (get-block-info? time (- 1)))",
        "(define-private (test-func) (get-block-info? time true))",
        "(define-private (test-func) (get-block-info? header-hash u1))",
        "(define-private (test-func) (get-block-info? burnchain-header-hash u1))",
        "(define-private (test-func) (get-block-info? vrf-seed u1))",
    ];

    let expected = [
        Ok(Value::none()),
        Ok(Value::none()),
        Ok(Value::none()),
        Err(CheckErrors::TypeValueError(TypeSignature::UIntType, Value::Int(-1)).into()),
        Err(CheckErrors::TypeValueError(TypeSignature::UIntType, Value::Bool(true)).into()),
        Ok(Value::none()),
        Ok(Value::none()),
        Ok(Value::none()),
    ];

    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let mut owned_env = tl_env_factory.get_env(epoch);
    for i in 0..contracts.len() {
        let contract_identifier =
            QualifiedContractIdentifier::local(&format!("test-contract-{}", i)).unwrap();
        owned_env
            .initialize_versioned_contract(
                contract_identifier.clone(),
                ClarityVersion::Clarity2,
                contracts[i],
                None,
                ASTRules::PrecheckSize,
            )
            .unwrap();

        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);
        eprintln!("{}", contracts[i]);
        let eval_result = env.eval_read_only(&contract_identifier, "(test-func)");
        match expected[i] {
            // any (some UINT) is okay for checking get-block-info? time
            Ok(Value::UInt(0)) => {
                assert!(
                    if let Ok(Value::Optional(OptionalData { data: Some(x) })) = eval_result {
                        matches!(*x, Value::UInt(_))
                    } else {
                        false
                    }
                );
            }
            _ => assert_eq!(expected[i], eval_result),
        }
    }
}

#[apply(test_epochs)]
fn test_contract_caller(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);
    let contract_a = "(define-read-only (get-caller)
           (list contract-caller tx-sender))";
    let contract_b = "(define-read-only (get-caller)
           (list contract-caller tx-sender))
         (define-read-only (as-contract-get-caller)
           (as-contract (get-caller)))
         (define-read-only (cc-get-caller)
           (contract-call? .contract-a get-caller))
         (define-read-only (as-contract-cc-get-caller)
           (as-contract (contract-call? .contract-a get-caller)))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    {
        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-a").unwrap(),
            contract_a,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-b").unwrap(),
            contract_b,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    }

    {
        let c_b = Value::from(PrincipalData::Contract(
            QualifiedContractIdentifier::local("contract-b").unwrap(),
        ));
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone().expect_principal().unwrap()),
            None,
            &mut placeholder_context,
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-a").unwrap(),
                "get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![p1.clone(), p1.clone()]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "as-contract-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), c_b.clone()]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "cc-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), p1]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "as-contract-cc-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), c_b]).unwrap()
        );
    }
}

fn tx_sponsor_contract_asserts(env: &mut Environment, sponsor: Option<PrincipalData>) {
    let sponsor = match sponsor {
        None => Value::none(),
        Some(p) => Value::some(Value::Principal(p)).unwrap(),
    };
    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-a").unwrap(),
            "get-sponsor",
            &[],
            false
        )
        .unwrap(),
        Value::cons_list_unsanitized(vec![sponsor.clone()]).unwrap()
    );
    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-b").unwrap(),
            "as-contract-get-sponsor",
            &[],
            false
        )
        .unwrap(),
        Value::cons_list_unsanitized(vec![sponsor.clone()]).unwrap()
    );
    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-b").unwrap(),
            "cc-get-sponsor",
            &[],
            false
        )
        .unwrap(),
        Value::cons_list_unsanitized(vec![sponsor.clone()]).unwrap()
    );
    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-b").unwrap(),
            "as-contract-cc-get-sponsor",
            &[],
            false
        )
        .unwrap(),
        Value::cons_list_unsanitized(vec![sponsor]).unwrap()
    );
}

#[apply(test_epochs)]
fn test_tx_sponsor(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);

    let contract_a = "(define-read-only (get-sponsor)
           (list tx-sponsor?))
           (asserts! (is-eq tx-sponsor? (some 'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G)) (err 1))";
    let contract_b = "(define-read-only (get-sponsor)
           (list tx-sponsor?))
         (define-read-only (as-contract-get-sponsor)
           (as-contract (get-sponsor)))
         (define-read-only (cc-get-sponsor)
           (contract-call? .contract-a get-sponsor))
         (define-read-only (as-contract-cc-get-sponsor)
           (as-contract (contract-call? .contract-a get-sponsor)))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR")
        .expect_principal()
        .unwrap();
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");
    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let sponsor = if let Value::Principal(p) = p2 {
        Some(p)
    } else {
        panic!("p2 is not a principal value");
    };

    {
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone()),
            sponsor.clone(),
            &mut placeholder_context,
        );
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-a").unwrap(),
            contract_a,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-b").unwrap(),
            contract_b,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    }

    // Sponsor is equal to some(principal) in this code block.
    {
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone()),
            sponsor.clone(),
            &mut placeholder_context,
        );
        tx_sponsor_contract_asserts(&mut env, sponsor);
    }

    // Sponsor is none in this code block.
    {
        let sponsor = None;
        let mut env =
            owned_env.get_exec_environment(Some(p1), sponsor.clone(), &mut placeholder_context);
        tx_sponsor_contract_asserts(&mut env, sponsor);
    }
}

#[apply(test_epochs)]
fn test_fully_qualified_contract_call(
    epoch: StacksEpochId,
    mut env_factory: MemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);

    let contract_a = "(define-read-only (get-caller)
           (list contract-caller tx-sender))";
    let contract_b = "(define-read-only (get-caller)
           (list contract-caller tx-sender))
         (define-read-only (as-contract-get-caller)
           (as-contract (get-caller)))
         (define-read-only (cc-get-caller)
           (contract-call? 'S1G2081040G2081040G2081040G208105NK8PE5.contract-a get-caller))
         (define-read-only (as-contract-cc-get-caller)
           (as-contract (contract-call? .contract-a get-caller)))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    {
        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-a").unwrap(),
            contract_a,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        env.initialize_contract(
            QualifiedContractIdentifier::local("contract-b").unwrap(),
            contract_b,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    }

    {
        let c_b = Value::from(PrincipalData::Contract(
            QualifiedContractIdentifier::local("contract-b").unwrap(),
        ));
        let mut env = owned_env.get_exec_environment(
            Some(p1.clone().expect_principal().unwrap()),
            None,
            &mut placeholder_context,
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-a").unwrap(),
                "get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![p1.clone(), p1.clone()]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "as-contract-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), c_b.clone()]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "cc-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), p1]).unwrap()
        );
        assert_eq!(
            env.execute_contract(
                &QualifiedContractIdentifier::local("contract-b").unwrap(),
                "as-contract-cc-get-caller",
                &[],
                false
            )
            .unwrap(),
            Value::cons_list_unsanitized(vec![c_b.clone(), c_b]).unwrap()
        );
    }
}

#[apply(test_epochs)]
fn test_simple_naming_system(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);

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
    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    {
        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

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
            &mut placeholder_context,
        );

        assert!(is_err_code(
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
            &mut placeholder_context,
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
        assert!(is_err_code(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_0, Value::UInt(1000)]),
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
            &mut placeholder_context,
        );
        assert!(is_err_code(
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
            Some(p1.expect_principal().unwrap()),
            None,
            &mut placeholder_context,
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
            &mut placeholder_context,
        );
        assert!(is_committed(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "preorder",
                &symbols_from_values(vec![name_hash_expensive_1, Value::UInt(100)]),
                false
            )
            .unwrap()
        ));
        assert!(is_err_code(
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
                &symbols_from_values(vec![name_hash_cheap_0, Value::UInt(100)]),
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
        assert!(is_err_code(
            &env.execute_contract(
                &QualifiedContractIdentifier::local("names").unwrap(),
                "register",
                &symbols_from_values(vec![p2, Value::Int(100001), Value::Int(0)]),
                false
            )
            .unwrap(),
            5
        ));
    }
}

#[apply(test_epochs)]
fn test_simple_contract_call(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);

    let contract_1 = FACTORIAL_CONTRACT;
    let contract_2 = "(define-public (proxy-compute)
            (contract-call? .factorial-contract compute 8008))
        ";

    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let mut env = owned_env.get_exec_environment(
        Some(get_principal().expect_principal().unwrap()),
        None,
        &mut placeholder_context,
    );

    let contract_identifier = QualifiedContractIdentifier::local("factorial-contract").unwrap();
    env.initialize_contract(contract_identifier, contract_1, ASTRules::PrecheckSize)
        .unwrap();

    let contract_identifier = QualifiedContractIdentifier::local("proxy-compute").unwrap();
    env.initialize_contract(contract_identifier, contract_2, ASTRules::PrecheckSize)
        .unwrap();

    let args = symbols_from_values(vec![]);

    let expected = [
        Value::Int(5),
        Value::Int(20),
        Value::Int(60),
        Value::Int(120),
        Value::Int(120),
        Value::Int(120),
    ];
    for expected_result in &expected {
        env.execute_contract(
            &QualifiedContractIdentifier::local("proxy-compute").unwrap(),
            "proxy-compute",
            &args,
            false,
        )
        .unwrap();
        assert_eq!(
            env.eval_read_only(
                &QualifiedContractIdentifier::local("factorial-contract").unwrap(),
                "(get current (unwrap! (map-get? factorials {id: 8008}) false))"
            )
            .unwrap(),
            *expected_result
        );
    }
}

#[apply(test_epochs)]
fn test_aborts(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);

    let contract_1 = "
(define-map data { id: int } { value: int })

;; this will return false if id != value,
;;   which _aborts_ any data that is modified during
;;   the routine.
(define-public (modify-data
                 (id int)
                 (value int))
   (begin
     (map-set data (tuple (id id))
                      (tuple (value value)))
     (if (is-eq id value)
         (ok 1)
         (err 1))))

(define-private (get-data (id int))
  (default-to 0
    (get value
     (map-get? data (tuple (id id))))))
";

    let contract_2 = "
(define-public (fail-in-other)
  (begin
    (contract-call? .contract-1 modify-data 100 101)
    (ok 1)))

(define-public (fail-in-self)
  (begin
    (contract-call? .contract-1 modify-data 105 105)
    (err 1)))
";
    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    let contract_identifier = QualifiedContractIdentifier::local("contract-1").unwrap();
    env.initialize_contract(contract_identifier, contract_1, ASTRules::PrecheckSize)
        .unwrap();

    let contract_identifier = QualifiedContractIdentifier::local("contract-2").unwrap();
    env.initialize_contract(contract_identifier, contract_2, ASTRules::PrecheckSize)
        .unwrap();

    env.sender = Some(get_principal_as_principal_data());

    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "modify-data",
            &symbols_from_values(vec![Value::Int(10), Value::Int(10)]),
            false
        )
        .unwrap(),
        Value::Response(ResponseData {
            committed: true,
            data: Box::new(Value::Int(1))
        })
    );

    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "modify-data",
            &symbols_from_values(vec![Value::Int(20), Value::Int(10)]),
            false
        )
        .unwrap(),
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(Value::Int(1))
        })
    );

    assert_eq!(
        env.eval_read_only(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "(get-data 20)"
        )
        .unwrap(),
        Value::Int(0)
    );

    assert_eq!(
        env.eval_read_only(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "(get-data 10)"
        )
        .unwrap(),
        Value::Int(10)
    );

    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-2").unwrap(),
            "fail-in-other",
            &symbols_from_values(vec![]),
            false
        )
        .unwrap(),
        Value::Response(ResponseData {
            committed: true,
            data: Box::new(Value::Int(1))
        })
    );

    assert_eq!(
        env.execute_contract(
            &QualifiedContractIdentifier::local("contract-2").unwrap(),
            "fail-in-self",
            &symbols_from_values(vec![]),
            false
        )
        .unwrap(),
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(Value::Int(1))
        })
    );

    assert_eq!(
        env.eval_read_only(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "(get-data 105)"
        )
        .unwrap(),
        Value::Int(0)
    );

    assert_eq!(
        env.eval_read_only(
            &QualifiedContractIdentifier::local("contract-1").unwrap(),
            "(get-data 100)"
        )
        .unwrap(),
        Value::Int(0)
    );
}

#[apply(test_epochs)]
fn test_factorial_contract(epoch: StacksEpochId, mut env_factory: MemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);

    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    let contract_identifier = QualifiedContractIdentifier::local("factorial").unwrap();
    env.initialize_contract(
        contract_identifier,
        FACTORIAL_CONTRACT,
        ASTRules::PrecheckSize,
    )
    .unwrap();

    let tx_name = "compute";
    let arguments_to_test = [
        symbols_from_values(vec![Value::Int(1337)]),
        symbols_from_values(vec![Value::Int(1337)]),
        symbols_from_values(vec![Value::Int(1337)]),
        symbols_from_values(vec![Value::Int(1337)]),
        symbols_from_values(vec![Value::Int(1337)]),
        symbols_from_values(vec![Value::Int(8008)]),
        symbols_from_values(vec![Value::Int(8008)]),
        symbols_from_values(vec![Value::Int(8008)]),
        symbols_from_values(vec![Value::Int(8008)]),
        symbols_from_values(vec![Value::Int(8008)]),
        symbols_from_values(vec![Value::Int(8008)]),
    ];

    let expected = vec![
        Value::Int(3),
        Value::Int(6),
        Value::Int(6),
        Value::Int(6),
        Value::Int(6),
        Value::Int(5),
        Value::Int(20),
        Value::Int(60),
        Value::Int(120),
        Value::Int(120),
        Value::Int(120),
    ];

    env.sender = Some(get_principal_as_principal_data());

    for (arguments, expectation) in arguments_to_test.iter().zip(expected.iter()) {
        env.execute_contract(
            &QualifiedContractIdentifier::local("factorial").unwrap(),
            tx_name,
            arguments,
            false,
        )
        .unwrap();

        assert_eq!(
            *expectation,
            env.eval_read_only(
                &QualifiedContractIdentifier::local("factorial").unwrap(),
                &format!(
                    "(unwrap! (get current (map-get? factorials (tuple (id {})))) false)",
                    arguments[0]
                )
            )
            .unwrap()
        );
    }

    let err_result = env
        .execute_contract(
            &QualifiedContractIdentifier::local("factorial").unwrap(),
            "init-factorial",
            &symbols_from_values(vec![Value::Int(9000), Value::Int(15)]),
            false,
        )
        .unwrap_err();
    assert!(matches!(
        err_result,
        Error::Unchecked(CheckErrors::NoSuchPublicFunction(_, _))
    ));

    let err_result = env
        .execute_contract(
            &QualifiedContractIdentifier::local("factorial").unwrap(),
            "compute",
            &symbols_from_values(vec![Value::Bool(true)]),
            false,
        )
        .unwrap_err();
    assert!(matches!(
        err_result,
        Error::Unchecked(CheckErrors::TypeValueError(_, _))
    ));
}

#[apply(test_epochs)]
fn test_at_unknown_block(
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract = "(define-data-var foo int 3)
                        (at-block 0x0202020202020202020202020202020202020202020202020202020202020202
                          (+ 1 2))";
    let err = owned_env
        .initialize_contract(
            QualifiedContractIdentifier::local("contract").unwrap(),
            contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
    eprintln!("{}", err);
    match err {
        Error::Runtime(x, _) => assert_eq!(
            x,
            RuntimeErrorType::UnknownBlockHeaderHash(BlockHeaderHash::from(
                vec![2_u8; 32].as_slice()
            ))
        ),
        _ => panic!("Unexpected error"),
    }
}

#[apply(test_epochs)]
fn test_as_max_len(epoch: StacksEpochId, mut tl_env_factory: TopLevelMemoryEnvironmentGenerator) {
    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract = "(define-data-var token-ids (list 10 uint) (list))
                        (var-set token-ids
                           (unwrap! (as-max-len? (append (var-get token-ids) u1) u10) (err 10)))";

    owned_env
        .initialize_contract(
            QualifiedContractIdentifier::local("contract").unwrap(),
            contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
}

#[test]
fn test_ast_stack_depth() {
    let program = "(+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       1 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)

                      ";
    assert_eq!(
        vm_execute(program).unwrap_err(),
        RuntimeErrorType::ASTError(ParseErrors::VaryExpressionStackDepthTooDeep.into()).into()
    );
}

#[test]
fn test_arg_stack_depth() {
    let program = "(define-private (foo)
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       bar 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1))
                       (define-private (bar)
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       1 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1))
                       (foo)
                      ";
    assert_eq!(
        vm_execute(program).unwrap_err(),
        RuntimeErrorType::MaxStackDepthReached.into()
    );
}

#[apply(test_clarity_versions)]
fn test_cc_stack_depth(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut env_factory: MemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);
    let contract_one = "(define-public (foo)
                        (ok (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       1 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)))";
    let contract_two =
                      "(define-private (bar)
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (unwrap-panic (contract-call? .c-foo foo ) )
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1))
                       (bar)
                      ";
    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);
    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    let contract_identifier = QualifiedContractIdentifier::local("c-foo").unwrap();
    env.initialize_contract(contract_identifier, contract_one, ASTRules::PrecheckSize)
        .unwrap();

    let contract_identifier = QualifiedContractIdentifier::local("c-bar").unwrap();
    assert_eq!(
        env.initialize_contract(contract_identifier, contract_two, ASTRules::PrecheckSize)
            .unwrap_err(),
        RuntimeErrorType::MaxStackDepthReached.into()
    );
}

#[apply(test_clarity_versions)]
fn test_cc_trait_stack_depth(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut env_factory: MemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);

    let contract_one = "(define-public (foo)
                        (ok (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                       1 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)))";
    let contract_two =
                      "(define-trait trait-1 (
                        (foo () (response int int))))
                       (define-private (bar (F <trait-1>))
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+
                        (unwrap-panic (contract-call? F foo))
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)
                         1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1) 1))
                       (bar .c-foo)
                      ";

    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);
    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    let contract_identifier = QualifiedContractIdentifier::local("c-foo").unwrap();
    env.initialize_contract(contract_identifier, contract_one, ASTRules::PrecheckSize)
        .unwrap();

    let contract_identifier = QualifiedContractIdentifier::local("c-bar").unwrap();
    assert_eq!(
        env.initialize_contract(contract_identifier, contract_two, ASTRules::PrecheckSize)
            .unwrap_err(),
        RuntimeErrorType::MaxStackDepthReached.into()
    );
}

#[apply(test_epochs)]
fn test_eval_with_non_existing_contract(
    epoch: StacksEpochId,
    mut env_factory: MemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);

    let mut placeholder_context = ContractContext::new(
        QualifiedContractIdentifier::transient(),
        ClarityVersion::Clarity2,
    );

    let mut env = owned_env.get_exec_environment(
        Some(get_principal().expect_principal().unwrap()),
        None,
        &mut placeholder_context,
    );

    let result = env.eval_read_only(
        &QualifiedContractIdentifier::local("absent").unwrap(),
        "(ok 0)",
    );
    assert_eq!(
        result.as_ref().unwrap_err(),
        &Error::Unchecked(CheckErrors::NoSuchContract(
            QualifiedContractIdentifier::local("absent")
                .unwrap()
                .to_string()
        ))
    );
    drop(env);
    owned_env.commit().unwrap();
    assert!(owned_env.destruct().is_some());
}
