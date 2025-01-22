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

#[cfg(any(test, feature = "testing"))]
use rstest::rstest;
use stacks_common::types::StacksEpochId;

#[cfg(test)]
use crate::vm::analysis::type_checker::v2_1::tests::contracts::type_check_version;
use crate::vm::analysis::{run_analysis, CheckError};
use crate::vm::ast::{parse, ASTRules};
use crate::vm::database::MemoryBackingStore;
use crate::vm::errors::{CheckErrors, Error};
use crate::vm::tests::{test_clarity_versions, tl_env_factory, TopLevelMemoryEnvironmentGenerator};
use crate::vm::types::{QualifiedContractIdentifier, Value};
use crate::vm::{ClarityVersion, ContractContext};

#[apply(test_clarity_versions)]
fn test_block_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let contract = "(define-read-only (test-func) block-height)";

    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);

    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract_identifier = QualifiedContractIdentifier::local("test-contract").unwrap();

    let mut exprs = parse(&contract_identifier, contract, version, epoch).unwrap();
    let mut marf = MemoryBackingStore::new();
    let mut db = marf.as_analysis_db();
    let analysis = db.execute(|db| {
        type_check_version(&contract_identifier, &mut exprs, db, true, epoch, version)
    });
    if version >= ClarityVersion::Clarity3 {
        let err = analysis.unwrap_err();
        assert_eq!(
            CheckErrors::UndefinedVariable("block-height".to_string()),
            err.err
        );
    } else {
        assert!(analysis.is_ok());
    }

    // Initialize the contract
    // Note that we're ignoring the analysis failure here so that we can test
    // the runtime behavior. In Clarity 3, if this case somehow gets past the
    // analysis, it should fail at runtime.
    let result = owned_env.initialize_versioned_contract(
        contract_identifier.clone(),
        version,
        contract,
        None,
        ASTRules::PrecheckSize,
    );

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    // Call the function
    let eval_result = env.eval_read_only(&contract_identifier, "(test-func)");
    // In Clarity 3, this should trigger a runtime error
    if version >= ClarityVersion::Clarity3 {
        let err = eval_result.unwrap_err();
        assert_eq!(
            Error::Unchecked(CheckErrors::UndefinedVariable("block-height".to_string(),)),
            err
        );
    } else {
        assert_eq!(Ok(Value::UInt(1)), eval_result);
    }
}

#[apply(test_clarity_versions)]
fn test_stacks_block_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let contract = "(define-read-only (test-func) stacks-block-height)";

    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);

    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract_identifier = QualifiedContractIdentifier::local("test-contract").unwrap();

    let mut exprs = parse(&contract_identifier, contract, version, epoch).unwrap();
    let mut marf = MemoryBackingStore::new();
    let mut db = marf.as_analysis_db();
    let analysis = db.execute(|db| {
        type_check_version(&contract_identifier, &mut exprs, db, true, epoch, version)
    });
    if version < ClarityVersion::Clarity3 {
        let err = analysis.unwrap_err();
        assert_eq!(
            CheckErrors::UndefinedVariable("stacks-block-height".to_string()),
            err.err
        );
    } else {
        assert!(analysis.is_ok());
    }

    // Initialize the contract
    // Note that we're ignoring the analysis failure here so that we can test
    // the runtime behavior. In Clarity 3, if this case somehow gets past the
    // analysis, it should fail at runtime.
    let result = owned_env.initialize_versioned_contract(
        contract_identifier.clone(),
        version,
        contract,
        None,
        ASTRules::PrecheckSize,
    );

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    // Call the function
    let eval_result = env.eval_read_only(&contract_identifier, "(test-func)");
    // In Clarity 3, this should trigger a runtime error
    if version < ClarityVersion::Clarity3 {
        let err = eval_result.unwrap_err();
        assert_eq!(
            Error::Unchecked(CheckErrors::UndefinedVariable(
                "stacks-block-height".to_string(),
            )),
            err
        );
    } else {
        assert_eq!(Ok(Value::UInt(1)), eval_result);
    }
}

#[apply(test_clarity_versions)]
fn test_tenure_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let contract = "(define-read-only (test-func) tenure-height)";

    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);

    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract_identifier = QualifiedContractIdentifier::local("test-contract").unwrap();

    let mut exprs = parse(&contract_identifier, contract, version, epoch).unwrap();
    let mut marf = MemoryBackingStore::new();
    let mut db = marf.as_analysis_db();
    let analysis = db.execute(|db| {
        type_check_version(&contract_identifier, &mut exprs, db, true, epoch, version)
    });
    if version < ClarityVersion::Clarity3 {
        let err = analysis.unwrap_err();
        assert_eq!(
            CheckErrors::UndefinedVariable("tenure-height".to_string()),
            err.err
        );
    } else {
        assert!(analysis.is_ok());
    }

    // Initialize the contract
    // Note that we're ignoring the analysis failure here so that we can test
    // the runtime behavior. In Clarity 3, if this case somehow gets past the
    // analysis, it should fail at runtime.
    let result = owned_env.initialize_versioned_contract(
        contract_identifier.clone(),
        version,
        contract,
        None,
        ASTRules::PrecheckSize,
    );

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    // Call the function
    let eval_result = env.eval_read_only(&contract_identifier, "(test-func)");
    // In Clarity 3, this should trigger a runtime error
    if version < ClarityVersion::Clarity3 {
        let err = eval_result.unwrap_err();
        assert_eq!(
            Error::Unchecked(CheckErrors::UndefinedVariable("tenure-height".to_string(),)),
            err
        );
    } else {
        assert_eq!(Ok(Value::UInt(1)), eval_result);
    }
}

#[derive(Debug, PartialEq)]
enum WhenError {
    Analysis,
    Initialization,
    Runtime,
    Never,
}

#[cfg(test)]
#[allow(clippy::type_complexity)]
fn expect_contract_error(
    version: ClarityVersion,
    epoch: StacksEpochId,
    tl_env_factory: &mut TopLevelMemoryEnvironmentGenerator,
    name: &str,
    contract: &str,
    expected_errors: &[(
        WhenError,
        fn(ClarityVersion, StacksEpochId) -> bool,
        CheckErrors,
    )],
    expected_success: Value,
) {
    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::local(name).unwrap(), version);

    let mut owned_env = tl_env_factory.get_env(epoch);
    let contract_identifier = QualifiedContractIdentifier::local(name).unwrap();

    let mut exprs = parse(&contract_identifier, contract, version, epoch).unwrap();
    let mut marf = MemoryBackingStore::new();
    let mut db = marf.as_analysis_db();
    let analysis = db.execute(|db| {
        type_check_version(&contract_identifier, &mut exprs, db, true, epoch, version)
    });

    for (when, err_condition, expected_error) in expected_errors {
        if *when == WhenError::Analysis && err_condition(version, epoch) {
            let err = analysis.unwrap_err();
            assert_eq!(*expected_error, err.err);

            // Do not continue with the test if the analysis failed.
            return;
        }
    }

    // The type-checker does not report an error for the reuse of the built-in
    // name `stacks-block-height`. It is instead caught at initialization. This
    // matches the behavior of Clarity 1 and 2.
    assert!(analysis.is_ok());

    // Initialize the contract
    // Note that we're ignoring the analysis failure here so that we can test
    // the runtime behavior. In Clarity 3, if this case somehow gets past the
    // analysis, it should fail at runtime.
    let init_result = owned_env.initialize_versioned_contract(
        contract_identifier.clone(),
        version,
        contract,
        None,
        ASTRules::PrecheckSize,
    );

    for (when, err_condition, expected_error) in expected_errors {
        if *when == WhenError::Initialization && err_condition(version, epoch) {
            let err = init_result.unwrap_err();
            if let Error::Unchecked(inner_err) = &err {
                assert_eq!(expected_error, inner_err);
            } else {
                panic!("Expected an Unchecked error, but got a different error");
            }

            // Do not continue with the test if the initialization failed.
            return;
        }
    }

    let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);

    // Call the function
    let eval_result = env.eval_read_only(&contract_identifier, "(test-func)");

    for (when, err_condition, expected_error) in expected_errors {
        if *when == WhenError::Runtime && err_condition(version, epoch) {
            let err = eval_result.unwrap_err();
            if let Error::Unchecked(inner_err) = &err {
                assert_eq!(expected_error, inner_err);
            } else {
                panic!("Expected an Unchecked error, but got a different error");
            }

            // Do not continue with the test if the evaluation failed.
            return;
        }
    }

    assert_eq!(Ok(expected_success), eval_result);
}

#[apply(test_clarity_versions)]
fn reuse_block_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    // data var
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "data-var",
        r#"
        (define-data-var block-height uint u1234)
        (define-read-only (test-func)
            (var-get block-height)
        )
        "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::UInt(1234),
    );

    // map
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "map",
        r#"
        (define-map block-height uint uint)
        (define-private (test-func)
            (map-insert block-height u1 u2)
        )
        "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(true),
    );

    // let
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "let",
        r#"
        (define-private (test-func)
            (let ((block-height 32))
                block-height
            )
        )
        "#,
        &[
            (
                WhenError::Runtime,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Int(32),
    );

    // match binding
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "match-binding",
        r#"
        (define-read-only (test-func)
          (let ((x (if true (ok u5) (err u7))))
            (match x
              block-height 3
              e 4
            )
          )
        )
        "#,
        &[
            (
                WhenError::Runtime,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Int(3),
    );

    // private function
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-private (block-height) true)
        (define-private (test-func) (block-height))
        "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(true),
    );

    // constant
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "constant",
        r#"
            (define-constant block-height u1234)
            (define-read-only (test-func) block-height)
            "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::UInt(1234),
    );

    // define-trait
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-trait block-height ())
            (define-read-only (test-func) false)
            "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(false),
    );

    // tuple
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "tuple",
        r#"
            (define-read-only (test-func)
                (get block-height { block-height: 1234 })
            )
            "#,
        &[],
        Value::Int(1234),
    );

    // define-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-fungible-token block-height)
            (define-read-only (test-func) false)
            "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(false),
    );

    // define-non-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-non-fungible-token block-height uint)
            (define-read-only (test-func) false)
            "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(false),
    );

    // define-public
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-public (block-height) (ok true))
        (define-private (test-func) (unwrap-panic (block-height)))
        "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(true),
    );

    // define-read-only
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-read-only (block-height) true)
        (define-private (test-func) (block-height))
        "#,
        &[
            (
                WhenError::Initialization,
                |version, _| version < ClarityVersion::Clarity3,
                CheckErrors::NameAlreadyUsed("block-height".to_string()),
            ),
            (
                WhenError::Analysis,
                |version, _| version >= ClarityVersion::Clarity3,
                CheckErrors::ReservedWord("block-height".to_string()),
            ),
        ],
        Value::Bool(true),
    );
}

#[apply(test_clarity_versions)]
fn reuse_stacks_block_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    // data var
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "data-var",
        r#"
        (define-data-var stacks-block-height uint u1234)
        (define-read-only (test-func)
            (var-get stacks-block-height)
        )
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::UInt(1234),
    );

    // map
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "map",
        r#"
        (define-map stacks-block-height uint uint)
        (define-private (test-func)
            (map-insert stacks-block-height u1 u2)
        )
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(true),
    );

    // let
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "let",
        r#"
        (define-private (test-func)
            (let ((stacks-block-height 32))
                stacks-block-height
            )
        )
        "#,
        &[(
            WhenError::Runtime,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Int(32),
    );

    // match binding
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "match-binding",
        r#"
        (define-read-only (test-func)
          (let ((x (if true (ok u5) (err u7))))
            (match x
              stacks-block-height 3
              e 4
            )
          )
        )
        "#,
        &[(
            WhenError::Runtime,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Int(3),
    );

    // function
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-private (stacks-block-height) true)
        (define-private (test-func) (stacks-block-height))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(true),
    );

    // constant
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "constant",
        r#"
            (define-constant stacks-block-height u1234)
            (define-read-only (test-func) stacks-block-height)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::UInt(1234),
    );

    // define-trait
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-trait stacks-block-height ())
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(false),
    );

    // tuple
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "tuple",
        r#"
            (define-read-only (test-func)
                (get stacks-block-height { stacks-block-height: 1234 })
            )
            "#,
        &[],
        Value::Int(1234),
    );

    // define-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-fungible-token stacks-block-height)
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(false),
    );

    // define-non-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-non-fungible-token stacks-block-height uint)
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(false),
    );

    // define-public
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-public (stacks-block-height) (ok true))
        (define-private (test-func) (unwrap-panic (stacks-block-height)))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(true),
    );

    // define-read-only
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-read-only (stacks-block-height) true)
        (define-private (test-func) (stacks-block-height))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("stacks-block-height".to_string()),
        )],
        Value::Bool(true),
    );
}

#[apply(test_clarity_versions)]
fn reuse_tenure_height(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut tl_env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    // data var
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "data-var",
        r#"
        (define-data-var tenure-height uint u1234)
        (define-read-only (test-func)
            (var-get tenure-height)
        )
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::UInt(1234),
    );

    // map
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "map",
        r#"
        (define-map tenure-height uint uint)
        (define-private (test-func)
            (map-insert tenure-height u1 u2)
        )
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(true),
    );

    // let
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "let",
        r#"
        (define-private (test-func)
            (let ((tenure-height 32))
                tenure-height
            )
        )
        "#,
        &[(
            WhenError::Runtime,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Int(32),
    );

    // match binding
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "match-binding",
        r#"
        (define-read-only (test-func)
          (let ((x (if true (ok u5) (err u7))))
            (match x
              tenure-height 3
              e 4
            )
          )
        )
        "#,
        &[(
            WhenError::Runtime,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Int(3),
    );

    // function
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-private (tenure-height) true)
        (define-private (test-func) (tenure-height))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(true),
    );

    // constant
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "constant",
        r#"
            (define-constant tenure-height u1234)
            (define-read-only (test-func) tenure-height)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::UInt(1234),
    );

    // define-trait
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-trait tenure-height ())
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(false),
    );

    // tuple
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "tuple",
        r#"
            (define-read-only (test-func)
                (get tenure-height { tenure-height: 1234 })
            )
            "#,
        &[],
        Value::Int(1234),
    );

    // define-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-fungible-token tenure-height)
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(false),
    );

    // define-non-fungible-token
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "trait",
        r#"
            (define-non-fungible-token tenure-height uint)
            (define-read-only (test-func) false)
            "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(false),
    );

    // define-public
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-public (tenure-height) (ok true))
        (define-private (test-func) (unwrap-panic (tenure-height)))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(true),
    );

    // define-read-only
    expect_contract_error(
        version,
        epoch,
        &mut tl_env_factory,
        "function",
        r#"
        (define-read-only (tenure-height) true)
        (define-private (test-func) (tenure-height))
        "#,
        &[(
            WhenError::Initialization,
            |version, _| version >= ClarityVersion::Clarity3,
            CheckErrors::NameAlreadyUsed("tenure-height".to_string()),
        )],
        Value::Bool(true),
    );
}
