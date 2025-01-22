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

use stacks_common::types::StacksEpochId;

use crate::vm::ast::ASTRules;
use crate::vm::contexts::{AssetMap, AssetMapEntry, OwnedEnvironment};
use crate::vm::errors::{CheckErrors, Error, RuntimeErrorType};
use crate::vm::events::StacksTransactionEvent;
use crate::vm::representations::SymbolicExpression;
use crate::vm::tests::{
    execute, is_committed, is_err_code, symbols_from_values, test_clarity_versions, test_epochs,
    tl_env_factory as env_factory, TopLevelMemoryEnvironmentGenerator,
};
use crate::vm::types::{AssetIdentifier, PrincipalData, QualifiedContractIdentifier, Value};
use crate::vm::version::ClarityVersion;
use crate::vm::ContractContext;

const FIRST_CLASS_TOKENS: &str = "(define-fungible-token stackaroos)
         (define-read-only (my-ft-get-balance (account principal))
            (ft-get-balance stackaroos account))
         (define-read-only (get-total-supply)
            (ft-get-supply stackaroos))
         (define-public (my-token-transfer (to principal) (amount uint))
            (ft-transfer? stackaroos amount tx-sender to))
         (define-public (faucet)
           (let ((original-sender tx-sender))
             (as-contract (ft-transfer? stackaroos u1 tx-sender original-sender))))
         (define-public (mint-after (block-to-release uint))
           (if (>= block-height block-to-release)
               (faucet)
               (err \"must be in the future\")))
         (define-public (burn (amount uint) (p principal))
           (ft-burn? stackaroos amount p))
         (begin (ft-mint? stackaroos u10000 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
                (ft-mint? stackaroos u200 'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G)
                (ft-mint? stackaroos u4 .tokens))";

const ASSET_NAMES: &str =
        "(define-constant burn-address 'SP000000000000000000002Q6VF78)
         (define-private (price-function (name int))
           (if (< name 100000) u1000 u100))

         (define-non-fungible-token names int)
         (define-map preorder-map
           { name-hash: (buff 20) }
           { buyer: principal, paid: uint })

         (define-public (preorder
                        (name-hash (buff 20))
                        (name-price uint))
           (let ((xfer-result (contract-call? .tokens my-token-transfer
                                burn-address name-price)))
            (if (is-ok xfer-result)
               (if
                 (map-insert preorder-map
                   (tuple (name-hash name-hash))
                   (tuple (paid name-price)
                          (buyer tx-sender)))
                 (ok 0) (err u2))
               (if (is-eq xfer-result (err u1)) ;; not enough balance
                   (err u1) (err u3)))))

         (define-public (force-mint (name int))
           (nft-mint? names name tx-sender))
         (define-public (force-burn (name int) (p principal))
           (nft-burn? names name p))
         (define-public (try-bad-transfers)
           (begin
             (contract-call? .tokens my-token-transfer burn-address u50000)
             (contract-call? .tokens my-token-transfer burn-address u1000)
             (contract-call? .tokens my-token-transfer burn-address u1)
             (err u0)))
         (define-public (try-bad-transfers-but-ok)
           (begin
             (contract-call? .tokens my-token-transfer burn-address u50000)
             (contract-call? .tokens my-token-transfer burn-address u1000)
             (contract-call? .tokens my-token-transfer burn-address u1)
             (ok 0)))
         (define-public (transfer (name int) (recipient principal))
           (let ((transfer-name-result (nft-transfer? names name tx-sender recipient))
                 (token-to-contract-result (contract-call? .tokens my-token-transfer .names u1))
                 (contract-to-burn-result (as-contract (contract-call? .tokens my-token-transfer burn-address u1))))
             (begin (unwrap! transfer-name-result transfer-name-result)
                    (unwrap! token-to-contract-result token-to-contract-result)
                    (unwrap! contract-to-burn-result contract-to-burn-result)
                    (ok 0))))
         (define-public (register
                        (recipient-principal principal)
                        (name int)
                        (salt int))
           (let ((preorder-entry
                   ;; preorder entry must exist!
                   (unwrap! (map-get? preorder-map
                                  (tuple (name-hash (hash160 (xor name salt))))) (err u5)))
                 (name-entry
                   (nft-get-owner? names name)))
             (if (and
                  (is-none name-entry)
                  ;; preorder must have paid enough
                  (<= (price-function name)
                      (get paid preorder-entry))
                  ;; preorder must have been the current principal
                  (is-eq tx-sender
                       (get buyer preorder-entry)))
                  (if (and
                    (is-ok (nft-mint? names name recipient-principal))
                    (map-delete preorder-map
                      (tuple (name-hash (hash160 (xor name salt))))))
                    (ok 0)
                    (err u3))
                  (err u4))))";

fn execute_transaction(
    env: &mut OwnedEnvironment,
    issuer: PrincipalData,
    contract_identifier: &QualifiedContractIdentifier,
    tx: &str,
    args: &[SymbolicExpression],
) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>), Error> {
    env.execute_transaction(issuer, None, contract_identifier.clone(), tx, args)
}

#[apply(test_epochs)]
fn test_native_stx_ops(epoch: StacksEpochId, mut env_factory: TopLevelMemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);
    let contract = r#"(define-public (burn-stx (amount uint) (p principal)) (stx-burn? amount p))
                    (define-public (xfer-stx (amount uint) (p principal) (t principal)) (stx-transfer? amount p t))
                    (define-read-only (balance-stx (p principal)) (stx-get-balance p))
                    (define-public (to-contract (amount uint) (p principal))
                      (let ((contract-principal (as-contract tx-sender)))
                        (stx-transfer? amount p contract-principal)))
                    (define-public (from-contract (amount uint) (t principal))
                      (let ((contract-principal 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR.tokens))
                        (as-contract (stx-transfer? amount contract-principal t))))"#;

    let contract_second = r#"(define-public (send-to-other (amount uint))
                             (as-contract
                              (stx-transfer? amount tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR.tokens)))"#;

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");
    let p3 = execute("'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY");

    let p1_std_principal_data = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };

    let p1_principal = match p1 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let p3_principal = match p3 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let token_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data.clone(), "tokens".into());
    let second_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data, "second".into());

    owned_env
        .initialize_contract(
            token_contract_id.clone(),
            contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    owned_env
        .initialize_contract(
            second_contract_id.clone(),
            contract_second,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    owned_env.stx_faucet(&(p1_principal), u128::MAX - 1500);
    owned_env.stx_faucet(&p2_principal, 1000);

    // test 1: send 0

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(0), p1.clone(), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 3));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "burn-stx",
        &symbols_from_values(vec![Value::UInt(0), p1.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 3));
    assert_eq!(asset_map.to_table().len(), 0);

    // test 2: from = to

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(50), p2.clone(), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 2));
    assert_eq!(asset_map.to_table().len(), 0);

    // test 3: sender is not tx-sender

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(50), p1.clone(), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 4));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn-stx",
        &symbols_from_values(vec![Value::UInt(50), p1.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 4));
    assert_eq!(asset_map.to_table().len(), 0);

    // test 4: amount > balance

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(1001), p2.clone(), p3.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn-stx",
        &symbols_from_values(vec![Value::UInt(1001), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));
    assert_eq!(asset_map.to_table().len(), 0);

    // test 5: overflow
    //  NOTE: this tested behavior is no longer reachable: the total liquid ustx supply
    //    will overflow before such an overflowing transfer is allowed.
    // assert_eq!(
    //     execute_transaction(
    //         &mut owned_env,
    //         p2.clone(),
    //         &token_contract_id,
    //         "xfer-stx",
    //         &symbols_from_values(vec![Value::UInt(2), p2.clone(), p1.clone()])
    //     )
    //     .unwrap_err(),
    //     RuntimeErrorType::ArithmeticOverflow.into()
    // );

    // test 6: check balance

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "balance-stx",
        &symbols_from_values(vec![p2.clone()]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(1000));

    // test 7: check balance is 0 for nonexistent principal

    let sp_data =
        PrincipalData::parse_standard_principal("SPZG6BAY4JVR9RNAB1HY92B7Q208ZYY4HZEA9PX5")
            .unwrap();
    let nonexistent_principal = Value::Principal(PrincipalData::Standard(sp_data));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "balance-stx",
        &symbols_from_values(vec![nonexistent_principal]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(0));

    // now, let's actually do a couple transfers/burns and check the asset maps.

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn-stx",
        &symbols_from_values(vec![Value::UInt(10), p2.clone()]),
    )
    .unwrap();

    assert!(is_committed(&result));
    let table = asset_map.to_table();
    assert_eq!(
        table[&p2_principal][&AssetIdentifier::STX_burned()],
        AssetMapEntry::Burn(10)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(500), p2.clone(), p3.clone()]),
    )
    .unwrap();

    assert!(is_committed(&result));
    let table = asset_map.to_table();
    assert_eq!(
        table[&p2_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(500)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p3_principal.clone(),
        &token_contract_id,
        "xfer-stx",
        &symbols_from_values(vec![Value::UInt(1), p3.clone(), p1]),
    )
    .unwrap();

    assert!(is_committed(&result));
    let table = asset_map.to_table();
    assert_eq!(
        table[&p3_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(1)
    );

    // let's try a user -> contract transfer

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "to-contract",
        &symbols_from_values(vec![Value::UInt(10), p2]),
    )
    .unwrap();

    assert!(is_committed(&result));
    let table = asset_map.to_table();
    assert_eq!(
        table[&p2_principal.clone()][&AssetIdentifier::STX()],
        AssetMapEntry::STX(10)
    );

    // now check contract balance with stx-get-balance

    let cp_data = PrincipalData::parse_qualified_contract_principal(
        "SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR.tokens",
    )
    .unwrap();
    let contract_principal = Value::Principal(cp_data);

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "balance-stx",
        &symbols_from_values(vec![contract_principal]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(10));

    // now let's do a contract -> user transfer

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p3_principal.clone(),
        &token_contract_id,
        "from-contract",
        &symbols_from_values(vec![Value::UInt(10), p3]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let table = asset_map.to_table();

    let contract_principal = PrincipalData::from(token_contract_id.clone());

    assert_eq!(
        table[&contract_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(10)
    );

    // now let's do a contract -> contract transfer

    // first, let's fund some STX in contract 2
    let second_contract_principal = second_contract_id.clone().into();
    owned_env.stx_faucet(&second_contract_principal, 500);

    // now, to transfer
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &second_contract_id,
        "send-to-other",
        &symbols_from_values(vec![Value::UInt(500)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let table = asset_map.to_table();

    assert_eq!(table.len(), 1);
    assert_eq!(
        table[&second_contract_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(500)
    );

    // now, let's send some back

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p3_principal,
        &token_contract_id,
        "from-contract",
        &symbols_from_values(vec![Value::UInt(100), second_contract_id.clone().into()]),
    )
    .unwrap();

    assert!(is_committed(&result));
    let table = asset_map.to_table();

    assert_eq!(table.len(), 1);
    assert_eq!(
        table[&contract_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(100)
    );

    // and, one more time for good measure
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &second_contract_id,
        "send-to-other",
        &symbols_from_values(vec![Value::UInt(100)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let table = asset_map.to_table();

    assert_eq!(table.len(), 1);
    assert_eq!(
        table[&second_contract_principal][&AssetIdentifier::STX()],
        AssetMapEntry::STX(100)
    );
}

#[apply(test_epochs)]
fn test_simple_token_system(
    epoch: StacksEpochId,
    mut env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);
    let tokens_contract = FIRST_CLASS_TOKENS;

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_std_principal_data = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };

    let p1_principal = match p1 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let token_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data, "tokens".into());

    let token_identifier = AssetIdentifier {
        contract_identifier: token_contract_id.clone(),
        asset_name: "stackaroos".into(),
    };

    let contract_principal = PrincipalData::Contract(token_contract_id.clone());

    owned_env
        .initialize_contract(
            token_contract_id.clone(),
            tokens_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "my-token-transfer",
        &symbols_from_values(vec![p1.clone(), Value::UInt(210)]),
    )
    .unwrap();
    assert!(!is_committed(&result));

    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-token-transfer",
        &symbols_from_values(vec![p2.clone(), Value::UInt(9000)]),
    )
    .unwrap();
    assert!(is_committed(&result));

    let asset_map = asset_map.to_table();
    assert_eq!(
        asset_map[&p1_principal][&token_identifier],
        AssetMapEntry::Token(9000)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-token-transfer",
        &symbols_from_values(vec![p2.clone(), Value::UInt(1001)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-token-transfer",
        &symbols_from_values(vec![p1.clone(), Value::UInt(1000)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 2));
    assert_eq!(asset_map.to_table().len(), 0);

    let err = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-token-transfer",
        &symbols_from_values(vec![p1.clone(), Value::Int(-1)]),
    )
    .unwrap_err();

    assert!(matches!(
        err,
        Error::Unchecked(CheckErrors::TypeValueError(_, _))
    ));

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-ft-get-balance",
        &symbols_from_values(vec![p1.clone()]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(1000));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-ft-get-balance",
        &symbols_from_values(vec![p2.clone()]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(9200));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "faucet",
        &[],
    )
    .unwrap();

    assert!(is_committed(&result));

    let asset_map = asset_map.to_table();
    assert_eq!(
        asset_map[&contract_principal][&token_identifier],
        AssetMapEntry::Token(1)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "faucet",
        &[],
    )
    .unwrap();

    let asset_map = asset_map.to_table();
    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&contract_principal][&token_identifier],
        AssetMapEntry::Token(1)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "faucet",
        &[],
    )
    .unwrap();

    let asset_map = asset_map.to_table();
    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&contract_principal][&token_identifier],
        AssetMapEntry::Token(1)
    );

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-ft-get-balance",
        &symbols_from_values(vec![p1]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(1003));

    // Get the total supply - Total minted so far = 10204
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "get-total-supply",
        &symbols_from_values(vec![]),
    )
    .unwrap();
    assert_eq!(result, Value::UInt(10204));

    // Burn 100 tokens from p2's balance (out of 9200)
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn",
        &symbols_from_values(vec![Value::UInt(100), p2.clone()]),
    )
    .unwrap();

    let asset_map = asset_map.to_table();
    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&p2_principal][&token_identifier],
        AssetMapEntry::Token(100)
    );

    // Get p2's balance we should get 9200 - 100 = 9100
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "my-ft-get-balance",
        &symbols_from_values(vec![p2.clone()]),
    )
    .unwrap();

    assert_eq!(result, Value::UInt(9100));

    // Get the new total supply
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "get-total-supply",
        &symbols_from_values(vec![]),
    )
    .unwrap();
    assert_eq!(result, Value::UInt(10104));

    // Burn 9101 tokens from p2's balance (out of 9100) - Should fail with error code 1
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn",
        &symbols_from_values(vec![Value::UInt(9101), p2.clone()]),
    )
    .unwrap();

    assert!(!is_committed(&result));
    assert!(is_err_code(&result, 1));

    // Try to burn 0 tokens from p2's balance - Should fail with error code 1
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &token_contract_id,
        "burn",
        &symbols_from_values(vec![Value::UInt(0), p2.clone()]),
    )
    .unwrap();

    assert!(!is_committed(&result));
    assert!(is_err_code(&result, 1));

    // Try to burn 1 tokens from p2's balance (out of 9100) - Should pass even though
    // sender != tx sender
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "burn",
        &symbols_from_values(vec![Value::UInt(1), p2]),
    )
    .unwrap();

    let asset_map = asset_map.to_table();
    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&p2_principal][&token_identifier],
        AssetMapEntry::Token(1)
    );

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal,
        &token_contract_id,
        "mint-after",
        &symbols_from_values(vec![Value::UInt(25)]),
    )
    .unwrap();

    assert!(!is_committed(&result));
    assert_eq!(asset_map.to_table().len(), 0);
}

#[apply(test_epochs)]
fn test_total_supply(epoch: StacksEpochId, mut env_factory: TopLevelMemoryEnvironmentGenerator) {
    let mut owned_env = env_factory.get_env(epoch);
    let bad_0 = "(define-fungible-token stackaroos (- 5))";
    let bad_1 = "(define-fungible-token stackaroos true)";

    let contract = "(define-fungible-token stackaroos u5)
         (define-read-only (get-balance (account principal))
            (ft-get-balance stackaroos account))
         (define-public (transfer (to principal) (amount uint))
            (ft-transfer? stackaroos amount tx-sender to))
         (define-public (faucet)
            (ft-mint? stackaroos u2 tx-sender))
         (define-public (gated-faucet (x bool))
            (begin (faucet)
                   (if x (ok 1) (err 0))))";

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");

    let p1_std_principal_data = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };

    let p1_principal = match p1 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let token_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data, "tokens".into());
    let err = owned_env
        .initialize_contract(
            token_contract_id.clone(),
            bad_0,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
    assert!(matches!(
        err,
        Error::Unchecked(CheckErrors::TypeValueError(_, _))
    ));

    let err = owned_env
        .initialize_contract(
            token_contract_id.clone(),
            bad_1,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
    assert!(matches!(
        err,
        Error::Unchecked(CheckErrors::TypeValueError(_, _))
    ));

    owned_env
        .initialize_contract(
            token_contract_id.clone(),
            contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "gated-faucet",
        &symbols_from_values(vec![Value::Bool(true)]),
    )
    .unwrap();
    assert!(is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "gated-faucet",
        &symbols_from_values(vec![Value::Bool(false)]),
    )
    .unwrap();
    assert!(!is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &token_contract_id,
        "gated-faucet",
        &symbols_from_values(vec![Value::Bool(true)]),
    )
    .unwrap();
    assert!(is_committed(&result));

    let err = execute_transaction(
        &mut owned_env,
        p1_principal,
        &token_contract_id,
        "gated-faucet",
        &symbols_from_values(vec![Value::Bool(false)]),
    )
    .unwrap_err();
    println!("{}", err);
    assert!(match err {
        Error::Runtime(RuntimeErrorType::SupplyOverflow(x, y), _) => (x, y) == (6, 5),
        _ => false,
    });
}

#[apply(test_epochs)]
fn test_overlapping_nfts(
    epoch: StacksEpochId,
    mut env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);
    let tokens_contract = FIRST_CLASS_TOKENS;
    let names_contract = ASSET_NAMES;

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");

    let p1_std_principal_data = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };

    let tokens_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data.clone(), "tokens".into());
    let names_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data.clone(), "names".into());
    let names_2_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data, "names-2".into());

    owned_env
        .initialize_contract(
            tokens_contract_id,
            tokens_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    owned_env
        .initialize_contract(
            names_contract_id,
            names_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
    owned_env
        .initialize_contract(
            names_2_contract_id,
            names_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();
}

#[apply(test_clarity_versions)]
fn test_simple_naming_system(
    version: ClarityVersion,
    epoch: StacksEpochId,
    mut env_factory: TopLevelMemoryEnvironmentGenerator,
) {
    let mut owned_env = env_factory.get_env(epoch);
    let tokens_contract = FIRST_CLASS_TOKENS;

    let names_contract = ASSET_NAMES;

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_std_principal_data = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };

    let p1_principal = match p1 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let mut placeholder_context =
        ContractContext::new(QualifiedContractIdentifier::transient(), version);

    let tokens_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data.clone(), "tokens".into());

    let names_contract_id =
        QualifiedContractIdentifier::new(p1_std_principal_data.clone(), "names".into());

    let names_identifier = AssetIdentifier {
        contract_identifier: names_contract_id,
        asset_name: "names".into(),
    };
    let tokens_identifier = AssetIdentifier {
        contract_identifier: tokens_contract_id.clone(),
        asset_name: "stackaroos".into(),
    };

    let name_hash_expensive_0 = execute("(hash160 1)");
    let name_hash_expensive_1 = execute("(hash160 2)");
    let name_hash_cheap_0 = execute("(hash160 100001)");

    owned_env
        .initialize_contract(
            tokens_contract_id,
            tokens_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    let names_contract_id = QualifiedContractIdentifier::new(p1_std_principal_data, "names".into());
    owned_env
        .initialize_contract(
            names_contract_id.clone(),
            names_contract,
            None,
            ASTRules::PrecheckSize,
        )
        .unwrap();

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "preorder",
        &symbols_from_values(vec![name_hash_expensive_0.clone(), Value::UInt(1000)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "preorder",
        &symbols_from_values(vec![name_hash_expensive_0.clone(), Value::UInt(1000)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "preorder",
        &symbols_from_values(vec![name_hash_expensive_0, Value::UInt(1000)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 2));

    // shouldn't be able to register a name you didn't preorder!

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "register",
        &symbols_from_values(vec![p2.clone(), Value::Int(1), Value::Int(0)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 4));

    // should work!

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "register",
        &symbols_from_values(vec![p2.clone(), Value::Int(1), Value::Int(0)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    {
        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);
        assert_eq!(
            env.eval_read_only(&names_contract_id.clone(), "(nft-get-owner? names 1)")
                .unwrap(),
            Value::some(p2.clone()).unwrap()
        );
    }

    // let's try some token-transfers

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "try-bad-transfers",
        &[],
    )
    .unwrap();
    assert!(is_err_code(&result, 0));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "try-bad-transfers-but-ok",
        &[],
    )
    .unwrap();

    assert!(is_committed(&result));

    let asset_map = asset_map.to_table();
    assert_eq!(
        asset_map[&p1_principal][&tokens_identifier],
        AssetMapEntry::Token(1001)
    );

    // let's mint some names

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "force-mint",
        &symbols_from_values(vec![Value::Int(1)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "force-mint",
        &symbols_from_values(vec![Value::Int(5)]),
    )
    .unwrap();

    assert!(is_committed(&result));
    assert_eq!(asset_map.to_table().len(), 0);

    // let's transfer name

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "transfer",
        &symbols_from_values(vec![Value::Int(7), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 3));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "transfer",
        &symbols_from_values(vec![Value::Int(1), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 1));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "transfer",
        &symbols_from_values(vec![Value::Int(1), p2.clone()]),
    )
    .unwrap();

    assert!(is_err_code(&result, 2));
    assert_eq!(asset_map.to_table().len(), 0);

    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "transfer",
        &symbols_from_values(vec![Value::Int(5), p2.clone()]),
    )
    .unwrap();

    let asset_map = asset_map.to_table();

    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&p1_principal][&names_identifier],
        AssetMapEntry::Asset(vec![Value::Int(5)])
    );
    assert_eq!(
        asset_map[&p1_principal][&tokens_identifier],
        AssetMapEntry::Token(1)
    );

    // try to underpay!

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "preorder",
        &symbols_from_values(vec![name_hash_expensive_1, Value::UInt(100)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "register",
        &symbols_from_values(vec![p2.clone(), Value::Int(2), Value::Int(0)]),
    )
    .unwrap();

    assert!(is_err_code(&result, 4));

    // register a cheap name!

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "preorder",
        &symbols_from_values(vec![name_hash_cheap_0, Value::UInt(100)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "register",
        &symbols_from_values(vec![p2.clone(), Value::Int(100001), Value::Int(0)]),
    )
    .unwrap();

    assert!(is_committed(&result));

    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "register",
        &symbols_from_values(vec![p2.clone(), Value::Int(100001), Value::Int(0)]),
    )
    .unwrap();

    // preorder must exist!
    assert!(is_err_code(&result, 5));

    // p1 burning 5 should fail (not owner anymore).
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "force-burn",
        &symbols_from_values(vec![Value::Int(5), p1.clone()]),
    )
    .unwrap();

    assert!(!is_committed(&result));
    assert!(is_err_code(&result, 1));

    // p1 minting 8 should succeed
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal.clone(),
        &names_contract_id,
        "force-mint",
        &symbols_from_values(vec![Value::Int(8)]),
    )
    .unwrap();

    assert!(is_committed(&result));
    assert_eq!(asset_map.to_table().len(), 0);

    // p2 burning 8 (which belongs to p1) should succeed even though sender != tx_sender.
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "force-burn",
        &symbols_from_values(vec![Value::Int(8), p1.clone()]),
    )
    .unwrap();

    let asset_map = asset_map.to_table();

    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&p1_principal][&names_identifier],
        AssetMapEntry::Asset(vec![Value::Int(8)])
    );

    // p2 burning 5 should succeed.
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal.clone(),
        &names_contract_id,
        "force-burn",
        &symbols_from_values(vec![Value::Int(5), p2.clone()]),
    )
    .unwrap();

    let asset_map = asset_map.to_table();

    assert!(is_committed(&result));
    assert_eq!(
        asset_map[&p2_principal][&names_identifier],
        AssetMapEntry::Asset(vec![Value::Int(5)])
    );

    // p2 re-burning 5 should succeed.
    let (result, _asset_map, _events) = execute_transaction(
        &mut owned_env,
        p2_principal,
        &names_contract_id,
        "force-burn",
        &symbols_from_values(vec![Value::Int(5), p2]),
    )
    .unwrap();
    assert!(!is_committed(&result));
    assert!(is_err_code(&result, 3));

    // p1 re-minting 5 should succeed
    let (result, asset_map, _events) = execute_transaction(
        &mut owned_env,
        p1_principal,
        &names_contract_id,
        "force-mint",
        &symbols_from_values(vec![Value::Int(5)]),
    )
    .unwrap();

    assert!(is_committed(&result));
    assert_eq!(asset_map.to_table().len(), 0);

    {
        let mut env = owned_env.get_exec_environment(None, None, &mut placeholder_context);
        assert_eq!(
            env.eval_read_only(&names_contract_id.clone(), "(nft-get-owner? names 5)")
                .unwrap(),
            Value::some(p1).unwrap()
        );
    }
}
