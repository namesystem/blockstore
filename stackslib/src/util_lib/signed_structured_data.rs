// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2021 Stacks Open Internet Foundation
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

use clarity::vm::types::TupleData;
use clarity::vm::Value;
use stacks_common::codec::StacksMessageCodec;
use stacks_common::types::chainstate::StacksPrivateKey;
use stacks_common::types::PrivateKey;
use stacks_common::util::hash::{to_hex, Sha256Sum};
use stacks_common::util::secp256k1::{MessageSignature, Secp256k1PrivateKey};

use crate::chainstate::stacks::address::PoxAddress;

/// Message prefix for signed structured data. "SIP018" in ascii
pub const STRUCTURED_DATA_PREFIX: [u8; 6] = [0x53, 0x49, 0x50, 0x30, 0x31, 0x38];

pub fn structured_data_hash(value: Value) -> Sha256Sum {
    let mut bytes = vec![];
    value.serialize_write(&mut bytes).unwrap();
    Sha256Sum::from_data(&bytes.as_slice())
}

/// Generate a message hash for signing structured Clarity data.
/// Reference [SIP018](https://github.com/stacksgov/sips/blob/main/sips/sip-018/sip-018-signed-structured-data.md) for more information.
pub fn structured_data_message_hash(structured_data: Value, domain: Value) -> Sha256Sum {
    let message = [
        STRUCTURED_DATA_PREFIX.as_ref(),
        structured_data_hash(domain).as_bytes(),
        structured_data_hash(structured_data).as_bytes(),
    ]
    .concat();

    Sha256Sum::from_data(&message)
}

/// Sign structured Clarity data with a given private key.
/// Reference [SIP018](https://github.com/stacksgov/sips/blob/main/sips/sip-018/sip-018-signed-structured-data.md) for more information.
pub fn sign_structured_data(
    structured_data: Value,
    domain: Value,
    private_key: &Secp256k1PrivateKey,
) -> Result<MessageSignature, &str> {
    let msg_hash = structured_data_message_hash(structured_data, domain);
    private_key.sign(msg_hash.as_bytes())
}

// Helper function to generate domain for structured data hash
pub fn make_structured_data_domain(name: &str, version: &str, chain_id: u32) -> Value {
    Value::Tuple(
        TupleData::from_data(vec![
            (
                "name".into(),
                Value::string_ascii_from_bytes(name.into()).unwrap(),
            ),
            (
                "version".into(),
                Value::string_ascii_from_bytes(version.into()).unwrap(),
            ),
            ("chain-id".into(), Value::UInt(chain_id.into())),
        ])
        .unwrap(),
    )
}

pub mod pox4 {
    use super::{
        make_structured_data_domain, structured_data_message_hash, MessageSignature, PoxAddress,
        PrivateKey, Sha256Sum, StacksPrivateKey, TupleData, Value,
    };
    define_named_enum!(Pox4SignatureTopic {
        StackStx("stack-stx"),
        AggregationCommit("agg-commit"),
        AggregationIncrease("agg-increase"),
        StackExtend("stack-extend"),
        StackIncrease("stack-increase"),
    });

    pub fn make_pox_4_signed_data_domain(chain_id: u32) -> Value {
        make_structured_data_domain("pox-4-signer", "1.0.0", chain_id)
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn make_pox_4_signer_key_message_hash(
        pox_addr: &PoxAddress,
        reward_cycle: u128,
        topic: &Pox4SignatureTopic,
        chain_id: u32,
        period: u128,
        max_amount: u128,
        auth_id: u128,
    ) -> Sha256Sum {
        let domain_tuple = make_pox_4_signed_data_domain(chain_id);
        let data_tuple = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "pox-addr".into(),
                    pox_addr
                        .clone()
                        .as_clarity_tuple()
                        .expect("Error creating signature hash - invalid PoX Address")
                        .into(),
                ),
                ("reward-cycle".into(), Value::UInt(reward_cycle)),
                ("period".into(), Value::UInt(period)),
                (
                    "topic".into(),
                    Value::string_ascii_from_bytes(topic.get_name_str().into()).unwrap(),
                ),
                ("auth-id".into(), Value::UInt(auth_id)),
                ("max-amount".into(), Value::UInt(max_amount)),
            ])
            .expect("Error creating signature hash"),
        );
        structured_data_message_hash(data_tuple, domain_tuple)
    }

    impl Into<Pox4SignatureTopic> for &'static str {
        #[cfg_attr(test, mutants::skip)]
        fn into(self) -> Pox4SignatureTopic {
            match self {
                "stack-stx" => Pox4SignatureTopic::StackStx,
                "agg-commit" => Pox4SignatureTopic::AggregationCommit,
                "stack-extend" => Pox4SignatureTopic::StackExtend,
                "stack-increase" => Pox4SignatureTopic::StackIncrease,
                _ => panic!("Invalid pox-4 signature topic"),
            }
        }
    }

    #[cfg_attr(test, mutants::skip)]
    pub fn make_pox_4_signer_key_signature(
        pox_addr: &PoxAddress,
        signer_key: &StacksPrivateKey,
        reward_cycle: u128,
        topic: &Pox4SignatureTopic,
        chain_id: u32,
        period: u128,
        max_amount: u128,
        auth_id: u128,
    ) -> Result<MessageSignature, &'static str> {
        let msg_hash = make_pox_4_signer_key_message_hash(
            pox_addr,
            reward_cycle,
            topic,
            chain_id,
            period,
            max_amount,
            auth_id,
        );
        signer_key.sign(msg_hash.as_bytes())
    }

    #[cfg(test)]
    mod tests {
        use clarity::vm::ast::ASTRules;
        use clarity::vm::clarity::{ClarityConnection, TransactionConnection};
        use clarity::vm::costs::LimitedCostTracker;
        use clarity::vm::types::{PrincipalData, StandardPrincipalData};
        use clarity::vm::ClarityVersion;
        use stacks_common::address::AddressHashMode;
        use stacks_common::consts::CHAIN_ID_TESTNET;
        use stacks_common::types::chainstate::StacksAddress;
        use stacks_common::util::hash::to_hex;
        use stacks_common::util::secp256k1::Secp256k1PublicKey;

        use super::*;
        use crate::chainstate::stacks::address::pox_addr_b58_serialize;
        use crate::chainstate::stacks::boot::contract_tests::ClarityTestSim;
        use crate::chainstate::stacks::boot::{POX_4_CODE, POX_4_NAME};
        use crate::util_lib::boot::boot_code_id;

        fn call_get_signer_message_hash(
            sim: &mut ClarityTestSim,
            pox_addr: &PoxAddress,
            reward_cycle: u128,
            topic: &Pox4SignatureTopic,
            lock_period: u128,
            sender: &PrincipalData,
            max_amount: u128,
            auth_id: u128,
        ) -> Vec<u8> {
            let pox_contract_id = boot_code_id(POX_4_NAME, false);
            sim.execute_next_block_as_conn(|conn| {
                let result = conn.with_readonly_clarity_env(
                    false,
                    CHAIN_ID_TESTNET,
                    ClarityVersion::Clarity2,
                    sender.clone(),
                    None,
                    LimitedCostTracker::new_free(),
                    |env| {
                        let program = format!(
                            "(get-signer-key-message-hash {} u{} \"{}\" u{} u{} u{})",
                            Value::Tuple(pox_addr.clone().as_clarity_tuple().unwrap()), //p
                            reward_cycle,
                            topic.get_name_str(),
                            lock_period,
                            max_amount,
                            auth_id,
                        );
                        env.eval_read_only(&pox_contract_id, &program)
                    },
                );
                result
                    .expect("FATAL: failed to execute contract call")
                    .expect_buff(32)
                    .expect("FATAL: expected buff result")
            })
        }

        #[test]
        fn test_make_pox_4_message_hash() {
            let mut sim = ClarityTestSim::new();
            sim.epoch_bounds = vec![0, 1, 2];

            // Test setup
            sim.execute_next_block(|_env| {});
            sim.execute_next_block(|_env| {});
            sim.execute_next_block(|_env| {});

            let body = &*POX_4_CODE;
            let pox_contract_id = boot_code_id(POX_4_NAME, false);

            sim.execute_next_block_as_conn(|conn| {
                conn.as_transaction(|clarity_db| {
                    let clarity_version = ClarityVersion::Clarity2;
                    let (mut ast, analysis) = clarity_db
                        .analyze_smart_contract(
                            &pox_contract_id,
                            clarity_version,
                            &body,
                            ASTRules::PrecheckSize,
                        )
                        .unwrap();
                    clarity_db
                        .initialize_smart_contract(
                            &pox_contract_id,
                            clarity_version,
                            &mut ast,
                            &analysis,
                            &body,
                            None,
                            |_, _| false,
                        )
                        .unwrap();
                    clarity_db
                        .save_analysis(&pox_contract_id, &analysis)
                        .expect("FATAL: failed to store contract analysis");
                });
            });

            let pubkey = Secp256k1PublicKey::new();
            let stacks_addr = StacksAddress::p2pkh(false, &pubkey);
            let pubkey = Secp256k1PublicKey::new();
            let principal = PrincipalData::from(stacks_addr.clone());
            let pox_addr = PoxAddress::standard_burn_address(false);
            let reward_cycle: u128 = 1;
            let topic = Pox4SignatureTopic::StackStx;
            let lock_period = 12;
            let auth_id = 111;
            let max_amount = u128::MAX;

            let expected_hash_vec = make_pox_4_signer_key_message_hash(
                &pox_addr,
                reward_cycle,
                &Pox4SignatureTopic::StackStx,
                CHAIN_ID_TESTNET,
                lock_period,
                max_amount,
                auth_id,
            );
            let expected_hash = expected_hash_vec.as_bytes();

            // Test 1: valid result

            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                reward_cycle,
                &topic,
                lock_period,
                &principal,
                max_amount,
                auth_id,
            );
            assert_eq!(expected_hash.clone(), result.as_slice());

            // Test 2: invalid pox address
            let other_pox_address = PoxAddress::from_legacy(
                AddressHashMode::SerializeP2PKH,
                StacksAddress::p2pkh(false, &Secp256k1PublicKey::new()).bytes,
            );
            let result = call_get_signer_message_hash(
                &mut sim,
                &other_pox_address,
                reward_cycle,
                &topic,
                lock_period,
                &principal,
                max_amount,
                auth_id,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());

            // Test 3: invalid reward cycle
            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                0,
                &topic,
                lock_period,
                &principal,
                max_amount,
                auth_id,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());

            // Test 4: invalid topic
            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                reward_cycle,
                &Pox4SignatureTopic::AggregationCommit,
                lock_period,
                &principal,
                max_amount,
                auth_id,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());

            // Test 5: invalid lock period
            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                reward_cycle,
                &topic,
                0,
                &principal,
                max_amount,
                auth_id,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());

            // Test 5: invalid max amount
            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                reward_cycle,
                &topic,
                lock_period,
                &principal,
                1010101,
                auth_id,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());

            // Test 6: invalid auth id
            let result = call_get_signer_message_hash(
                &mut sim,
                &pox_addr,
                reward_cycle,
                &topic,
                lock_period,
                &principal,
                max_amount,
                10101,
            );
            assert_ne!(expected_hash.clone(), result.as_slice());
        }

        #[test]
        /// Fixture message hash to test against in other libraries
        fn test_sig_hash_fixture() {
            let fixture = "ec5b88aa81a96a6983c26cdba537a13d253425348ffc0ba6b07130869b025a2d";
            let pox_addr = PoxAddress::standard_burn_address(false);
            let pubkey_hex = "0206952cd8813a64f7b97144c984015490a8f9c5778e8f928fbc8aa6cbf02f48e6";
            let pubkey = Secp256k1PublicKey::from_hex(pubkey_hex).unwrap();
            let reward_cycle: u128 = 1;
            let lock_period = 12;
            let auth_id = 111;
            let max_amount = u128::MAX;

            let message_hash = make_pox_4_signer_key_message_hash(
                &pox_addr,
                reward_cycle,
                &Pox4SignatureTopic::StackStx,
                CHAIN_ID_TESTNET,
                lock_period,
                max_amount,
                auth_id,
            );

            assert_eq!(to_hex(message_hash.as_bytes()), fixture);
        }
    }
}

#[cfg(test)]
mod test {
    use clarity::vm::types::{TupleData, Value};
    use stacks_common::consts::CHAIN_ID_MAINNET;
    use stacks_common::util::hash::to_hex;

    use super::*;

    /// [SIP18 test vectors](https://github.com/stacksgov/sips/blob/main/sips/sip-018/sip-018-signed-structured-data.md)
    #[test]
    fn test_sip18_ref_structured_data_hash() {
        let value = Value::string_ascii_from_bytes("Hello World".into()).unwrap();
        let msg_hash = structured_data_hash(value);
        assert_eq!(
            to_hex(msg_hash.as_bytes()),
            "5297eef9765c466d945ad1cb2c81b30b9fed6c165575dc9226e9edf78b8cd9e8"
        )
    }

    /// [SIP18 test vectors](https://github.com/stacksgov/sips/blob/main/sips/sip-018/sip-018-signed-structured-data.md)
    #[test]
    fn test_sip18_ref_message_hashing() {
        let domain = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "name".into(),
                    Value::string_ascii_from_bytes("Test App".into()).unwrap(),
                ),
                (
                    "version".into(),
                    Value::string_ascii_from_bytes("1.0.0".into()).unwrap(),
                ),
                ("chain-id".into(), Value::UInt(CHAIN_ID_MAINNET.into())),
            ])
            .unwrap(),
        );
        let data = Value::string_ascii_from_bytes("Hello World".into()).unwrap();

        let msg_hash = structured_data_message_hash(data, domain);

        assert_eq!(
            to_hex(msg_hash.as_bytes()),
            "1bfdab6d4158313ce34073fbb8d6b0fc32c154d439def12247a0f44bb2225259"
        );
    }

    /// [SIP18 test vectors](https://github.com/stacksgov/sips/blob/main/sips/sip-018/sip-018-signed-structured-data.md)
    #[test]
    fn test_sip18_ref_signing() {
        let key = Secp256k1PrivateKey::from_hex(
            "753b7cc01a1a2e86221266a154af739463fce51219d97e4f856cd7200c3bd2a601",
        )
        .unwrap();
        let domain = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "name".into(),
                    Value::string_ascii_from_bytes("Test App".into()).unwrap(),
                ),
                (
                    "version".into(),
                    Value::string_ascii_from_bytes("1.0.0".into()).unwrap(),
                ),
                ("chain-id".into(), Value::UInt(CHAIN_ID_MAINNET.into())),
            ])
            .unwrap(),
        );
        let data = Value::string_ascii_from_bytes("Hello World".into()).unwrap();
        let signature =
            sign_structured_data(data, domain, &key).expect("Failed to sign structured data");

        let signature_rsv = signature.to_rsv();

        assert_eq!(to_hex(signature_rsv.as_slice()), "8b94e45701d857c9f1d1d70e8b2ca076045dae4920fb0160be0642a68cd78de072ab527b5c5277a593baeb2a8b657c216b99f7abb5d14af35b4bf12ba6460ba401");
    }

    #[test]
    fn test_prefix_bytes() {
        let hex = to_hex(STRUCTURED_DATA_PREFIX.as_ref());
        assert_eq!(hex, "534950303138");
    }
}
