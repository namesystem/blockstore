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

use std::io::Write;

use serde::Deserialize;
use stacks_common::util::hash::{hex_bytes, to_hex};

use crate::vm::analysis::ContractAnalysis;
use crate::vm::contracts::Contract;
use crate::vm::database::ClarityDatabase;
use crate::vm::errors::{
    Error, IncomparableError, InterpreterError, InterpreterResult, RuntimeErrorType,
};
use crate::vm::types::{
    OptionalData, PrincipalData, TupleTypeSignature, TypeSignature, Value, NONE,
};

pub trait ClaritySerializable {
    fn serialize(&self) -> String;
}

pub trait ClarityDeserializable<T> {
    fn deserialize(json: &str) -> Result<T>;
}

impl ClaritySerializable for String {
    fn serialize(&self) -> String {
        self.into()
    }
}

impl ClarityDeserializable<String> for String {
    fn deserialize(serialized: &str) -> Result<String> {
        Ok(serialized.into())
    }
}

macro_rules! clarity_serializable {
    ($Name:ident) => {
        impl ClaritySerializable for $Name {
            fn serialize(&self) -> String {
                serde_json::to_string(self).expect("Failed to serialize vm.Value")
            }
        }
        impl ClarityDeserializable<$Name> for $Name {
            #[cfg(not(feature = "wasm"))]
            fn deserialize(json: &str) -> Result<Self> {
                let mut deserializer = serde_json::Deserializer::from_str(&json);
                // serde's default 128 depth limit can be exhausted
                //  by a 64-stack-depth AST, so disable the recursion limit
                deserializer.disable_recursion_limit();
                // use stacker to prevent the deserializer from overflowing.
                //  this will instead spill to the heap
                let deserializer = serde_stacker::Deserializer::new(&mut deserializer);
                Deserialize::deserialize(deserializer).map_err(|_| {
                    InterpreterError::Expect("Failed to deserialize vm.Value".into()).into()
                })
            }
            #[cfg(feature = "wasm")]
            fn deserialize(json: &str) -> Result<Self> {
                serde_json::from_str(json).map_err(|_| {
                    InterpreterError::Expect("Failed to deserialize vm.Value".into()).into()
                })
            }
        }
    };
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FungibleTokenMetadata {
    pub total_supply: Option<u128>,
}

clarity_serializable!(FungibleTokenMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonFungibleTokenMetadata {
    pub key_type: TypeSignature,
}

clarity_serializable!(NonFungibleTokenMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataMapMetadata {
    pub key_type: TypeSignature,
    pub value_type: TypeSignature,
}

clarity_serializable!(DataMapMetadata);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DataVariableMetadata {
    pub value_type: TypeSignature,
}

clarity_serializable!(DataVariableMetadata);

#[derive(Serialize, Deserialize)]
pub struct ContractMetadata {
    pub contract: Contract,
}

clarity_serializable!(ContractMetadata);

#[derive(Serialize, Deserialize)]
pub struct SimmedBlock {
    pub block_height: u64,
    pub block_time: u64,
    pub block_header_hash: [u8; 32],
    pub burn_chain_header_hash: [u8; 32],
    pub vrf_seed: [u8; 32],
}

clarity_serializable!(SimmedBlock);

clarity_serializable!(PrincipalData);
clarity_serializable!(i128);
clarity_serializable!(u128);
clarity_serializable!(u64);
clarity_serializable!(Contract);
clarity_serializable!(ContractAnalysis);

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum STXBalance {
    Unlocked {
        amount: u128,
    },
    LockedPoxOne {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
    LockedPoxTwo {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
    LockedPoxThree {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
    LockedPoxFour {
        amount_unlocked: u128,
        amount_locked: u128,
        unlock_height: u64,
    },
}

/// Lifetime-limited handle to an uncommitted balance structure.
/// All balance mutations (debits, credits, locks, unlocks) must go through this structure.
pub struct STXBalanceSnapshot<'db, 'conn> {
    principal: PrincipalData,
    balance: STXBalance,
    burn_block_height: u64,
    db_ref: &'conn mut ClarityDatabase<'db>,
}

type Result<T> = std::result::Result<T, Error>;

impl ClaritySerializable for STXBalance {
    #[allow(clippy::expect_used)]
    fn serialize(&self) -> String {
        let mut buffer = Vec::new();
        match self {
            STXBalance::Unlocked { amount } => {
                buffer
                    .write_all(&amount.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&0u128.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&0u64.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxOne {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&[STXBalance::pox_2_version])
                    .expect("STXBalance serialization: failed to write PoX version byte");
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxThree {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&[STXBalance::pox_3_version])
                    .expect("STXBalance serialization: failed to write PoX version byte");
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
            STXBalance::LockedPoxFour {
                amount_unlocked,
                amount_locked,
                unlock_height,
            } => {
                buffer
                    .write_all(&[STXBalance::pox_4_version])
                    .expect("STXBalance serialization: failed to write PoX version byte");
                buffer
                    .write_all(&amount_unlocked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_unlocked.");
                buffer
                    .write_all(&amount_locked.to_be_bytes())
                    .expect("STXBalance serialization: failed writing amount_locked.");
                buffer
                    .write_all(&unlock_height.to_be_bytes())
                    .expect("STXBalance serialization: failed writing unlock_height.");
            }
        }
        to_hex(buffer.as_slice())
    }
}

impl ClarityDeserializable<STXBalance> for STXBalance {
    fn deserialize(input: &str) -> Result<Self> {
        let bytes = hex_bytes(input).map_err(|_| {
            InterpreterError::Expect("STXBalance deserialization: failed decoding bytes.".into())
        })?;
        let result = if bytes.len() == STXBalance::unlocked_and_v1_size {
            let amount_unlocked = u128::from_be_bytes(bytes[0..16].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading amount_unlocked.".into(),
                )
            })?);
            let amount_locked = u128::from_be_bytes(bytes[16..32].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading amount_locked.".into(),
                )
            })?);
            let unlock_height = u64::from_be_bytes(bytes[32..40].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading unlock_height.".into(),
                )
            })?);

            if amount_locked == 0 {
                STXBalance::Unlocked {
                    amount: amount_unlocked,
                }
            } else {
                STXBalance::LockedPoxOne {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            }
        } else if bytes.len() == STXBalance::v2_to_v4_size {
            let version = &bytes[0];
            if version != &STXBalance::pox_2_version
                && version != &STXBalance::pox_3_version
                && version != &STXBalance::pox_4_version
            {
                return Err(InterpreterError::Expect(format!(
                    "Bad version byte in STX Balance serialization = {version}"
                ))
                .into());
            }
            let amount_unlocked = u128::from_be_bytes(bytes[1..17].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading amount_unlocked.".into(),
                )
            })?);
            let amount_locked = u128::from_be_bytes(bytes[17..33].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading amount_locked.".into(),
                )
            })?);
            let unlock_height = u64::from_be_bytes(bytes[33..41].try_into().map_err(|_| {
                InterpreterError::Expect(
                    "STXBalance deserialization: failed reading unlock_height.".into(),
                )
            })?);

            if amount_locked == 0 {
                STXBalance::Unlocked {
                    amount: amount_unlocked,
                }
            } else if version == &STXBalance::pox_2_version {
                STXBalance::LockedPoxTwo {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            } else if version == &STXBalance::pox_3_version {
                STXBalance::LockedPoxThree {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            } else if version == &STXBalance::pox_4_version {
                STXBalance::LockedPoxFour {
                    amount_unlocked,
                    amount_locked,
                    unlock_height,
                }
            } else {
                return Err(InterpreterError::Expect(
                    "Version is checked for pox_3 or pox_2 version compliance above".into(),
                )
                .into());
            }
        } else {
            return Err(InterpreterError::Expect(format!(
                "Bad STX Balance serialization size = {}",
                bytes.len()
            ))
            .into());
        };
        Ok(result)
    }
}

impl<'db, 'conn> STXBalanceSnapshot<'db, 'conn> {
    pub fn new(
        principal: &PrincipalData,
        balance: STXBalance,
        burn_height: u64,
        db_ref: &'conn mut ClarityDatabase<'db>,
    ) -> STXBalanceSnapshot<'db, 'conn> {
        STXBalanceSnapshot {
            principal: principal.clone(),
            balance,
            burn_block_height: burn_height,
            db_ref,
        }
    }

    pub fn balance(&self) -> &STXBalance {
        &self.balance
    }

    pub fn save(self) -> Result<()> {
        let key = ClarityDatabase::make_key_for_account_balance(&self.principal);
        self.db_ref.put_data(&key, &self.balance)
    }

    pub fn transfer_to(mut self, recipient: &PrincipalData, amount: u128) -> Result<()> {
        if !self.can_transfer(amount)? {
            return Err(InterpreterError::InsufficientBalance.into());
        }

        let recipient_key = ClarityDatabase::make_key_for_account_balance(recipient);
        let mut recipient_balance = self
            .db_ref
            .get_data(&recipient_key)?
            .unwrap_or(STXBalance::zero());

        recipient_balance
            .checked_add_unlocked_amount(amount)
            .ok_or(Error::Runtime(RuntimeErrorType::ArithmeticOverflow, None))?;

        self.debit(amount)?;
        self.db_ref.put_data(&recipient_key, &recipient_balance)?;
        self.save()?;
        Ok(())
    }

    pub fn get_available_balance(&mut self) -> Result<u128> {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        let v2_unlock_height = self.db_ref.get_v2_unlock_height()?;
        let v3_unlock_height = self.db_ref.get_v3_unlock_height()?;
        self.balance.get_available_balance_at_burn_block(
            self.burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        )
    }

    pub fn canonical_balance_repr(&mut self) -> Result<STXBalance> {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        let v2_unlock_height = self.db_ref.get_v2_unlock_height()?;
        let v3_unlock_height = self.db_ref.get_v3_unlock_height()?;
        Ok(self
            .balance
            .canonical_repr_at_block(
                self.burn_block_height,
                v1_unlock_height,
                v2_unlock_height,
                v3_unlock_height,
            )?
            .0)
    }

    pub fn has_locked_tokens(&mut self) -> Result<bool> {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        let v2_unlock_height = self.db_ref.get_v2_unlock_height()?;
        let v3_unlock_height = self.db_ref.get_v3_unlock_height()?;
        Ok(self.balance.has_locked_tokens_at_burn_block(
            self.burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        ))
    }

    pub fn has_unlockable_tokens(&mut self) -> Result<bool> {
        let v1_unlock_height = self.db_ref.get_v1_unlock_height();
        let v2_unlock_height = self.db_ref.get_v2_unlock_height()?;
        let v3_unlock_height = self.db_ref.get_v3_unlock_height()?;
        Ok(self.balance.has_unlockable_tokens_at_burn_block(
            self.burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        ))
    }

    pub fn can_transfer(&mut self, amount: u128) -> Result<bool> {
        Ok(self.get_available_balance()? >= amount)
    }

    pub fn debit(&mut self, amount: u128) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-debit");
        }

        self.balance.debit_unlocked_amount(amount)
    }

    pub fn credit(&mut self, amount: u128) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-credit");
        }

        self.balance
            .checked_add_unlocked_amount(amount)
            .ok_or_else(|| InterpreterError::Expect("STX balance overflow".into()))?;
        Ok(())
    }

    pub fn set_balance(&mut self, balance: STXBalance) {
        self.balance = balance;
    }

    pub fn lock_tokens_v1(&mut self, amount_to_lock: u128, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        assert!(amount_to_lock > 0, "BUG: cannot lock 0 tokens");

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: cannot set a lock with expired unlock burn height".into(),
            )
            .into());
        }

        if self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account already has locked tokens".into(),
            )
            .into());
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()?
            .checked_sub(amount_to_lock)
            .ok_or_else(|| InterpreterError::Expect("STX underflow".into()))?;

        self.balance = STXBalance::LockedPoxOne {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    ////////////// Pox-2 /////////////////

    /// Return true iff `self` represents a snapshot that has a lock
    ///  created by PoX v2.
    pub fn is_v2_locked(&mut self) -> Result<bool> {
        match self.canonical_balance_repr()? {
            STXBalance::LockedPoxTwo { .. } => Ok(true),
            _ => Ok(false),
        }
    }

    /// Increase the account's current lock to `new_total_locked`.
    /// Panics if `self` was not locked by V2 PoX.
    pub fn increase_lock_v2(&mut self, new_total_locked: u128) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account does not have locked tokens".into(),
            )
            .into());
        }

        if !self.is_v2_locked()? {
            // caller needs to have checked this
            return Err(
                InterpreterError::Expect("FATAL: account must be locked by pox-2".into()).into(),
            );
        }

        if self.balance.amount_locked() > new_total_locked {
            return Err(InterpreterError::Expect(
                "FATAL: account must lock more after `increase_lock_v2`".into(),
            )
            .into());
        }

        let total_amount = self
            .balance
            .amount_unlocked()
            .checked_add(self.balance.amount_locked())
            .ok_or_else(|| InterpreterError::Expect("STX balance overflowed u128".into()))?;
        let amount_unlocked = total_amount.checked_sub(new_total_locked).ok_or_else(|| {
            InterpreterError::Expect("STX underflow: more is locked than total balance".into())
        })?;

        self.balance = STXBalance::LockedPoxTwo {
            amount_unlocked,
            amount_locked: new_total_locked,
            unlock_height: self.balance.unlock_height(),
        };

        Ok(())
    }

    /// Extend this account's current lock to `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxTwo" balance,
    ///  because this method is only invoked as a result of PoX2 interactions
    pub fn extend_lock_v2(&mut self, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account does not have locked tokens".into(),
            )
            .into());
        }

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: cannot set a lock with expired unlock burn height".into(),
            )
            .into());
        }

        self.balance = STXBalance::LockedPoxTwo {
            amount_unlocked: self.balance.amount_unlocked(),
            amount_locked: self.balance.amount_locked(),
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    /// Lock `amount_to_lock` tokens on this account until `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxTwo" balance,
    ///  because this method is only invoked as a result of PoX2 interactions
    pub fn lock_tokens_v2(&mut self, amount_to_lock: u128, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        if amount_to_lock == 0 {
            return Err(InterpreterError::Expect("BUG: cannot lock 0 tokens".into()).into());
        }

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: cannot set a lock with expired unlock burn height".into(),
            )
            .into());
        }

        if self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account already has locked tokens".into(),
            )
            .into());
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()?
            .checked_sub(amount_to_lock)
            .ok_or_else(|| InterpreterError::Expect("STX underflow".into()))?;

        self.balance = STXBalance::LockedPoxTwo {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    //////////////// Pox-3 //////////////////

    /// Lock `amount_to_lock` tokens on this account until `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxThree" balance,
    ///  because this method is only invoked as a result of PoX3 interactions
    pub fn lock_tokens_v3(&mut self, amount_to_lock: u128, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        assert!(amount_to_lock > 0, "BUG: cannot lock 0 tokens");

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: cannot set a lock with expired unlock burn height".into(),
            )
            .into());
        }

        if self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account already has locked tokens".into(),
            )
            .into());
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()?
            .checked_sub(amount_to_lock)
            .ok_or_else(|| {
                InterpreterError::Expect(
                    "FATAL: account locks more STX than balance possessed".into(),
                )
            })?;

        self.balance = STXBalance::LockedPoxThree {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };

        Ok(())
    }

    /// Extend this account's current lock to `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxThree" balance,
    ///  because this method is only invoked as a result of PoX3 interactions
    pub fn extend_lock_v3(&mut self, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account does not have locked tokens".into(),
            )
            .into());
        }

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: cannot set a lock with expired unlock burn height".into(),
            )
            .into());
        }

        self.balance = STXBalance::LockedPoxThree {
            amount_unlocked: self.balance.amount_unlocked(),
            amount_locked: self.balance.amount_locked(),
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    /// Increase the account's current lock to `new_total_locked`.
    /// Panics if `self` was not locked by V3 PoX.
    pub fn increase_lock_v3(&mut self, new_total_locked: u128) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            return Err(InterpreterError::Expect(
                "FATAL: account does not have locked tokens".into(),
            )
            .into());
        }

        if !self.is_v3_locked()? {
            // caller needs to have checked this
            return Err(
                InterpreterError::Expect("FATAL: account must be locked by pox-3".into()).into(),
            );
        }

        assert!(
            self.balance.amount_locked() <= new_total_locked,
            "FATAL: account must lock more after `increase_lock_v3`"
        );

        let total_amount = self
            .balance
            .amount_unlocked()
            .checked_add(self.balance.amount_locked())
            .ok_or_else(|| InterpreterError::Expect("STX balance overflowed u128".into()))?;
        let amount_unlocked = total_amount.checked_sub(new_total_locked).ok_or_else(|| {
            InterpreterError::Expect("STX underflow: more is locked than total balance".into())
        })?;

        self.balance = STXBalance::LockedPoxThree {
            amount_unlocked,
            amount_locked: new_total_locked,
            unlock_height: self.balance.unlock_height(),
        };
        Ok(())
    }

    /// Return true iff `self` represents a snapshot that has a lock
    ///  created by PoX v3.
    pub fn is_v3_locked(&mut self) -> Result<bool> {
        match self.canonical_balance_repr()? {
            STXBalance::LockedPoxThree { .. } => Ok(true),
            _ => Ok(false),
        }
    }

    //////////////// Pox-4 //////////////////

    /// Lock `amount_to_lock` tokens on this account until `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxFour" balance,
    ///  because this method is only invoked as a result of PoX4 interactions
    pub fn lock_tokens_v4(&mut self, amount_to_lock: u128, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        // caller needs to have checked this
        assert!(amount_to_lock > 0, "BUG: cannot lock 0 tokens");

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            panic!("FATAL: cannot set a lock with expired unlock burn height");
        }

        if self.has_locked_tokens()? {
            // caller needs to have checked this
            panic!("FATAL: account already has locked tokens");
        }

        // from `unlock_available_tokens_if_any` call above, `self.balance` should
        //  be canonicalized already

        let new_amount_unlocked = self
            .balance
            .get_total_balance()?
            .checked_sub(amount_to_lock)
            .expect("FATAL: account locks more STX than balance possessed");

        self.balance = STXBalance::LockedPoxFour {
            amount_unlocked: new_amount_unlocked,
            amount_locked: amount_to_lock,
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    /// Extend this account's current lock to `unlock_burn_height`.
    /// After calling, this method will set the balance to a "LockedPoxFour" balance,
    ///  because this method is only invoked as a result of PoX3 interactions
    pub fn extend_lock_v4(&mut self, unlock_burn_height: u64) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            panic!("FATAL: account does not have locked tokens");
        }

        if unlock_burn_height <= self.burn_block_height {
            // caller needs to have checked this
            panic!("FATAL: cannot set a lock with expired unlock burn height");
        }

        self.balance = STXBalance::LockedPoxFour {
            amount_unlocked: self.balance.amount_unlocked(),
            amount_locked: self.balance.amount_locked(),
            unlock_height: unlock_burn_height,
        };
        Ok(())
    }

    /// Increase the account's current lock to `new_total_locked`.
    /// Panics if `self` was not locked by V3 PoX.
    pub fn increase_lock_v4(&mut self, new_total_locked: u128) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after extend-token-lock");
        }

        if !self.has_locked_tokens()? {
            // caller needs to have checked this
            panic!("FATAL: account does not have locked tokens");
        }

        if !self.is_v4_locked()? {
            // caller needs to have checked this
            panic!("FATAL: account must be locked by pox-3");
        }

        assert!(
            self.balance.amount_locked() <= new_total_locked,
            "FATAL: account must lock more after `increase_lock_v3`"
        );

        let total_amount = self
            .balance
            .amount_unlocked()
            .checked_add(self.balance.amount_locked())
            .expect("STX balance overflowed u128");
        let amount_unlocked = total_amount
            .checked_sub(new_total_locked)
            .expect("STX underflow: more is locked than total balance");

        self.balance = STXBalance::LockedPoxFour {
            amount_unlocked,
            amount_locked: new_total_locked,
            unlock_height: self.balance.unlock_height(),
        };
        Ok(())
    }

    /// Return true iff `self` represents a snapshot that has a lock
    ///  created by PoX v3.
    pub fn is_v4_locked(&mut self) -> Result<bool> {
        match self.canonical_balance_repr()? {
            STXBalance::LockedPoxFour { .. } => Ok(true),
            _ => Ok(false),
        }
    }

    /////////////// GENERAL //////////////////////

    /// If this snapshot is locked, then alter the lock height to be
    /// the next burn block (i.e., `self.burn_block_height + 1`)
    pub fn accelerate_unlock(&mut self) -> Result<()> {
        let unlocked = self.unlock_available_tokens_if_any()?;
        if unlocked > 0 {
            debug!("Consolidated after account-token-lock");
        }

        let new_unlock_height = self.burn_block_height + 1;
        self.balance = match self.balance {
            STXBalance::Unlocked { amount } => STXBalance::Unlocked { amount },
            STXBalance::LockedPoxOne { .. } => {
                return Err(InterpreterError::Expect(
                    "Attempted to accelerate the unlock of a lockup created by PoX-1".into(),
                )
                .into())
            }
            STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                ..
            } => STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                unlock_height: new_unlock_height,
            },
            STXBalance::LockedPoxThree {
                amount_unlocked,
                amount_locked,
                ..
            } => STXBalance::LockedPoxThree {
                amount_unlocked,
                amount_locked,
                unlock_height: new_unlock_height,
            },
            STXBalance::LockedPoxFour {
                amount_unlocked,
                amount_locked,
                ..
            } => STXBalance::LockedPoxFour {
                amount_unlocked,
                amount_locked,
                unlock_height: new_unlock_height,
            },
        };
        Ok(())
    }

    /// Unlock any tokens that are unlockable at the current
    ///  burn block height, and return the amount newly unlocked
    fn unlock_available_tokens_if_any(&mut self) -> Result<u128> {
        let (new_balance, unlocked) = self.balance.canonical_repr_at_block(
            self.burn_block_height,
            self.db_ref.get_v1_unlock_height(),
            self.db_ref.get_v2_unlock_height()?,
            self.db_ref.get_v3_unlock_height()?,
        )?;
        self.balance = new_balance;
        Ok(unlocked)
    }
}

impl Default for STXBalance {
    fn default() -> Self {
        STXBalance::zero()
    }
}

// NOTE: do _not_ add mutation methods to this struct. Put them in STXBalanceSnapshot!
impl STXBalance {
    pub const unlocked_and_v1_size: usize = 40;
    pub const v2_to_v4_size: usize = 41;
    pub const pox_2_version: u8 = 0;
    pub const pox_3_version: u8 = 1;
    pub const pox_4_version: u8 = 2;

    pub fn zero() -> STXBalance {
        STXBalance::Unlocked { amount: 0 }
    }

    pub fn initial(amount: u128) -> STXBalance {
        STXBalance::Unlocked { amount }
    }

    /// This method returns the datastructure's lazy view of the unlock_height:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn unlock_height(&self) -> u64 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { unlock_height, .. }
            | STXBalance::LockedPoxTwo { unlock_height, .. }
            | STXBalance::LockedPoxThree { unlock_height, .. }
            | STXBalance::LockedPoxFour { unlock_height, .. } => *unlock_height,
        }
    }

    /// This method returns the datastructure's lazy view of the unlock_height
    ///  *while* factoring in the PoX 2 early unlock for PoX 1 and PoX 3 early unlock for PoX 2.
    /// This value is still lazy: this unlock height may be less than the current
    ///  burn block height, if so it will be updated in a canonicalized view.
    pub fn effective_unlock_height(
        &self,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> u64 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { unlock_height, .. } => {
                if *unlock_height >= u64::from(v1_unlock_height) {
                    u64::from(v1_unlock_height)
                } else {
                    *unlock_height
                }
            }
            STXBalance::LockedPoxTwo { unlock_height, .. } => {
                if *unlock_height >= u64::from(v2_unlock_height) {
                    u64::from(v2_unlock_height)
                } else {
                    *unlock_height
                }
            }
            STXBalance::LockedPoxThree { unlock_height, .. } => {
                if *unlock_height >= u64::from(v3_unlock_height) {
                    u64::from(v3_unlock_height)
                } else {
                    *unlock_height
                }
            }
            STXBalance::LockedPoxFour { unlock_height, .. } => *unlock_height,
        }
    }

    /// This method returns the datastructure's lazy view of the amount locked:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn amount_locked(&self) -> u128 {
        match self {
            STXBalance::Unlocked { .. } => 0,
            STXBalance::LockedPoxOne { amount_locked, .. }
            | STXBalance::LockedPoxTwo { amount_locked, .. }
            | STXBalance::LockedPoxThree { amount_locked, .. }
            | STXBalance::LockedPoxFour { amount_locked, .. } => *amount_locked,
        }
    }

    /// This method returns the datastructure's lazy view of the amount unlocked:
    ///  this *may* be updated by a canonicalized view of the account
    pub fn amount_unlocked(&self) -> u128 {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxThree {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxFour {
                amount_unlocked, ..
            } => *amount_unlocked,
        }
    }

    fn debit_unlocked_amount(&mut self, delta: u128) -> Result<()> {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxThree {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxFour {
                amount_unlocked, ..
            } => {
                *amount_unlocked = amount_unlocked
                    .checked_sub(delta)
                    .ok_or_else(|| InterpreterError::Expect("STX underflow".into()))?;
                Ok(())
            }
        }
    }

    fn checked_add_unlocked_amount(&mut self, delta: u128) -> Option<u128> {
        match self {
            STXBalance::Unlocked {
                amount: amount_unlocked,
            }
            | STXBalance::LockedPoxOne {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxTwo {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxThree {
                amount_unlocked, ..
            }
            | STXBalance::LockedPoxFour {
                amount_unlocked, ..
            } => {
                if let Some(new_amount) = amount_unlocked.checked_add(delta) {
                    *amount_unlocked = new_amount;
                    Some(new_amount)
                } else {
                    None
                }
            }
        }
    }

    /// Returns a canonicalized STXBalance at a given burn_block_height
    /// (i.e., if burn_block_height >= unlock_height, then return struct where
    ///   amount_unlocked = 0, unlock_height = 0), and the amount of tokens which
    ///   are "unlocked" by the canonicalization
    pub fn canonical_repr_at_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> Result<(STXBalance, u128)> {
        if self.has_unlockable_tokens_at_burn_block(
            burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        ) {
            Ok((
                STXBalance::Unlocked {
                    amount: self.get_total_balance()?,
                },
                self.amount_locked(),
            ))
        } else {
            Ok((self.clone(), 0))
        }
    }

    pub fn get_available_balance_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> Result<u128> {
        if self.has_unlockable_tokens_at_burn_block(
            burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        ) {
            self.get_total_balance()
        } else {
            let out = match self {
                STXBalance::Unlocked { amount } => *amount,
                STXBalance::LockedPoxOne {
                    amount_unlocked, ..
                } => *amount_unlocked,
                STXBalance::LockedPoxTwo {
                    amount_unlocked, ..
                } => *amount_unlocked,
                STXBalance::LockedPoxThree {
                    amount_unlocked, ..
                } => *amount_unlocked,
                STXBalance::LockedPoxFour {
                    amount_unlocked, ..
                } => *amount_unlocked,
            };
            Ok(out)
        }
    }

    pub fn get_locked_balance_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> (u128, u64) {
        if self.has_unlockable_tokens_at_burn_block(
            burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        ) {
            (0, 0)
        } else {
            match self {
                STXBalance::Unlocked { .. } => (0, 0),
                STXBalance::LockedPoxOne {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
                STXBalance::LockedPoxTwo {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
                STXBalance::LockedPoxThree {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
                STXBalance::LockedPoxFour {
                    amount_locked,
                    unlock_height,
                    ..
                } => (*amount_locked, *unlock_height),
            }
        }
    }

    pub fn get_total_balance(&self) -> Result<u128> {
        let (unlocked, locked) = match self {
            STXBalance::Unlocked { amount } => (*amount, 0),
            STXBalance::LockedPoxOne {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
            STXBalance::LockedPoxTwo {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
            STXBalance::LockedPoxThree {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
            STXBalance::LockedPoxFour {
                amount_unlocked,
                amount_locked,
                ..
            } => (*amount_unlocked, *amount_locked),
        };
        unlocked
            .checked_add(locked)
            .ok_or_else(|| InterpreterError::Expect("STX overflow".into()).into())
    }

    pub fn was_locked_by_v1(&self) -> bool {
        matches!(self, STXBalance::LockedPoxOne { .. })
    }

    pub fn was_locked_by_v2(&self) -> bool {
        matches!(self, STXBalance::LockedPoxTwo { .. })
    }

    pub fn was_locked_by_v3(&self) -> bool {
        matches!(self, STXBalance::LockedPoxThree { .. })
    }

    pub fn has_locked_tokens_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> bool {
        match self {
            STXBalance::Unlocked { .. } => false,
            STXBalance::LockedPoxOne {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return false
                if *unlock_height <= burn_block_height {
                    return false;
                }
                // if unlockable due to Stacks 2.1 early unlock
                if u64::from(v1_unlock_height) <= burn_block_height {
                    return false;
                }
                true
            }
            STXBalance::LockedPoxTwo {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                if *unlock_height <= burn_block_height {
                    return false;
                }
                // if unlockable due to Stacks 2.2 early unlock
                if u64::from(v2_unlock_height) <= burn_block_height {
                    return false;
                }
                true
            }
            STXBalance::LockedPoxThree {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                if *unlock_height <= burn_block_height {
                    return false;
                }
                // if unlockable due to Stacks 2.5 early unlock
                if u64::from(v3_unlock_height) <= burn_block_height {
                    return false;
                }
                true
            }
            STXBalance::LockedPoxFour {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                if *unlock_height <= burn_block_height {
                    return false;
                }
                true
            }
        }
    }

    pub fn has_unlockable_tokens_at_burn_block(
        &self,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> bool {
        match self {
            STXBalance::Unlocked { .. } => false,
            STXBalance::LockedPoxOne {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return true
                if *unlock_height <= burn_block_height {
                    return true;
                }
                // if unlockable due to Stacks 2.1 early unlock
                if u64::from(v1_unlock_height) <= burn_block_height {
                    return true;
                }
                false
            }
            STXBalance::LockedPoxTwo {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return true
                if *unlock_height <= burn_block_height {
                    return true;
                }
                // if unlockable due to Stacks 2.2 early unlock
                if u64::from(v2_unlock_height) <= burn_block_height {
                    return true;
                }
                false
            }
            STXBalance::LockedPoxThree {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return true
                if *unlock_height <= burn_block_height {
                    return true;
                }
                // if unlockable due to Stacks 2.5 early unlock
                if u64::from(v3_unlock_height) <= burn_block_height {
                    return true;
                }
                false
            }
            STXBalance::LockedPoxFour {
                amount_locked,
                unlock_height,
                ..
            } => {
                if *amount_locked == 0 {
                    return false;
                }
                // if normally unlockable, return true
                if *unlock_height <= burn_block_height {
                    return true;
                }
                false
            }
        }
    }

    pub fn can_transfer_at_burn_block(
        &self,
        amount: u128,
        burn_block_height: u64,
        v1_unlock_height: u32,
        v2_unlock_height: u32,
        v3_unlock_height: u32,
    ) -> Result<bool> {
        Ok(self.get_available_balance_at_burn_block(
            burn_block_height,
            v1_unlock_height,
            v2_unlock_height,
            v3_unlock_height,
        )? >= amount)
    }
}
