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

use std::collections::{HashMap, HashSet};
use std::io::prelude::*;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::{fmt, fs, io};

use clar2wasm::compile_contract;
use clarity::vm::analysis::run_analysis;
use clarity::vm::analysis::types::ContractAnalysis;
use clarity::vm::ast::errors::ParseErrors;
use clarity::vm::ast::ASTRules;
use clarity::vm::clarity::TransactionConnection;
use clarity::vm::contexts::{AssetMap, AssetMapEntry, Environment};
use clarity::vm::contracts::Contract;
use clarity::vm::costs::cost_functions::ClarityCostFunction;
use clarity::vm::costs::{cost_functions, runtime_cost, CostTracker, ExecutionCost};
use clarity::vm::database::{ClarityBackingStore, ClarityDatabase};
use clarity::vm::diagnostic::DiagnosableError;
use clarity::vm::errors::{Error as InterpreterError, WasmError};
use clarity::vm::representations::{ClarityName, ContractName};
use clarity::vm::types::serialization::SerializationError as ClaritySerializationError;
use clarity::vm::types::{
    AssetIdentifier, BuffData, PrincipalData, QualifiedContractIdentifier, SequenceData,
    StacksAddressExtensions as ClarityStacksAddressExt, StandardPrincipalData, TupleData,
    TypeSignature, Value,
};
use stacks_common::util::hash::to_hex;

use crate::chainstate::burn::db::sortdb::*;
use crate::chainstate::nakamoto::NakamotoChainState;
use crate::chainstate::stacks::db::*;
use crate::chainstate::stacks::{Error, StacksMicroblockHeader, *};
use crate::clarity_vm::clarity::{
    ClarityBlockConnection, ClarityConnection, ClarityInstance, ClarityTransactionConnection,
    Error as clarity_error,
};
use crate::net::Error as net_error;
use crate::util_lib::db::{query_count, query_rows, DBConn, Error as db_error};
use crate::util_lib::strings::{StacksString, VecDisplay};

/// This is a safe-to-hash Clarity value
#[derive(PartialEq, Eq)]
struct HashableClarityValue(Value);

impl TryFrom<Value> for HashableClarityValue {
    type Error = InterpreterError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        // check that serialization _will_ be successful when hashed
        let _bytes = value.serialize_to_vec().map_err(|_| {
            InterpreterError::Interpreter(clarity::vm::errors::InterpreterError::Expect(
                "Failed to serialize asset in NFT during post-condition checks".into(),
            ))
        })?;
        Ok(Self(value))
    }
}

impl std::hash::Hash for HashableClarityValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        #[allow(clippy::unwrap_used)]
        // this unwrap is safe _as long as_ TryFrom<Value> was used as a constructor
        let bytes = self.0.serialize_to_vec().unwrap();
        bytes.hash(state);
    }
}

impl StacksTransactionReceipt {
    pub fn from_stx_transfer(
        tx: StacksTransaction,
        events: Vec<StacksTransactionEvent>,
        result: Value,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            events,
            result,
            stx_burned: 0,
            post_condition_aborted: false,
            contract_analysis: None,
            transaction: tx.into(),
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_contract_call(
        tx: StacksTransaction,
        events: Vec<StacksTransactionEvent>,
        result: Value,
        burned: u128,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            post_condition_aborted: false,
            events,
            result,
            stx_burned: burned,
            contract_analysis: None,
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_condition_aborted_contract_call(
        tx: StacksTransaction,
        events: Vec<StacksTransactionEvent>,
        result: Value,
        burned: u128,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            post_condition_aborted: true,
            events,
            result,
            stx_burned: burned,
            contract_analysis: None,
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_smart_contract(
        tx: StacksTransaction,
        events: Vec<StacksTransactionEvent>,
        burned: u128,
        analysis: ContractAnalysis,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            events,
            post_condition_aborted: false,
            result: Value::okay_true(),
            stx_burned: burned,
            contract_analysis: Some(analysis),
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_condition_aborted_smart_contract(
        tx: StacksTransaction,
        events: Vec<StacksTransactionEvent>,
        burned: u128,
        analysis: ContractAnalysis,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            events,
            post_condition_aborted: true,
            result: Value::okay_true(),
            stx_burned: burned,
            contract_analysis: Some(analysis),
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_coinbase(tx: StacksTransaction) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            events: vec![],
            post_condition_aborted: false,
            result: Value::okay_true(),
            stx_burned: 0,
            contract_analysis: None,
            execution_cost: ExecutionCost::ZERO,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_analysis_failure(
        tx: StacksTransaction,
        analysis_cost: ExecutionCost,
        error: clarity::vm::clarity::Error,
    ) -> StacksTransactionReceipt {
        let error_string = match error {
            clarity_error::Analysis(ref check_error) => {
                if let Some(span) = check_error.diagnostic.spans.first() {
                    format!(
                        ":{}:{}: {}",
                        span.start_line, span.start_column, check_error.diagnostic.message
                    )
                } else {
                    format!("{}", check_error.diagnostic.message)
                }
            }
            clarity_error::Parse(ref parse_error) => {
                if let Some(span) = parse_error.diagnostic.spans.first() {
                    format!(
                        ":{}:{}: {}",
                        span.start_line, span.start_column, parse_error.diagnostic.message
                    )
                } else {
                    format!("{}", parse_error.diagnostic.message)
                }
            }
            _ => error.to_string(),
        };
        StacksTransactionReceipt {
            transaction: tx.into(),
            events: vec![],
            post_condition_aborted: false,
            result: Value::err_none(),
            stx_burned: 0,
            contract_analysis: None,
            execution_cost: analysis_cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: Some(error_string),
        }
    }

    pub fn from_poison_microblock(
        tx: StacksTransaction,
        result: Value,
        cost: ExecutionCost,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            events: vec![],
            post_condition_aborted: false,
            result,
            stx_burned: 0,
            contract_analysis: None,
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn from_runtime_failure_smart_contract(
        tx: StacksTransaction,
        cost: ExecutionCost,
        contract_analysis: ContractAnalysis,
        error: CheckErrors,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            post_condition_aborted: false,
            result: Value::err_none(),
            events: vec![],
            stx_burned: 0,
            contract_analysis: Some(contract_analysis),
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: Some(format!("{}", &error)),
        }
    }

    pub fn from_runtime_failure_contract_call(
        tx: StacksTransaction,
        cost: ExecutionCost,
        error: CheckErrors,
    ) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            post_condition_aborted: false,
            result: Value::err_none(),
            events: vec![],
            stx_burned: 0,
            contract_analysis: None,
            execution_cost: cost,
            microblock_header: None,
            tx_index: 0,
            vm_error: Some(format!("{}", &error)),
        }
    }

    pub fn from_tenure_change(tx: StacksTransaction) -> StacksTransactionReceipt {
        StacksTransactionReceipt {
            transaction: tx.into(),
            events: vec![],
            post_condition_aborted: false,
            result: Value::okay_true(),
            stx_burned: 0,
            contract_analysis: None,
            execution_cost: ExecutionCost::ZERO,
            microblock_header: None,
            tx_index: 0,
            vm_error: None,
        }
    }

    pub fn is_coinbase_tx(&self) -> bool {
        if let TransactionOrigin::Stacks(ref transaction) = self.transaction {
            if let TransactionPayload::Coinbase(..) = transaction.payload {
                return true;
            }
        }
        false
    }
}

#[derive(Debug)]
pub struct TransactionNonceMismatch {
    pub expected: u64,
    pub actual: u64,
    pub txid: Txid,
    pub principal: PrincipalData,
    pub is_origin: bool,
    pub quiet: bool,
}

impl std::fmt::Display for TransactionNonceMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let acct_type = if self.is_origin { "origin" } else { "sponsor" };
        write!(
            f,
            "Bad nonce: {} account {} nonce of tx {} is {} (expected {})",
            acct_type,
            &self.principal,
            &self.txid.to_hex(),
            &self.actual,
            &self.expected
        )
    }
}

impl<T> From<(TransactionNonceMismatch, T)> for Error {
    fn from(e: (TransactionNonceMismatch, T)) -> Error {
        Error::InvalidStacksTransaction(e.0.to_string(), e.0.quiet)
    }
}

impl From<TransactionNonceMismatch> for MemPoolRejection {
    fn from(e: TransactionNonceMismatch) -> MemPoolRejection {
        MemPoolRejection::BadNonces(e)
    }
}

pub enum ClarityRuntimeTxError {
    Acceptable {
        error: clarity_error,
        err_type: &'static str,
    },
    AbortedByCallback(Option<Value>, AssetMap, Vec<StacksTransactionEvent>),
    CostError(ExecutionCost, ExecutionCost),
    AnalysisError(CheckErrors),
    Rejectable(clarity_error),
}

pub fn handle_clarity_runtime_error(error: clarity_error) -> ClarityRuntimeTxError {
    match error {
        // runtime errors are okay
        clarity_error::Interpreter(InterpreterError::Runtime(_, _)) => {
            ClarityRuntimeTxError::Acceptable {
                error,
                err_type: "runtime error",
            }
        }
        clarity_error::Interpreter(InterpreterError::ShortReturn(_)) => {
            ClarityRuntimeTxError::Acceptable {
                error,
                err_type: "short return/panic",
            }
        }
        clarity_error::Interpreter(InterpreterError::Unchecked(check_error)) => {
            if check_error.rejectable() {
                ClarityRuntimeTxError::Rejectable(clarity_error::Interpreter(
                    InterpreterError::Unchecked(check_error),
                ))
            } else {
                ClarityRuntimeTxError::AnalysisError(check_error)
            }
        }
        clarity_error::AbortedByCallback(val, assets, events) => {
            ClarityRuntimeTxError::AbortedByCallback(val, assets, events)
        }
        clarity_error::CostError(cost, budget) => ClarityRuntimeTxError::CostError(cost, budget),
        unhandled_error => ClarityRuntimeTxError::Rejectable(unhandled_error),
    }
}

impl StacksChainState {
    /// Get the payer account
    fn get_payer_account<T: ClarityConnection>(
        clarity_tx: &mut T,
        tx: &StacksTransaction,
    ) -> StacksAccount {
        // who's paying the fee?
        let payer_account = if let Some(sponsor_address) = tx.sponsor_address() {
            let payer_account = StacksChainState::get_account(clarity_tx, &sponsor_address.into());
            payer_account
        } else {
            let origin_account =
                StacksChainState::get_account(clarity_tx, &tx.origin_address().into());
            origin_account
        };

        payer_account
    }

    /// Check the account nonces for the supplied stacks transaction,
    ///   returning the origin and payer accounts if valid.
    pub fn check_transaction_nonces<T: ClarityConnection>(
        clarity_tx: &mut T,
        tx: &StacksTransaction,
        quiet: bool,
    ) -> Result<
        (StacksAccount, StacksAccount),
        (TransactionNonceMismatch, (StacksAccount, StacksAccount)),
    > {
        // who's sending it?
        let origin = tx.get_origin();
        let origin_account = StacksChainState::get_account(clarity_tx, &tx.origin_address().into());

        // who's paying the fee?
        let payer_account = if let Some(sponsor_address) = tx.sponsor_address() {
            let payer = tx.get_payer();
            let payer_account = StacksChainState::get_account(clarity_tx, &sponsor_address.into());

            if payer.nonce() != payer_account.nonce {
                let e = TransactionNonceMismatch {
                    expected: payer_account.nonce,
                    actual: payer.nonce(),
                    txid: tx.txid(),
                    principal: payer_account.principal.clone(),
                    is_origin: false,
                    quiet,
                };
                if !quiet {
                    warn!("{e}");
                }
                return Err((e, (origin_account, payer_account)));
            }

            payer_account
        } else {
            origin_account.clone()
        };

        // check nonces
        if origin.nonce() != origin_account.nonce {
            let e = TransactionNonceMismatch {
                expected: origin_account.nonce,
                actual: origin.nonce(),
                txid: tx.txid(),
                principal: origin_account.principal.clone(),
                is_origin: true,
                quiet,
            };
            if !quiet {
                warn!("{e}");
            }
            return Err((e, (origin_account, payer_account)));
        }

        Ok((origin_account, payer_account))
    }

    /// Pay the transaction fee (but don't credit it to the miner yet).
    /// Does not touch the account nonce.
    /// Consumes the account object, since it invalidates it.
    fn pay_transaction_fee(
        clarity_tx: &mut ClarityTransactionConnection,
        fee: u64,
        payer_account: StacksAccount,
    ) -> Result<u64, Error> {
        let (cur_burn_block_height, v1_unlock_ht, v2_unlock_ht, v3_unlock_ht) = clarity_tx
            .with_clarity_db_readonly(|ref mut db| {
                let res: Result<_, Error> = Ok((
                    db.get_current_burnchain_block_height()?,
                    db.get_v1_unlock_height(),
                    db.get_v2_unlock_height()?,
                    db.get_v3_unlock_height()?,
                ));
                res
            })?;

        let consolidated_balance = payer_account
            .stx_balance
            .get_available_balance_at_burn_block(
                u64::from(cur_burn_block_height),
                v1_unlock_ht,
                v2_unlock_ht,
                v3_unlock_ht,
            )?;

        if consolidated_balance < u128::from(fee) {
            return Err(Error::InvalidFee);
        }

        StacksChainState::account_debit(clarity_tx, &payer_account.principal, fee);
        Ok(fee)
    }

    /// Pre-check a transaction -- make sure it's well-formed
    pub fn process_transaction_precheck(
        config: &DBConfig,
        tx: &StacksTransaction,
        epoch_id: StacksEpochId,
    ) -> Result<(), Error> {
        // valid auth?
        if !tx.auth.is_supported_in_epoch(epoch_id) {
            let msg = format!(
                "Invalid tx {}: authentication mode not supported in Epoch {epoch_id}",
                tx.txid()
            );
            warn!("{msg}");

            return Err(Error::InvalidStacksTransaction(msg, false));
        }
        tx.verify().map_err(Error::NetError)?;

        // destined for us?
        if config.chain_id != tx.chain_id {
            let msg = format!(
                "Invalid tx {}: invalid chain ID {} (expected {})",
                tx.txid(),
                tx.chain_id,
                config.chain_id
            );
            warn!("{}", &msg);

            return Err(Error::InvalidStacksTransaction(msg, false));
        }

        match tx.version {
            TransactionVersion::Mainnet => {
                if !config.mainnet {
                    let msg = format!("Invalid tx {}: on testnet; got mainnet", tx.txid());
                    warn!("{}", &msg);

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }
            }
            TransactionVersion::Testnet => {
                if config.mainnet {
                    let msg = format!("Invalid tx {}: on mainnet; got testnet", tx.txid());
                    warn!("{}", &msg);

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }
            }
        }

        Ok(())
    }

    /// Apply a post-conditions check.
    /// Return true if they all pass.
    /// Return false if at least one fails.
    fn check_transaction_postconditions(
        post_conditions: &[TransactionPostCondition],
        post_condition_mode: &TransactionPostConditionMode,
        origin_account: &StacksAccount,
        asset_map: &AssetMap,
        txid: Txid,
    ) -> Result<bool, InterpreterError> {
        let mut checked_fungible_assets: HashMap<PrincipalData, HashSet<AssetIdentifier>> =
            HashMap::new();
        let mut checked_nonfungible_assets: HashMap<
            PrincipalData,
            HashMap<AssetIdentifier, HashSet<HashableClarityValue>>,
        > = HashMap::new();
        let allow_unchecked_assets = *post_condition_mode == TransactionPostConditionMode::Allow;

        for postcond in post_conditions {
            match postcond {
                TransactionPostCondition::STX(
                    ref principal,
                    ref condition_code,
                    ref amount_sent_condition,
                ) => {
                    let account_principal = principal.to_principal_data(&origin_account.principal);

                    let amount_transferred = asset_map.get_stx(&account_principal).unwrap_or(0);
                    let amount_burned = asset_map.get_stx_burned(&account_principal).unwrap_or(0);

                    let amount_sent = amount_transferred
                        .checked_add(amount_burned)
                        .expect("FATAL: sent waaaaay too much STX");

                    if !condition_code.check(u128::from(*amount_sent_condition), amount_sent) {
                        info!(
                            "Post-condition check failure on STX owned by {}: {:?} {:?} {}",
                            account_principal, amount_sent_condition, condition_code, amount_sent; "txid" => %txid
                        );
                        return Ok(false);
                    }

                    if let Some(ref mut asset_ids) =
                        checked_fungible_assets.get_mut(&account_principal)
                    {
                        if amount_transferred > 0 {
                            asset_ids.insert(AssetIdentifier::STX());
                        }
                        if amount_burned > 0 {
                            asset_ids.insert(AssetIdentifier::STX_burned());
                        }
                    } else {
                        let mut h = HashSet::new();
                        if amount_transferred > 0 {
                            h.insert(AssetIdentifier::STX());
                        }
                        if amount_burned > 0 {
                            h.insert(AssetIdentifier::STX_burned());
                        }
                        checked_fungible_assets.insert(account_principal, h);
                    }
                }
                TransactionPostCondition::Fungible(
                    ref principal,
                    ref asset_info,
                    ref condition_code,
                    ref amount_sent_condition,
                ) => {
                    let account_principal = principal.to_principal_data(&origin_account.principal);
                    let asset_id = AssetIdentifier {
                        contract_identifier: QualifiedContractIdentifier::new(
                            StandardPrincipalData::from(asset_info.contract_address.clone()),
                            asset_info.contract_name.clone(),
                        ),
                        asset_name: asset_info.asset_name.clone(),
                    };

                    let amount_sent = asset_map
                        .get_fungible_tokens(&account_principal, &asset_id)
                        .unwrap_or(0);
                    if !condition_code.check(u128::from(*amount_sent_condition), amount_sent) {
                        info!("Post-condition check failure on fungible asset {} owned by {}: {} {:?} {}", &asset_id, account_principal, amount_sent_condition, condition_code, amount_sent; "txid" => %txid);
                        return Ok(false);
                    }

                    if let Some(ref mut asset_ids) =
                        checked_fungible_assets.get_mut(&account_principal)
                    {
                        asset_ids.insert(asset_id);
                    } else {
                        let mut h = HashSet::new();
                        h.insert(asset_id);
                        checked_fungible_assets.insert(account_principal, h);
                    }
                }
                TransactionPostCondition::Nonfungible(
                    ref principal,
                    ref asset_info,
                    ref asset_value,
                    ref condition_code,
                ) => {
                    let account_principal = principal.to_principal_data(&origin_account.principal);
                    let asset_id = AssetIdentifier {
                        contract_identifier: QualifiedContractIdentifier::new(
                            StandardPrincipalData::from(asset_info.contract_address.clone()),
                            asset_info.contract_name.clone(),
                        ),
                        asset_name: asset_info.asset_name.clone(),
                    };

                    let empty_assets = vec![];
                    let assets_sent = asset_map
                        .get_nonfungible_tokens(&account_principal, &asset_id)
                        .unwrap_or(&empty_assets);
                    if !condition_code.check(asset_value, assets_sent) {
                        info!("Post-condition check failure on non-fungible asset {} owned by {}: {:?} {:?}", &asset_id, account_principal, &asset_value, condition_code; "txid" => %txid);
                        return Ok(false);
                    }

                    if let Some(ref mut asset_id_map) =
                        checked_nonfungible_assets.get_mut(&account_principal)
                    {
                        if let Some(ref mut asset_values) = asset_id_map.get_mut(&asset_id) {
                            asset_values.insert(asset_value.clone().try_into()?);
                        } else {
                            let mut asset_set = HashSet::new();
                            asset_set.insert(asset_value.clone().try_into()?);
                            asset_id_map.insert(asset_id, asset_set);
                        }
                    } else {
                        let mut asset_id_map = HashMap::new();
                        let mut asset_set = HashSet::new();
                        asset_set.insert(asset_value.clone().try_into()?);
                        asset_id_map.insert(asset_id, asset_set);
                        checked_nonfungible_assets.insert(account_principal, asset_id_map);
                    }
                }
            }
        }

        if !allow_unchecked_assets {
            // make sure every asset transferred is covered by a postcondition
            let asset_map_copy = (*asset_map).clone();
            let mut all_assets_sent = asset_map_copy.to_table();
            for (principal, mut assets) in all_assets_sent.drain() {
                for (asset_identifier, asset_entry) in assets.drain() {
                    match asset_entry {
                        AssetMapEntry::Asset(values) => {
                            // this is a NFT
                            if let Some(ref checked_nft_asset_map) =
                                checked_nonfungible_assets.get(&principal)
                            {
                                if let Some(ref nfts) = checked_nft_asset_map.get(&asset_identifier)
                                {
                                    // each value must be covered
                                    for v in values {
                                        if !nfts.contains(&v.clone().try_into()?) {
                                            info!("Post-condition check failure: Non-fungible asset {} value {:?} was moved by {} but not checked", &asset_identifier, &v, &principal; "txid" => %txid);
                                            return Ok(false);
                                        }
                                    }
                                } else {
                                    // no values covered
                                    info!("Post-condition check failure: No checks for non-fungible asset type {} moved by {}", &asset_identifier, &principal; "txid" => %txid);
                                    return Ok(false);
                                }
                            } else {
                                // no NFT for this principal
                                info!("Post-condition check failure: No checks for any non-fungible assets, but moved {} by {}", &asset_identifier, &principal; "txid" => %txid);
                                return Ok(false);
                            }
                        }
                        _ => {
                            // This is STX or a fungible token
                            if let Some(ref checked_ft_asset_ids) =
                                checked_fungible_assets.get(&principal)
                            {
                                if !checked_ft_asset_ids.contains(&asset_identifier) {
                                    info!("Post-condition check failure: checks did not cover transfer of {} by {}", &asset_identifier, &principal; "txid" => %txid);
                                    return Ok(false);
                                }
                            } else {
                                info!("Post-condition check failure: No checks for fungible token type {} moved by {}", &asset_identifier, &principal; "txid" => %txid);
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        }
        return Ok(true);
    }

    /// Given two microblock headers, were they signed by the same key?
    /// Return the pubkey hash if so; return Err otherwise
    fn check_microblock_header_signer(
        mblock_hdr_1: &StacksMicroblockHeader,
        mblock_hdr_2: &StacksMicroblockHeader,
    ) -> Result<Hash160, Error> {
        let pkh1 = mblock_hdr_1.check_recover_pubkey().map_err(|e| {
            Error::InvalidStacksTransaction(
                format!("Failed to recover public key: {:?}", &e),
                false,
            )
        })?;

        let pkh2 = mblock_hdr_2.check_recover_pubkey().map_err(|e| {
            Error::InvalidStacksTransaction(
                format!("Failed to recover public key: {:?}", &e),
                false,
            )
        })?;

        if pkh1 != pkh2 {
            let msg = format!(
                "Invalid PoisonMicroblock transaction -- signature pubkey hash {} != {}",
                &pkh1, &pkh2
            );
            warn!("{}", &msg);
            return Err(Error::InvalidStacksTransaction(msg, false));
        }
        Ok(pkh1)
    }

    /// Process a poison-microblock transaction within a Clarity environment.
    /// The code in vm::contexts will call this, via a similarly-named method.
    /// Returns a Value that represents the miner slashed:
    /// * contains the block height of the block with the slashed microblock public key hash
    /// * contains the microblock public key hash
    /// * contains the sender that reported the poison-microblock
    /// * contains the sequence number at which the fork occured
    pub fn handle_poison_microblock(
        env: &mut Environment,
        mblock_header_1: &StacksMicroblockHeader,
        mblock_header_2: &StacksMicroblockHeader,
    ) -> Result<Value, Error> {
        let cost_before = env.global_context.cost_track.get_total();

        // encodes MARF reads for loading microblock height and current height, and loading and storing a
        // poison-microblock report
        runtime_cost(ClarityCostFunction::PoisonMicroblock, env, 0)
            .map_err(|e| Error::from_cost_error(e, cost_before.clone(), &env.global_context))?;

        let sender_principal = match &env.sender {
            Some(ref sender) => {
                if let PrincipalData::Standard(sender) = sender.clone() {
                    sender
                } else {
                    panic!(
                        "BUG: tried to handle poison microblock without a standard principal sender"
                    );
                }
            }
            None => {
                panic!("BUG: tried to handle poison microblock without a sender");
            }
        };

        // is this valid -- were both headers signed by the same key?
        let pubkh =
            StacksChainState::check_microblock_header_signer(mblock_header_1, mblock_header_2)?;

        let microblock_height_opt = env
            .global_context
            .database
            .get_microblock_pubkey_hash_height(&pubkh)?;
        let current_height = env.global_context.database.get_current_block_height();

        // for the microblock public key hash we had to process
        env.add_memory(20)
            .map_err(|e| Error::from_cost_error(e, cost_before.clone(), &env.global_context))?;

        // for the block height we had to load
        env.add_memory(4)
            .map_err(|e| Error::from_cost_error(e, cost_before.clone(), &env.global_context))?;

        // was the referenced public key hash used anytime in the past
        // MINER_REWARD_MATURITY blocks?
        let mblock_pubk_height = match microblock_height_opt {
            None => {
                // public key has never been seen before
                let msg = format!(
                    "Invalid Stacks transaction: microblock public key hash {} never seen in this fork",
                    &pubkh
                );
                warn!("{}", &msg;
                      "microblock_pubkey_hash" => %pubkh
                );

                return Err(Error::InvalidStacksTransaction(msg, false));
            }
            Some(height) => {
                if height
                    .checked_add(
                        u32::try_from(MINER_REWARD_MATURITY).expect("FATAL: maturity > 2^32"),
                    )
                    .expect("BUG: too many blocks")
                    < current_height
                {
                    let msg = format!("Invalid Stacks transaction: microblock public key hash from height {} has matured relative to current height {}", height, current_height);
                    warn!("{}", &msg;
                          "microblock_pubkey_hash" => %pubkh
                    );

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }
                height
            }
        };

        // add punishment / commission record, if one does not already exist at lower sequence
        let (reporter_principal, reported_seq) = if let Some((reporter, seq)) = env
            .global_context
            .database
            .get_microblock_poison_report(mblock_pubk_height)?
        {
            // account for report loaded
            env.add_memory(u64::from(
                TypeSignature::PrincipalType
                    .size()
                    .map_err(InterpreterError::from)?,
            ))
            .map_err(|e| Error::from_cost_error(e, cost_before.clone(), &env.global_context))?;

            // u128 sequence
            env.add_memory(16)
                .map_err(|e| Error::from_cost_error(e, cost_before.clone(), &env.global_context))?;

            if mblock_header_1.sequence < seq {
                // this sender reports a point lower in the stream where a fork occurred, and is now
                // entitled to a commission of the punished miner's coinbase
                debug!("Sender {} reports a better poison-miroblock record (at {}) for key {} at height {} than {} (at {})", &sender_principal, mblock_header_1.sequence, &pubkh, mblock_pubk_height, &reporter, seq;
                    "sender" => %sender_principal,
                    "microblock_pubkey_hash" => %pubkh
                );
                env.global_context.database.insert_microblock_poison(
                    mblock_pubk_height,
                    &sender_principal,
                    mblock_header_1.sequence,
                )?;
                (sender_principal, mblock_header_1.sequence)
            } else {
                // someone else beat the sender to this report
                debug!("Sender {} reports an equal or worse poison-microblock record (at {}, but already have one for {}); dropping...", &sender_principal, mblock_header_1.sequence, seq;
                    "sender" => %sender_principal,
                    "microblock_pubkey_hash" => %pubkh
                );
                (reporter, seq)
            }
        } else {
            // first-ever report of a fork
            debug!(
                "Sender {} reports a poison-microblock record at seq {} for key {} at height {}",
                &sender_principal, mblock_header_1.sequence, &pubkh, &mblock_pubk_height;
                "sender" => %sender_principal,
                "microblock_pubkey_hash" => %pubkh
            );
            env.global_context.database.insert_microblock_poison(
                mblock_pubk_height,
                &sender_principal,
                mblock_header_1.sequence,
            )?;
            (sender_principal, mblock_header_1.sequence)
        };

        let hash_data = BuffData {
            data: pubkh.as_bytes().to_vec(),
        };
        let tuple_data = TupleData::from_data(vec![
            (
                ClarityName::try_from("block_height").expect("BUG: valid string representation"),
                Value::UInt(u128::from(mblock_pubk_height)),
            ),
            (
                ClarityName::try_from("microblock_pubkey_hash")
                    .expect("BUG: valid string representation"),
                Value::Sequence(SequenceData::Buffer(hash_data)),
            ),
            (
                ClarityName::try_from("reporter").expect("BUG: valid string representation"),
                Value::Principal(PrincipalData::Standard(reporter_principal)),
            ),
            (
                ClarityName::try_from("sequence").expect("BUG: valid string representation"),
                Value::UInt(u128::from(reported_seq)),
            ),
        ])
        .expect("BUG: valid tuple representation");

        Ok(Value::Tuple(tuple_data))
    }

    /// Process the transaction's payload, and run the post-conditions against the resulting state.
    ///
    /// NOTE: this does not verify that the transaction can be processed in the clarity_tx's Stacks
    /// epoch.  This check must be performed by the caller before processing the block, e.g. via
    /// StacksBlock::validate_transactions_static().
    ///
    /// Returns the stacks transaction receipt
    pub fn process_transaction_payload(
        clarity_tx: &mut ClarityTransactionConnection,
        tx: &StacksTransaction,
        origin_account: &StacksAccount,
        ast_rules: ASTRules,
    ) -> Result<StacksTransactionReceipt, Error> {
        match tx.payload {
            TransactionPayload::TokenTransfer(ref addr, ref amount, ref memo) => {
                // post-conditions are not allowed for this variant, since they're non-sensical.
                // Their presence in this variant makes the transaction invalid.
                if !tx.post_conditions.is_empty() {
                    let msg = format!("Invalid Stacks transaction: TokenTransfer transactions do not support post-conditions");
                    info!("{}", &msg; "txid" => %tx.txid());

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }

                if *addr == origin_account.principal {
                    let msg = format!("Invalid TokenTransfer: address tried to send to itself");
                    info!("{}", &msg; "txid" => %tx.txid());
                    return Err(Error::InvalidStacksTransaction(msg, false));
                }

                let cost_before = clarity_tx.cost_so_far();
                let (value, _asset_map, events) = clarity_tx
                    .run_stx_transfer(
                        &origin_account.principal,
                        addr,
                        u128::from(*amount),
                        &BuffData {
                            data: Vec::from(memo.0.clone()),
                        },
                    )
                    .map_err(Error::ClarityError)?;

                let mut total_cost = clarity_tx.cost_so_far();
                total_cost
                    .sub(&cost_before)
                    .expect("BUG: total block cost decreased");

                let receipt = StacksTransactionReceipt::from_stx_transfer(
                    tx.clone(),
                    events,
                    value,
                    total_cost,
                );
                Ok(receipt)
            }
            TransactionPayload::ContractCall(ref contract_call) => {
                // if this calls a function that doesn't exist or is syntactically invalid, then the
                // transaction is invalid (since this can be checked statically by the miner).
                // if on the other hand the contract being called has a runtime error, then the
                // transaction is still valid, but no changes will materialize besides debiting the
                // tx fee.
                let contract_id = contract_call.to_clarity_contract_id();
                let cost_before = clarity_tx.cost_so_far();
                let sponsor = tx.sponsor_address().map(|a| a.to_account_principal());
                let epoch_id = clarity_tx.get_epoch();

                let contract_call_resp = clarity_tx.run_contract_call(
                    &origin_account.principal,
                    sponsor.as_ref(),
                    &contract_id,
                    &contract_call.function_name,
                    &contract_call.function_args,
                    |asset_map, _| {
                        !StacksChainState::check_transaction_postconditions(
                            &tx.post_conditions,
                            &tx.post_condition_mode,
                            origin_account,
                            asset_map,
                            tx.txid(),
                        )
                        .expect("FATAL: error while evaluating post-conditions")
                    },
                );

                let mut total_cost = clarity_tx.cost_so_far();
                total_cost
                    .sub(&cost_before)
                    .expect("BUG: total block cost decreased");

                let (result, asset_map, events) = match contract_call_resp {
                    Ok((return_value, asset_map, events)) => {
                        info!("Contract-call successfully processed";
                              "txid" => %tx.txid(),
                              "origin" => %origin_account.principal,
                              "origin_nonce" => %origin_account.nonce,
                              "contract_name" => %contract_id,
                              "function_name" => %contract_call.function_name,
                              "function_args" => %VecDisplay(&contract_call.function_args),
                              "return_value" => %return_value,
                              "cost" => ?total_cost);
                        (return_value, asset_map, events)
                    }
                    Err(e) => match handle_clarity_runtime_error(e) {
                        ClarityRuntimeTxError::Acceptable { error, err_type } => {
                            info!("Contract-call processed with {}", err_type;
                                      "txid" => %tx.txid(),
                                      "origin" => %origin_account.principal,
                                      "origin_nonce" => %origin_account.nonce,
                                      "contract_name" => %contract_id,
                                      "function_name" => %contract_call.function_name,
                                      "function_args" => %VecDisplay(&contract_call.function_args),
                                      "error" => ?error);
                            (Value::err_none(), AssetMap::new(), vec![])
                        }
                        ClarityRuntimeTxError::AbortedByCallback(value, assets, events) => {
                            info!("Contract-call aborted by post-condition";
                                      "txid" => %tx.txid(),
                                      "origin" => %origin_account.principal,
                                      "origin_nonce" => %origin_account.nonce,
                                      "contract_name" => %contract_id,
                                      "function_name" => %contract_call.function_name,
                                      "function_args" => %VecDisplay(&contract_call.function_args));
                            let receipt = StacksTransactionReceipt::from_condition_aborted_contract_call(
                                    tx.clone(),
                                    events,
                                    value.expect("BUG: Post condition contract call must provide would-have-been-returned value"),
                                    assets.get_stx_burned_total()?,
                                    total_cost);
                            return Ok(receipt);
                        }
                        ClarityRuntimeTxError::CostError(cost_after, budget) => {
                            warn!("Block compute budget exceeded: if included, this will invalidate a block"; "txid" => %tx.txid(), "cost" => %cost_after, "budget" => %budget);
                            return Err(Error::CostOverflowError(cost_before, cost_after, budget));
                        }
                        ClarityRuntimeTxError::AnalysisError(check_error) => {
                            if epoch_id >= StacksEpochId::Epoch21 {
                                // in 2.1 and later, this is a permitted runtime error.  take the
                                // fee from the payer and keep the tx.
                                info!("Contract-call encountered an analysis error at runtime";
                                      "txid" => %tx.txid(),
                                      "origin" => %origin_account.principal,
                                      "origin_nonce" => %origin_account.nonce,
                                      "contract_name" => %contract_id,
                                      "function_name" => %contract_call.function_name,
                                      "function_args" => %VecDisplay(&contract_call.function_args),
                                      "error" => %check_error);

                                let receipt =
                                    StacksTransactionReceipt::from_runtime_failure_contract_call(
                                        tx.clone(),
                                        total_cost,
                                        check_error,
                                    );
                                return Ok(receipt);
                            } else {
                                // prior to 2.1, this is not permitted in a block.
                                warn!("Unexpected analysis error invalidating transaction: if included, this will invalidate a block";
                                          "txid" => %tx.txid(),
                                          "origin" => %origin_account.principal,
                                          "origin_nonce" => %origin_account.nonce,
                                           "contract_name" => %contract_id,
                                           "function_name" => %contract_call.function_name,
                                           "function_args" => %VecDisplay(&contract_call.function_args),
                                           "error" => %check_error);
                                return Err(Error::ClarityError(clarity_error::Interpreter(
                                    InterpreterError::Unchecked(check_error),
                                )));
                            }
                        }
                        ClarityRuntimeTxError::Rejectable(e) => {
                            error!("Unexpected error in validating transaction: if included, this will invalidate a block";
                                       "txid" => %tx.txid(),
                                       "origin" => %origin_account.principal,
                                       "origin_nonce" => %origin_account.nonce,
                                       "contract_name" => %contract_id,
                                       "function_name" => %contract_call.function_name,
                                       "function_args" => %VecDisplay(&contract_call.function_args),
                                       "error" => ?e);
                            return Err(Error::ClarityError(e));
                        }
                    },
                };

                let receipt = StacksTransactionReceipt::from_contract_call(
                    tx.clone(),
                    events,
                    result,
                    asset_map.get_stx_burned_total()?,
                    total_cost,
                );
                Ok(receipt)
            }
            TransactionPayload::SmartContract(ref smart_contract, ref version_opt) => {
                let epoch_id = clarity_tx.get_epoch();
                let clarity_version = version_opt
                    .unwrap_or(ClarityVersion::default_for_epoch(clarity_tx.get_epoch()));
                let issuer_principal = match origin_account.principal {
                    PrincipalData::Standard(ref p) => p.clone(),
                    _ => {
                        unreachable!(
                            "BUG: transaction issued by something other than a standard principal"
                        );
                    }
                };

                let contract_id =
                    QualifiedContractIdentifier::new(issuer_principal, smart_contract.name.clone());
                let contract_code_str = smart_contract.code_body.to_string();

                // can't be instantiated already -- if this fails, then the transaction is invalid
                // (because this can be checked statically by the miner before mining the block).
                if StacksChainState::get_contract(clarity_tx, &contract_id)?.is_some() {
                    let msg = format!("Duplicate contract '{}'", &contract_id);
                    info!("{}", &msg);

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }

                let cost_before = clarity_tx.cost_so_far();

                // analysis pass -- if this fails, then the transaction is still accepted, but nothing is stored or processed.
                // The reason for this is that analyzing the transaction is itself an expensive
                // operation, and the paying account will need to be debited the fee regardless.
                let analysis_resp = clarity_tx.analyze_smart_contract(
                    &contract_id,
                    clarity_version,
                    &contract_code_str,
                    ast_rules,
                );
                let (mut contract_ast, contract_analysis) = match analysis_resp {
                    Ok(x) => x,
                    Err(e) => {
                        match e {
                            clarity_error::CostError(ref cost_after, ref budget) => {
                                warn!("Block compute budget exceeded on {}: cost before={}, after={}, budget={}", tx.txid(), &cost_before, cost_after, budget);
                                return Err(Error::CostOverflowError(
                                    cost_before,
                                    cost_after.clone(),
                                    budget.clone(),
                                ));
                            }
                            other_error => {
                                if ast_rules == ASTRules::PrecheckSize {
                                    // a [Vary]ExpressionDepthTooDeep error in this situation
                                    // invalidates the block, since this should have prevented the
                                    // block from getting relayed in the first place
                                    if let clarity_error::Parse(ref parse_error) = &other_error {
                                        match parse_error.err {
                                            ParseErrors::ExpressionStackDepthTooDeep
                                            | ParseErrors::VaryExpressionStackDepthTooDeep => {
                                                info!("Transaction {} is problematic and should have prevented this block from being relayed", tx.txid());
                                                return Err(Error::ClarityError(other_error));
                                            }
                                            _ => {}
                                        }
                                    }
                                }
                                if let clarity_error::Parse(err) = &other_error {
                                    if err.rejectable() {
                                        info!("Transaction {} is problematic and should have prevented this block from being relayed", tx.txid());
                                        return Err(Error::ClarityError(other_error));
                                    }
                                }
                                if let clarity_error::Analysis(err) = &other_error {
                                    if err.err.rejectable() {
                                        info!("Transaction {} is problematic and should have prevented this block from being relayed", tx.txid());
                                        return Err(Error::ClarityError(other_error));
                                    }
                                }
                                // this analysis isn't free -- convert to runtime error
                                let mut analysis_cost = clarity_tx.cost_so_far();
                                analysis_cost
                                    .sub(&cost_before)
                                    .expect("BUG: total block cost decreased");

                                info!(
                                    "Runtime error in contract analysis for {}: {:?}",
                                    &contract_id, &other_error;
                                    "txid" => %tx.txid(),
                                    "AST rules" => %format!("{:?}", &ast_rules)
                                );
                                let receipt = StacksTransactionReceipt::from_analysis_failure(
                                    tx.clone(),
                                    analysis_cost,
                                    other_error,
                                );

                                // abort now -- no burns
                                return Ok(receipt);
                            }
                        }
                    }
                };

                let mut analysis_cost = clarity_tx.cost_so_far();
                analysis_cost
                    .sub(&cost_before)
                    .expect("BUG: total block cost decreased");
                let sponsor = tx.sponsor_address().map(|a| a.to_account_principal());

                // Beginning in epoch 3.0, smart contracts are compiled to Wasm
                // and executed using the Wasm runtime.
                debug!("Before Epoch 3.0 check");
                if epoch_id >= StacksEpochId::Epoch30 {
                    debug!("Compiling the contract to wasm binary");
                    let mut module = compile_contract(contract_analysis.clone()).map_err(|e| {
                        Error::ClarityError(clarity_error::Wasm(WasmError::WasmGeneratorError(
                            e.message(),
                        )))
                    })?;
                    contract_ast.wasm_module = Some(module.emit_wasm());
                }

                // execution -- if this fails due to a runtime error, then the transaction is still
                // accepted, but the contract does not materialize (but the sender is out their fee).
                let initialize_resp = clarity_tx.initialize_smart_contract(
                    &contract_id,
                    clarity_version,
                    &mut contract_ast,
                    &contract_analysis,
                    &contract_code_str,
                    sponsor,
                    |asset_map, _| {
                        !StacksChainState::check_transaction_postconditions(
                            &tx.post_conditions,
                            &tx.post_condition_mode,
                            origin_account,
                            asset_map,
                            tx.txid(),
                        )
                        .expect("FATAL: error while evaluating post-conditions")
                    },
                );

                let mut total_cost = clarity_tx.cost_so_far();
                total_cost
                    .sub(&cost_before)
                    .expect("BUG: total block cost decreased");

                let (asset_map, events) = match initialize_resp {
                    Ok(x) => {
                        // store analysis -- if this fails, then the have some pretty bad problems
                        clarity_tx
                            .save_analysis(&contract_id, &contract_analysis)
                            .expect("FATAL: failed to store contract analysis");
                        x
                    }
                    Err(e) => match handle_clarity_runtime_error(e) {
                        ClarityRuntimeTxError::Acceptable { error, err_type } => {
                            info!("Smart-contract processed with {}", err_type;
                                      "txid" => %tx.txid(),
                                      "contract" => %contract_id,
                                      "code" => %contract_code_str,
                                      "error" => ?error);
                            // When top-level code in a contract publish causes a runtime error,
                            // the transaction is accepted, but the contract is not created.
                            //   Return a tx receipt with an `err_none()` result to indicate
                            //   that the transaction failed during execution.
                            let receipt = StacksTransactionReceipt {
                                transaction: tx.clone().into(),
                                events: vec![],
                                post_condition_aborted: false,
                                result: Value::err_none(),
                                stx_burned: 0,
                                contract_analysis: Some(contract_analysis),
                                execution_cost: total_cost,
                                microblock_header: None,
                                tx_index: 0,
                                vm_error: Some(error.to_string()),
                            };
                            return Ok(receipt);
                        }
                        ClarityRuntimeTxError::AbortedByCallback(_, assets, events) => {
                            let receipt =
                                StacksTransactionReceipt::from_condition_aborted_smart_contract(
                                    tx.clone(),
                                    events,
                                    assets.get_stx_burned_total()?,
                                    contract_analysis,
                                    total_cost,
                                );
                            return Ok(receipt);
                        }
                        ClarityRuntimeTxError::CostError(cost_after, budget) => {
                            warn!("Block compute budget exceeded: if included, this will invalidate a block";
                                      "txid" => %tx.txid(),
                                      "cost" => %cost_after,
                                      "budget" => %budget);
                            return Err(Error::CostOverflowError(cost_before, cost_after, budget));
                        }
                        ClarityRuntimeTxError::AnalysisError(check_error) => {
                            if epoch_id >= StacksEpochId::Epoch21 {
                                // in 2.1 and later, this is a permitted runtime error.  take the
                                // fee from the payer and keep the tx.
                                info!("Smart-contract encountered an analysis error at runtime";
                                      "txid" => %tx.txid(),
                                      "contract" => %contract_id,
                                      "code" => %contract_code_str,
                                      "error" => %check_error);

                                let receipt =
                                    StacksTransactionReceipt::from_runtime_failure_smart_contract(
                                        tx.clone(),
                                        total_cost,
                                        contract_analysis,
                                        check_error,
                                    );
                                return Ok(receipt);
                            } else {
                                // prior to 2.1, this is not permitted in a block.
                                warn!("Unexpected analysis error invalidating transaction: if included, this will invalidate a block";
                                      "txid" => %tx.txid(),
                                      "contract" => %contract_id,
                                      "code" => %contract_code_str,
                                      "error" => %check_error);
                                return Err(Error::ClarityError(clarity_error::Interpreter(
                                    InterpreterError::Unchecked(check_error),
                                )));
                            }
                        }
                        ClarityRuntimeTxError::Rejectable(e) => {
                            error!("Unexpected error invalidating transaction: if included, this will invalidate a block";
                                       "txid" => %tx.txid(),
                                       "contract_name" => %contract_id,
                                       "code" => %contract_code_str,
                                       "error" => ?e);
                            return Err(Error::ClarityError(e));
                        }
                    },
                };

                let receipt = StacksTransactionReceipt::from_smart_contract(
                    tx.clone(),
                    events,
                    asset_map.get_stx_burned_total()?,
                    contract_analysis,
                    total_cost,
                );
                Ok(receipt)
            }
            TransactionPayload::PoisonMicroblock(ref mblock_header_1, ref mblock_header_2) => {
                // post-conditions are not allowed for this variant, since they're non-sensical.
                // Their presence in this variant makes the transaction invalid.
                if !tx.post_conditions.is_empty() {
                    let msg = format!("Invalid Stacks transaction: PoisonMicroblock transactions do not support post-conditions");
                    info!("{}", &msg);

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }

                let cost_before = clarity_tx.cost_so_far();
                let res = clarity_tx.run_poison_microblock(
                    &origin_account.principal,
                    mblock_header_1,
                    mblock_header_2,
                )?;
                let mut cost = clarity_tx.cost_so_far();
                cost.sub(&cost_before)
                    .expect("BUG: running poison microblock tx has negative cost");

                let receipt =
                    StacksTransactionReceipt::from_poison_microblock(tx.clone(), res, cost);

                Ok(receipt)
            }
            TransactionPayload::Coinbase(..) => {
                // no-op; not handled here
                // NOTE: technically, post-conditions are allowed (even if they're non-sensical).

                let receipt = StacksTransactionReceipt::from_coinbase(tx.clone());
                Ok(receipt)
            }
            TransactionPayload::TenureChange(ref payload) => {
                // post-conditions are not allowed for this variant, since they're non-sensical.
                // Their presence in this variant makes the transaction invalid.
                if !tx.post_conditions.is_empty() {
                    let msg = format!("Invalid Stacks transaction: TenureChange transactions do not support post-conditions");
                    info!("{msg}");

                    return Err(Error::InvalidStacksTransaction(msg, false));
                }

                // what kind of tenure-change?
                match payload.cause {
                    TenureChangeCause::BlockFound => {
                        // a sortition triggered this tenure change.
                        // this is already processed, so it's a no-op here.
                    }
                    TenureChangeCause::Extended => {
                        // the stackers granted a tenure extension.
                        // reset the runtime cost
                        debug!(
                            "TenureChange extends block tenure (confirms {} blocks)",
                            &payload.previous_tenure_blocks
                        );
                    }
                }

                let receipt = StacksTransactionReceipt::from_tenure_change(tx.clone());
                Ok(receipt)
            }
        }
    }

    /// Deduce the Clarity version to run
    pub fn get_tx_clarity_version(
        clarity_block: &mut ClarityTx,
        tx: &StacksTransaction,
    ) -> Result<ClarityVersion, Error> {
        let clarity_version = match &tx.payload {
            TransactionPayload::SmartContract(_, ref version_opt) => {
                // did the caller want to run a particular version of Clarity?
                version_opt.unwrap_or(ClarityVersion::default_for_epoch(clarity_block.get_epoch()))
            }
            _ => {
                // whatever the epoch default is, since no Clarity code will be executed anyway
                ClarityVersion::default_for_epoch(clarity_block.get_epoch())
            }
        };
        Ok(clarity_version)
    }

    /// Process a transaction.  Return the fee and the transaction receipt
    pub fn process_transaction(
        clarity_block: &mut ClarityTx,
        tx: &StacksTransaction,
        quiet: bool,
        ast_rules: ASTRules,
    ) -> Result<(u64, StacksTransactionReceipt), Error> {
        debug!("Process transaction {} ({})", tx.txid(), tx.payload.name());
        let epoch = clarity_block.get_epoch();

        StacksChainState::process_transaction_precheck(&clarity_block.config, tx, epoch)?;

        // what version of Clarity did the transaction caller want? And, is it valid now?
        let clarity_version = StacksChainState::get_tx_clarity_version(clarity_block, tx)?;
        if clarity_version == ClarityVersion::Clarity2 {
            // requires 2.1 and higher
            if clarity_block.get_epoch() < StacksEpochId::Epoch21 {
                let msg = format!("Invalid transaction {}: asks for Clarity2, but not in Stacks epoch 2.1 or later", tx.txid());
                info!("{}", &msg);
                return Err(Error::InvalidStacksTransaction(msg, false));
            }
        }

        let mut transaction = clarity_block.connection().start_transaction_processing();

        let fee = tx.get_tx_fee();
        let tx_receipt = if epoch >= StacksEpochId::Epoch21 {
            // 2.1 and later: pay tx fee, then process transaction
            let (_origin_account, payer_account) =
                StacksChainState::check_transaction_nonces(&mut transaction, tx, quiet)?;

            let payer_address = payer_account.principal.clone();
            let payer_nonce = payer_account.nonce;
            StacksChainState::pay_transaction_fee(&mut transaction, fee, payer_account)?;

            // origin balance may have changed (e.g. if the origin paid the tx fee), so reload the account
            let origin_account =
                StacksChainState::get_account(&mut transaction, &tx.origin_address().into());

            let tx_receipt = StacksChainState::process_transaction_payload(
                &mut transaction,
                tx,
                &origin_account,
                ast_rules,
            )?;

            // update the account nonces
            StacksChainState::update_account_nonce(
                &mut transaction,
                &origin_account.principal,
                origin_account.nonce,
            );
            if origin_account.principal != payer_address {
                // payer is a different account, so update its nonce too
                StacksChainState::update_account_nonce(
                    &mut transaction,
                    &payer_address,
                    payer_nonce,
                );
            }

            tx_receipt
        } else {
            // pre-2.1: process transaction, then pay tx fee
            let (origin_account, payer_account) =
                StacksChainState::check_transaction_nonces(&mut transaction, tx, quiet)?;

            let tx_receipt = StacksChainState::process_transaction_payload(
                &mut transaction,
                tx,
                &origin_account,
                ast_rules,
            )?;

            let new_payer_account = StacksChainState::get_payer_account(&mut transaction, tx);
            StacksChainState::pay_transaction_fee(&mut transaction, fee, new_payer_account)?;

            // update the account nonces
            StacksChainState::update_account_nonce(
                &mut transaction,
                &origin_account.principal,
                origin_account.nonce,
            );
            if origin_account != payer_account {
                StacksChainState::update_account_nonce(
                    &mut transaction,
                    &payer_account.principal,
                    payer_account.nonce,
                );
            }

            tx_receipt
        };

        transaction
            .commit()
            .map_err(|e| Error::InvalidStacksTransaction(e.to_string(), false))?;

        Ok((fee, tx_receipt))
    }
}

#[cfg(test)]
pub mod test {
    use clarity::vm::clarity::TransactionConnection;
    use clarity::vm::contracts::Contract;
    use clarity::vm::representations::{ClarityName, ContractName};
    use clarity::vm::test_util::{UnitTestBurnStateDB, TEST_BURN_STATE_DB};
    use clarity::vm::tests::TEST_HEADER_DB;
    use clarity::vm::types::*;
    use rand::Rng;
    use stacks_common::types::chainstate::SortitionId;
    use stacks_common::util::hash::*;

    use super::*;
    use crate::burnchains::Address;
    use crate::chainstate::stacks::boot::*;
    use crate::chainstate::stacks::db::test::*;
    use crate::chainstate::stacks::index::storage::*;
    use crate::chainstate::stacks::index::*;
    use crate::chainstate::stacks::{Error, *};
    use crate::chainstate::*;

    pub const TestBurnStateDB_20: UnitTestBurnStateDB = UnitTestBurnStateDB {
        epoch_id: StacksEpochId::Epoch20,
        ast_rules: ASTRules::Typical,
    };
    pub const TestBurnStateDB_2_05: UnitTestBurnStateDB = UnitTestBurnStateDB {
        epoch_id: StacksEpochId::Epoch2_05,
        ast_rules: ASTRules::PrecheckSize,
    };
    pub const TestBurnStateDB_21: UnitTestBurnStateDB = UnitTestBurnStateDB {
        epoch_id: StacksEpochId::Epoch21,
        ast_rules: ASTRules::PrecheckSize,
    };

    pub const ALL_BURN_DBS: &[&dyn BurnStateDB] = &[
        &TestBurnStateDB_20 as &dyn BurnStateDB,
        &TestBurnStateDB_2_05 as &dyn BurnStateDB,
        &TestBurnStateDB_21 as &dyn BurnStateDB,
    ];

    pub const PRE_21_DBS: &[&dyn BurnStateDB] = &[
        &TestBurnStateDB_20 as &dyn BurnStateDB,
        &TestBurnStateDB_2_05 as &dyn BurnStateDB,
    ];

    #[test]
    fn contract_publish_runtime_error() {
        let contract_id = QualifiedContractIdentifier::local("contract").unwrap();
        let address = "'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR";
        let sender = PrincipalData::parse(address).unwrap();

        let marf_kv = MarfedKV::temporary();
        let chain_id = 0x80000000;
        let mut clarity_instance = ClarityInstance::new(false, chain_id, marf_kv);
        let mut genesis = clarity_instance.begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB,
        );
        genesis.initialize_epoch_2_05().unwrap();
        genesis.initialize_epoch_2_1().unwrap();
        genesis.as_transaction(|tx_conn| {
            // bump the epoch in the Clarity DB
            tx_conn
                .with_clarity_db(|db| {
                    db.set_clarity_epoch_version(StacksEpochId::Epoch21)
                        .unwrap();
                    Ok(())
                })
                .unwrap();
        });
        genesis.commit_block();

        let mut next_block = clarity_instance.begin_block(
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &StacksBlockId([3; 32]),
            &TEST_HEADER_DB,
            &TEST_BURN_STATE_DB,
        );

        let mut tx_conn = next_block.start_transaction_processing();
        let sk = secp256k1::Secp256k1PrivateKey::new();

        let tx = StacksTransaction {
            version: TransactionVersion::Testnet,
            chain_id,
            auth: TransactionAuth::from_p2pkh(&sk).unwrap(),
            anchor_mode: TransactionAnchorMode::Any,
            post_condition_mode: TransactionPostConditionMode::Allow,
            post_conditions: vec![],
            payload: TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: "test-contract".into(),
                    code_body: StacksString::from_str("(/ 1 0)").unwrap(),
                },
                None,
            ),
        };
        let receipt = StacksChainState::process_transaction_payload(
            &mut tx_conn,
            &tx,
            &StacksAccount {
                principal: sender.clone(),
                nonce: 0,
                stx_balance: STXBalance::Unlocked { amount: 100 },
            },
            ASTRules::PrecheckSize,
        )
        .unwrap();

        assert_eq!(receipt.result, Value::err_none());
        assert!(receipt.vm_error.unwrap().starts_with("DivisionByZero"));
    }

    #[test]
    fn process_token_transfer_stx_transaction() {
        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        let mut tx_stx_transfer = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        tx_stx_transfer.chain_id = 0x80000000;
        tx_stx_transfer.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_stx_transfer);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            // give the spending account some stx
            let _account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            let recv_account =
                StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());

            assert_eq!(recv_account.stx_balance.amount_unlocked(), 0);
            assert_eq!(recv_account.nonce, 0);

            conn.connection().as_transaction(|tx| {
                StacksChainState::account_credit(tx, &addr.to_account_principal(), 223)
            });

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account_after =
                StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account_after.nonce, 1);
            assert_eq!(account_after.stx_balance.amount_unlocked(), 100);

            let recv_account_after =
                StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
            assert_eq!(recv_account_after.nonce, 0);
            assert_eq!(recv_account_after.stx_balance.amount_unlocked(), 123);

            assert_eq!(fee, 0);

            let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
            let recv_addr = PrincipalData::from(QualifiedContractIdentifier {
                issuer: StacksAddress {
                    version: 1,
                    bytes: Hash160([0xfe; 20]),
                }
                .into(),
                name: "contract-hellow".into(),
            });

            let mut tx_stx_transfer = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth.clone(),
                TransactionPayload::TokenTransfer(
                    recv_addr.clone(),
                    100,
                    TokenTransferMemo([0u8; 34]),
                ),
            );

            tx_stx_transfer.chain_id = 0x80000000;
            tx_stx_transfer.post_condition_mode = TransactionPostConditionMode::Allow;
            tx_stx_transfer.set_tx_fee(0);
            tx_stx_transfer.set_origin_nonce(1);

            let mut signer = StacksTransactionSigner::new(&tx_stx_transfer);
            signer.sign_origin(&privk).unwrap();

            let signed_tx = signer.get_tx().unwrap();

            let recv_account = StacksChainState::get_account(&mut conn, &recv_addr);

            assert_eq!(recv_account.stx_balance.amount_unlocked(), 0);
            assert_eq!(recv_account.nonce, 0);

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account_after =
                StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account_after.nonce, 2);
            assert_eq!(account_after.stx_balance.amount_unlocked(), 0);

            let recv_account_after = StacksChainState::get_account(&mut conn, &recv_addr);
            assert_eq!(recv_account_after.nonce, 0);
            assert_eq!(recv_account_after.stx_balance.amount_unlocked(), 100);

            assert_eq!(fee, 0);

            conn.commit_block();
        }
    }

    #[test]
    fn process_token_transfer_stx_transaction_invalid() {
        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let privk_sponsor = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();

        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let sponsor_addr = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk_sponsor)],
        )
        .unwrap();
        let recv_addr = addr.clone(); // shouldn't be allowed

        let auth_sponsored = {
            let auth_origin = TransactionAuth::from_p2pkh(&privk).unwrap();
            let auth_sponsor = TransactionAuth::from_p2pkh(&privk_sponsor).unwrap();
            auth_origin.into_sponsored(auth_sponsor).unwrap()
        };

        let mut tx_stx_transfer_same_receiver = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let mut tx_stx_transfer_wrong_network = StacksTransaction::new(
            TransactionVersion::Mainnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                sponsor_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let mut tx_stx_transfer_wrong_chain_id = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                sponsor_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let mut tx_stx_transfer_postconditions = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                sponsor_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        tx_stx_transfer_postconditions.add_post_condition(TransactionPostCondition::STX(
            PostConditionPrincipal::Origin,
            FungibleConditionCode::SentGt,
            0,
        ));

        let mut wrong_nonce_auth = auth.clone();
        wrong_nonce_auth.set_origin_nonce(1);
        let mut tx_stx_transfer_wrong_nonce = StacksTransaction::new(
            TransactionVersion::Testnet,
            wrong_nonce_auth,
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let mut wrong_nonce_auth_sponsored = auth_sponsored.clone();
        wrong_nonce_auth_sponsored.set_sponsor_nonce(1).unwrap();
        let mut tx_stx_transfer_wrong_nonce_sponsored = StacksTransaction::new(
            TransactionVersion::Testnet,
            wrong_nonce_auth_sponsored,
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        tx_stx_transfer_same_receiver.chain_id = 0x80000000;
        tx_stx_transfer_wrong_network.chain_id = 0x80000000;
        tx_stx_transfer_wrong_chain_id.chain_id = 0x80000001;
        tx_stx_transfer_postconditions.chain_id = 0x80000000;
        tx_stx_transfer_wrong_nonce.chain_id = 0x80000000;
        tx_stx_transfer_wrong_nonce_sponsored.chain_id = 0x80000000;

        tx_stx_transfer_same_receiver.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer_wrong_network.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer_wrong_chain_id.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer_postconditions.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer_wrong_nonce.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer_wrong_nonce_sponsored.post_condition_mode =
            TransactionPostConditionMode::Allow;

        tx_stx_transfer_same_receiver.set_tx_fee(0);
        tx_stx_transfer_wrong_network.set_tx_fee(0);
        tx_stx_transfer_wrong_chain_id.set_tx_fee(0);
        tx_stx_transfer_postconditions.set_tx_fee(0);
        tx_stx_transfer_wrong_nonce.set_tx_fee(0);
        tx_stx_transfer_wrong_nonce_sponsored.set_tx_fee(0);

        let error_frags = vec![
            "address tried to send to itself".to_string(),
            "on testnet; got mainnet".to_string(),
            "invalid chain ID".to_string(),
            "do not support post-conditions".to_string(),
            "Bad nonce".to_string(),
            "Bad nonce".to_string(),
        ];

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            conn.connection().as_transaction(|tx| {
                StacksChainState::account_credit(tx, &addr.to_account_principal(), 123)
            });

            for (tx_stx_transfer, err_frag) in [
                tx_stx_transfer_same_receiver.clone(),
                tx_stx_transfer_wrong_network.clone(),
                tx_stx_transfer_wrong_chain_id.clone(),
                tx_stx_transfer_postconditions.clone(),
                tx_stx_transfer_wrong_nonce.clone(),
                tx_stx_transfer_wrong_nonce_sponsored.clone(),
            ]
            .iter()
            .zip(error_frags.clone())
            {
                let mut signer = StacksTransactionSigner::new(&tx_stx_transfer);
                signer.sign_origin(&privk).unwrap();

                if tx_stx_transfer.auth.is_sponsored() {
                    signer.sign_sponsor(&privk_sponsor).unwrap();
                }

                let signed_tx = signer.get_tx().unwrap();

                // give the spending account some stx
                let account =
                    StacksChainState::get_account(&mut conn, &addr.to_account_principal());

                assert_eq!(account.stx_balance.amount_unlocked(), 123);
                assert_eq!(account.nonce, 0);

                let res = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx,
                    false,
                    ASTRules::PrecheckSize,
                );
                assert!(res.is_err());

                match res {
                    Err(Error::InvalidStacksTransaction(msg, false)) => {
                        assert!(msg.contains(&err_frag), "{}", err_frag);
                    }
                    _ => {
                        eprintln!("bad error: {:?}", &res);
                        eprintln!("Expected '{}'", &err_frag);
                        assert!(false);
                    }
                }

                let account_after =
                    StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                assert_eq!(account_after.stx_balance.amount_unlocked(), 123);
                assert_eq!(account_after.nonce, 0);
            }

            conn.commit_block();
        }
    }

    #[test]
    fn process_token_transfer_stx_sponsored_transaction() {
        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk_origin = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let privk_sponsor = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();

        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_sponsor = TransactionAuth::from_p2pkh(&privk_sponsor).unwrap();
        let auth = auth_origin.into_sponsored(auth_sponsor).unwrap();

        let addr = auth.origin().address_testnet();
        let addr_sponsor = auth.sponsor().unwrap().address_testnet();

        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        let mut tx_stx_transfer = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        tx_stx_transfer.chain_id = 0x80000000;
        tx_stx_transfer.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_stx_transfer);
        signer.sign_origin(&privk_origin).unwrap();
        signer.sign_sponsor(&privk_sponsor).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            let account_sponsor =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            let recv_account =
                StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());

            assert_eq!(account.nonce, 0);
            assert_eq!(account_sponsor.nonce, 0);
            assert_eq!(account_sponsor.stx_balance.amount_unlocked(), 0);
            assert_eq!(recv_account.nonce, 0);
            assert_eq!(recv_account.stx_balance.amount_unlocked(), 0);

            // give the spending account some stx
            conn.connection().as_transaction(|tx| {
                StacksChainState::account_credit(tx, &addr.to_account_principal(), 123)
            });

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account_after =
                StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account_after.nonce, 1);
            assert_eq!(account_after.stx_balance.amount_unlocked(), 0);

            let account_sponsor_after =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            assert_eq!(account_sponsor_after.nonce, 1);
            assert_eq!(account_sponsor_after.stx_balance.amount_unlocked(), 0);

            let recv_account_after =
                StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
            assert_eq!(recv_account_after.nonce, 0);
            assert_eq!(recv_account_after.stx_balance.amount_unlocked(), 123);

            conn.commit_block();

            assert_eq!(fee, 0);
        }
    }

    #[test]
    fn process_smart_contract_transaction() {
        let contract = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("hello-world"),
            );
            let contract_before_res =
                StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            assert!(contract_before_res.is_none());

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 0);

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 1);

            let contract_res = StacksChainState::get_contract(&mut conn, &contract_id);

            conn.commit_block();

            assert_eq!(fee, 0);
            assert!(contract_res.is_ok());
        }
    }

    #[test]
    fn process_smart_contract_transaction_invalid() {
        let contract_correct = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let contract_syntax_error = "
        (define-data-var bar int 0)) ;; oops
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let contracts = [
                contract_correct,
                contract_correct,
                contract_syntax_error, // should still be mined, even though analysis fails
            ];

            let expected_behavior = [true, false, true];

            let contract_names = ["hello-world-0", "hello-world-0", "hello-world-1"];

            let mut next_nonce = 0;
            for i in 0..contracts.len() {
                let contract_name = contract_names[i].to_string();
                let contract = contracts[i].to_string();

                test_debug!("\ninstantiate contract\n{}\n", &contracts[i]);

                let mut tx_contract = StacksTransaction::new(
                    TransactionVersion::Testnet,
                    auth.clone(),
                    TransactionPayload::new_smart_contract(&contract_name, &contract, None)
                        .unwrap(),
                );

                tx_contract.chain_id = 0x80000000;
                tx_contract.set_tx_fee(0);
                tx_contract.set_origin_nonce(next_nonce);

                let mut signer = StacksTransactionSigner::new(&tx_contract);
                signer.sign_origin(&privk).unwrap();

                let signed_tx = signer.get_tx().unwrap();

                let _contract_id = QualifiedContractIdentifier::new(
                    StandardPrincipalData::from(addr.clone()),
                    ContractName::from(contract_name.as_str()),
                );

                let account =
                    StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                assert_eq!(account.nonce, next_nonce);

                let res = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx,
                    false,
                    ASTRules::PrecheckSize,
                );
                if expected_behavior[i] {
                    assert!(res.is_ok());

                    // account nonce should increment
                    let account =
                        StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                    assert_eq!(account.nonce, next_nonce + 1);

                    next_nonce += 1;
                } else {
                    assert!(res.is_err());

                    // account nonce should NOT increment
                    let account =
                        StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                    assert_eq!(account.nonce, next_nonce);
                    continue;
                }
            }
            conn.commit_block();
        }
    }

    #[test]
    fn process_smart_contract_transaction_syntax_error() {
        let contracts = [
            "(define-data-var bar int 0)) ;; oops",
            ";; `Int` instead of `int`
             (define-data-var bar Int 0)",
        ];
        let contract_names = ["hello-world-0", "hello-world-1"];
        let expected_line_num_error = if cfg!(feature = "developer-mode") {
            ":2:14: invalid variable definition"
        } else {
            ":0:0: invalid variable definition"
        };
        let expected_errors = [
            "Tried to close list which isn't open.",
            expected_line_num_error,
        ];
        let expected_errors_2_1 = ["unexpected ')'", expected_line_num_error];

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let mut next_nonce = 0;
            for i in 0..contracts.len() {
                let contract_name = contract_names[i];
                let contract = contracts[i].to_string();

                test_debug!("\ninstantiate contract\n{}\n", &contract);

                let mut tx_contract = StacksTransaction::new(
                    TransactionVersion::Testnet,
                    auth.clone(),
                    TransactionPayload::new_smart_contract(&contract_name, &contract, None)
                        .unwrap(),
                );

                tx_contract.chain_id = 0x80000000;
                tx_contract.set_tx_fee(0);
                tx_contract.set_origin_nonce(next_nonce);

                let mut signer = StacksTransactionSigner::new(&tx_contract);
                signer.sign_origin(&privk).unwrap();

                let signed_tx = signer.get_tx().unwrap();

                let _contract_id = QualifiedContractIdentifier::new(
                    StandardPrincipalData::from(addr.clone()),
                    ContractName::from(contract_name),
                );

                let (fee, receipt) = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();

                // Verify that the syntax error is recorded in the receipt
                let expected_error =
                    if burn_db.get_stacks_epoch(0).unwrap().epoch_id == StacksEpochId::Epoch21 {
                        expected_errors_2_1[i].to_string()
                    } else {
                        expected_errors[i].to_string()
                    };
                assert_eq!(receipt.vm_error.unwrap(), expected_error);

                next_nonce += 1;
            }

            conn.commit_block();
        }
    }

    #[test]
    fn process_smart_contract_transaction_runtime_error() {
        let contract_correct = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let contract_runtime_error_definition = "
        (define-data-var bar int (/ 1 0))   ;; divide-by-zero
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let contract_runtime_error_bare_code = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))
        (begin (set-bar 1 0) (ok 1))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let contracts = [
                contract_correct,
                contract_runtime_error_definition,
                contract_runtime_error_bare_code,
            ];

            let contract_names = ["hello-world-0", "hello-world-1", "hello-world-2"];

            for i in 0..contracts.len() {
                let contract_name = contract_names[i].to_string();
                let contract = contracts[i].to_string();

                let mut tx_contract = StacksTransaction::new(
                    TransactionVersion::Testnet,
                    auth.clone(),
                    TransactionPayload::new_smart_contract(&contract_name, &contract, None)
                        .unwrap(),
                );

                tx_contract.chain_id = 0x80000000;
                tx_contract.set_tx_fee(0);
                tx_contract.set_origin_nonce(i as u64);

                let mut signer = StacksTransactionSigner::new(&tx_contract);
                signer.sign_origin(&privk).unwrap();

                let signed_tx = signer.get_tx().unwrap();

                let contract_id = QualifiedContractIdentifier::new(
                    StandardPrincipalData::from(addr.clone()),
                    ContractName::from(contract_name.as_str()),
                );
                let contract_before_res =
                    StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
                assert!(contract_before_res.is_none());

                let account =
                    StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                assert_eq!(account.nonce, i as u64);

                // runtime error should be handled
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();

                // account nonce should increment
                let account =
                    StacksChainState::get_account(&mut conn, &addr.to_account_principal());
                assert_eq!(account.nonce, (i + 1) as u64);

                // contract is instantiated despite runtime error
                let contract_res = StacksChainState::get_contract(&mut conn, &contract_id);
                assert!(contract_res.is_ok());
            }

            conn.commit_block();
        }
    }

    #[test]
    fn process_smart_contract_sponsored_transaction() {
        let contract = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk_origin = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let privk_sponsor = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();

        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_sponsor = TransactionAuth::from_p2pkh(&privk_sponsor).unwrap();

        let auth = auth_origin.into_sponsored(auth_sponsor).unwrap();

        let addr = auth.origin().address_testnet();
        let addr_sponsor = auth.sponsor().unwrap().address_testnet();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk_origin).unwrap();
        signer.sign_sponsor(&privk_sponsor).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("hello-world"),
            );
            let contract_before_res =
                StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            assert!(contract_before_res.is_none());

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 0);

            let _account_sponsor =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            assert_eq!(account.nonce, 0);

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 1);

            let account_sponsor =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            assert_eq!(account_sponsor.nonce, 1);

            let contract_res = StacksChainState::get_contract(&mut conn, &contract_id);

            conn.commit_block();

            assert_eq!(fee, 0);
            assert!(contract_res.is_ok());
        }
    }

    #[test]
    fn process_smart_contract_contract_call_transaction() {
        let contract = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        // contract-call
        let privk_2 = StacksPrivateKey::from_hex(
            "d2c340ebcc0794b6fabdd8ac8b1c983e363b05dc8adcdf7e30db205a3fa54c1601",
        )
        .unwrap();
        let auth_2 = TransactionAuth::from_p2pkh(&privk_2).unwrap();
        let addr_2 = auth.origin().address_testnet();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_2.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "hello-world",
                "set-bar",
                vec![Value::Int(6), Value::Int(2)],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);

        let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
        signer_2.sign_origin(&privk_2).unwrap();

        let signed_tx_2 = signer_2.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            // process both
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 0);

            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
            assert_eq!(account_2.nonce, 0);

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("hello-world"),
            );
            let contract_before_res =
                StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            assert!(contract_before_res.is_none());

            let var_before_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
            assert!(var_before_res.is_none());

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let var_before_set_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
            assert_eq!(var_before_set_res, Some(Value::Int(0)));

            let (fee_2, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_2,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 1);

            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
            assert_eq!(account_2.nonce, 1);

            let contract_res = StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            let var_res = StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();

            conn.commit_block();

            assert_eq!(fee, 0);
            assert_eq!(fee_2, 0);
            assert!(contract_res.is_some());
            assert!(var_res.is_some());
            assert_eq!(var_res, Some(Value::Int(3)));
        }
    }

    // Verify that a contract call transaction which passes a long contract
    // name (> 40 chars and < 128) is processed successfully.
    #[test]
    fn process_contract_call_long_contract_name_transaction() {
        let contract = "
        (define-data-var savedContract principal tx-sender)
        (define-public (save (contract principal)) (ok (var-set savedContract contract)))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        // contract-call
        let privk_2 = StacksPrivateKey::from_hex(
            "d2c340ebcc0794b6fabdd8ac8b1c983e363b05dc8adcdf7e30db205a3fa54c1601",
        )
        .unwrap();
        let auth_2 = TransactionAuth::from_p2pkh(&privk_2).unwrap();
        let addr_2 = auth.origin().address_testnet();

        let contractPrincipalValue =
            Value::Principal(PrincipalData::Contract(QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("aip10-arkadiko-update-tvl-liquidation-ratio"),
            )));
        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_2.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "hello-world",
                "save",
                vec![contractPrincipalValue.clone()],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);

        let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
        signer_2.sign_origin(&privk_2).unwrap();

        let signed_tx_2 = signer_2.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            // process both
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 0);

            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
            assert_eq!(account_2.nonce, 0);

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("hello-world"),
            );
            let contract_before_res =
                StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            assert!(contract_before_res.is_none());

            let var_before_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "savedContract").unwrap();
            assert!(var_before_res.is_none());

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let var_before_set_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "savedContract").unwrap();
            assert_eq!(
                var_before_set_res,
                Some(Value::Principal(PrincipalData::from(addr.clone())))
            );

            let (fee_2, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_2,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account = StacksChainState::get_account(&mut conn, &addr.to_account_principal());
            assert_eq!(account.nonce, 1);

            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
            assert_eq!(account_2.nonce, 1);

            let contract_res = StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            let var_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "savedContract").unwrap();

            conn.commit_block();

            assert_eq!(fee, 0);
            assert_eq!(fee_2, 0);
            assert!(contract_res.is_some());
            assert!(var_res.is_some());
            assert_eq!(var_res, Some(contractPrincipalValue.clone()));
        }
    }

    #[test]
    fn process_smart_contract_contract_call_runtime_error() {
        let contract = "
        (define-data-var bar int 1)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))
        (define-public (return-error) (err 1))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr.clone()),
                ContractName::from("hello-world"),
            );
            let (_fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // contract-calls that don't commit
            let contract_calls = vec![
                ("hello-world", "set-bar", vec![Value::Int(1), Value::Int(0)]), // divide-by-zero
                ("hello-world", "return-error", vec![]), // returns an (err ...)
            ];

            // do contract-calls
            let privk_2 = StacksPrivateKey::from_hex(
                "d2c340ebcc0794b6fabdd8ac8b1c983e363b05dc8adcdf7e30db205a3fa54c1601",
            )
            .unwrap();
            let auth_2 = TransactionAuth::from_p2pkh(&privk_2).unwrap();
            let addr_2 = auth_2.origin().address_testnet();

            let mut next_nonce = 0;

            for contract_call in contract_calls {
                let (contract_name, contract_function, contract_args) = contract_call;
                let mut tx_contract_call = StacksTransaction::new(
                    TransactionVersion::Testnet,
                    auth_2.clone(),
                    TransactionPayload::new_contract_call(
                        addr.clone(),
                        contract_name,
                        contract_function,
                        contract_args,
                    )
                    .unwrap(),
                );

                tx_contract_call.chain_id = 0x80000000;
                tx_contract_call.set_tx_fee(0);
                tx_contract_call.set_origin_nonce(next_nonce);

                let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
                signer_2.sign_origin(&privk_2).unwrap();

                let signed_tx_2 = signer_2.get_tx().unwrap();

                let account_2 =
                    StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
                assert_eq!(account_2.nonce, next_nonce);

                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx_2,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();

                // nonce should have incremented
                next_nonce += 1;
                let account_2 =
                    StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
                assert_eq!(account_2.nonce, next_nonce);

                // var should not have changed
                let var_res =
                    StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
                assert!(var_res.is_some());
                assert_eq!(var_res, Some(Value::Int(1)));
            }
            conn.commit_block();
        }
    }

    #[test]
    fn process_smart_contract_user_aborts_2257() {
        let contract = "(asserts! false (err 1))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::from("hello-world"),
        );

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );
            let (_fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            conn.commit_block();
        }
    }

    #[test]
    fn process_smart_contract_contract_call_invalid() {
        let contract = "
        (define-data-var bar int 1)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::from("hello-world"),
        );

        // for contract-calls
        let privk_2 = StacksPrivateKey::from_hex(
            "d2c340ebcc0794b6fabdd8ac8b1c983e363b05dc8adcdf7e30db205a3fa54c1601",
        )
        .unwrap();
        let auth_2 = TransactionAuth::from_p2pkh(&privk_2).unwrap();
        let addr_2 = auth_2.origin().address_testnet();

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        // invalid contract-calls
        let contract_calls = vec![
            (
                addr.clone(),
                "hello-world",
                "set-bar-not-a-method",
                vec![Value::Int(1), Value::Int(1)],
            ), // call into non-existant method
            (
                addr.clone(),
                "hello-world-not-a-contract",
                "set-bar",
                vec![Value::Int(1), Value::Int(1)],
            ), // call into non-existant contract
            (
                addr_2.clone(),
                "hello-world",
                "set-bar",
                vec![Value::Int(1), Value::Int(1)],
            ), // address does not have a contract
            (addr.clone(), "hello-world", "set-bar", vec![Value::Int(1)]), // wrong number of args (too few)
            (
                addr.clone(),
                "hello-world",
                "set-bar",
                vec![Value::Int(1), Value::Int(1), Value::Int(1)],
            ), // wrong number of args (too many)
            (
                addr.clone(),
                "hello-world",
                "set-bar",
                vec![Value::buff_from([0xff, 4].to_vec()).unwrap(), Value::Int(1)],
            ), // wrong arg type
            (
                addr.clone(),
                "hello-world",
                "set-bar",
                vec![Value::UInt(1), Value::Int(1)],
            ), // wrong arg type
        ];

        for (dbi, burn_db) in PRE_21_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );
            let (_fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let next_nonce = 0;

            for contract_call in contract_calls.iter() {
                let (contract_addr, contract_name, contract_function, contract_args) =
                    contract_call.clone();
                let mut tx_contract_call = StacksTransaction::new(
                    TransactionVersion::Testnet,
                    auth_2.clone(),
                    TransactionPayload::new_contract_call(
                        contract_addr.clone(),
                        contract_name,
                        contract_function,
                        contract_args,
                    )
                    .unwrap(),
                );

                tx_contract_call.chain_id = 0x80000000;
                tx_contract_call.set_tx_fee(0);

                let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
                signer_2.sign_origin(&privk_2).unwrap();

                let signed_tx_2 = signer_2.get_tx().unwrap();

                let account_2 =
                    StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
                assert_eq!(account_2.nonce, next_nonce);

                // transaction is invalid, and won't be mined
                let res = StacksChainState::process_transaction(
                    &mut conn,
                    &signed_tx_2,
                    false,
                    ASTRules::PrecheckSize,
                );
                assert!(res.is_err());

                // nonce should NOT have incremented
                let account_2 =
                    StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
                assert_eq!(account_2.nonce, next_nonce);

                // var should NOT have changed
                let var_res =
                    StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
                assert!(var_res.is_some());
                assert_eq!(var_res, Some(Value::Int(1)));
            }
            conn.commit_block();
        }

        // in 2.1, all of these are mineable -- the fee will be collected, and the nonce(s) will
        // advance, but no state changes go through
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );
        let (_fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        let mut next_nonce = 0;

        for contract_call in contract_calls.iter() {
            let (contract_addr, contract_name, contract_function, contract_args) =
                contract_call.clone();
            let mut tx_contract_call = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_2.clone(),
                TransactionPayload::new_contract_call(
                    contract_addr.clone(),
                    contract_name,
                    contract_function,
                    contract_args,
                )
                .unwrap(),
            );

            tx_contract_call.chain_id = 0x80000000;
            tx_contract_call.set_tx_fee(0);
            tx_contract_call.set_origin_nonce(next_nonce);

            let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
            signer_2.sign_origin(&privk_2).unwrap();

            let signed_tx_2 = signer_2.get_tx().unwrap();

            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());

            assert_eq!(account_2.nonce, next_nonce);

            // this is expected to be mined
            let res = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_2,
                false,
                ASTRules::PrecheckSize,
            );
            assert!(res.is_ok());

            next_nonce += 1;
            let account_2 =
                StacksChainState::get_account(&mut conn, &addr_2.to_account_principal());
            assert_eq!(account_2.nonce, next_nonce);

            // no state change though
            let var_res = StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
            assert!(var_res.is_some());
            assert_eq!(var_res, Some(Value::Int(1)));
        }
    }

    #[test]
    fn process_smart_contract_contract_call_sponsored_transaction() {
        let contract = "
        (define-data-var bar int 0)
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        // contract instantiation
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr_publisher = auth.origin().address_testnet();

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk).unwrap();

        let signed_tx = signer.get_tx().unwrap();

        // sponsored contract-call
        let privk_origin = StacksPrivateKey::from_hex(
            "027682d2f7b05c3801fe4467883ab4cff0568b5e36412b5289e83ea5b519de8a01",
        )
        .unwrap();
        let privk_sponsor = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();

        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_sponsor = TransactionAuth::from_p2pkh(&privk_sponsor).unwrap();

        let auth_contract_call = auth_origin.into_sponsored(auth_sponsor).unwrap();

        let addr_origin = auth_contract_call.origin().address_testnet();
        let addr_sponsor = auth_contract_call.sponsor().unwrap().address_testnet();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_contract_call.clone(),
            TransactionPayload::new_contract_call(
                addr_publisher.clone(),
                "hello-world",
                "set-bar",
                vec![Value::Int(6), Value::Int(2)],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);

        let mut signer_2 = StacksTransactionSigner::new(&tx_contract_call);
        signer_2.sign_origin(&privk_origin).unwrap();
        signer_2.sign_sponsor(&privk_sponsor).unwrap();

        let signed_tx_2 = signer_2.get_tx().unwrap();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            // process both
            let account_publisher =
                StacksChainState::get_account(&mut conn, &addr_publisher.to_account_principal());
            assert_eq!(account_publisher.nonce, 0);

            let account_origin =
                StacksChainState::get_account(&mut conn, &addr_origin.to_account_principal());
            assert_eq!(account_origin.nonce, 0);

            let account_sponsor =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            assert_eq!(account_sponsor.nonce, 0);

            let contract_id = QualifiedContractIdentifier::new(
                StandardPrincipalData::from(addr_publisher.clone()),
                ContractName::from("hello-world"),
            );
            let contract_before_res =
                StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            assert!(contract_before_res.is_none());

            let var_before_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
            assert!(var_before_res.is_none());

            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account_publisher =
                StacksChainState::get_account(&mut conn, &addr_publisher.to_account_principal());
            assert_eq!(account_publisher.nonce, 1);

            let var_before_set_res =
                StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();
            assert_eq!(var_before_set_res, Some(Value::Int(0)));

            let (fee_2, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_2,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let account_origin =
                StacksChainState::get_account(&mut conn, &addr_origin.to_account_principal());
            assert_eq!(account_origin.nonce, 1);

            let account_sponsor =
                StacksChainState::get_account(&mut conn, &addr_sponsor.to_account_principal());
            assert_eq!(account_sponsor.nonce, 1);

            let contract_res = StacksChainState::get_contract(&mut conn, &contract_id).unwrap();
            let var_res = StacksChainState::get_data_var(&mut conn, &contract_id, "bar").unwrap();

            conn.commit_block();

            assert_eq!(fee, 0);
            assert_eq!(fee_2, 0);
            assert!(contract_res.is_some());
            assert!(var_res.is_some());
            assert_eq!(var_res, Some(Value::Int(3)));
        }
    }

    #[test]
    fn process_post_conditions_tokens() {
        let contract = "
        (define-data-var bar int 0)
        (define-fungible-token stackaroos)
        (define-non-fungible-token names (buff 50))
        (define-public (send-stackaroos (recipient principal))
          (begin
             (as-contract  ;; used to test post-conditions on contract principal
               (begin (unwrap-panic (ft-mint? stackaroos u100 tx-sender))
                      (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
                      (ok true))
             )
           )
        )
        (define-public (send-name (name (buff 50)) (recipient principal))
          (begin
            (as-contract   ;; used to test post-conditions on contract principal
              (begin (unwrap-panic (nft-mint? names name tx-sender))
                     (unwrap-panic (nft-transfer? names name tx-sender recipient))
                     (ok true))
            )
          )
        )
        (define-public (user-send-stackaroos (recipient principal))
          (begin
             (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
             (ok true))
        )
        (define-public (user-send-name (name (buff 50)) (recipient principal))
          (begin
             (unwrap-panic (nft-transfer? names name tx-sender recipient))
             (ok true))
        )
        (define-public (send-stackaroos-and-name (name (buff 50)) (recipient principal))
          (begin
             (as-contract  ;; used to test post-conditions on contract principal
               (begin (unwrap-panic (nft-mint? names name tx-sender))
                      (unwrap-panic (nft-transfer? names name tx-sender recipient))
                      (unwrap-panic (ft-mint? stackaroos u100 tx-sender))
                      (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
                      (ok true))
             )
          )
        )
        (define-public (user-send-stackaroos-and-name (name (buff 50)) (recipient principal))
           (begin
             (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
             (unwrap-panic (nft-transfer? names name tx-sender recipient))
             (ok true))
        )
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let privk_origin = StacksPrivateKey::from_hex(
            "027682d2f7b05c3801fe4467883ab4cff0568b5e36412b5289e83ea5b519de8a01",
        )
        .unwrap();
        let privk_recipient = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();
        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_recv = TransactionAuth::from_p2pkh(&privk_recipient).unwrap();
        let addr_publisher = auth_origin.origin().address_testnet();
        let addr_principal = addr_publisher.to_account_principal();

        let contract_name = ContractName::try_from("hello-world").unwrap();

        let recv_addr = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk_recipient)],
        )
        .unwrap();
        let recv_principal = recv_addr.to_account_principal();
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr_publisher.clone()),
            contract_name.clone(),
        );
        let _contract_principal = PrincipalData::Contract(contract_id.clone());

        let asset_info = AssetInfo {
            contract_address: addr_publisher.clone(),
            contract_name: contract_name.clone(),
            asset_name: ClarityName::try_from("stackaroos").unwrap(),
        };

        let name_asset_info = AssetInfo {
            contract_address: addr_publisher.clone(),
            contract_name: contract_name.clone(),
            asset_name: ClarityName::try_from("names").unwrap(),
        };

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_origin.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk_origin).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        let mut post_conditions_pass = vec![];
        let mut post_conditions_pass_payback = vec![];
        let mut post_conditions_pass_nft = vec![];
        let mut post_conditions_fail = vec![];
        let mut post_conditions_fail_payback = vec![];
        let mut post_conditions_fail_nft = vec![];
        let mut nonce = 1;
        let mut recv_nonce = 0;
        let mut next_name: u64 = 0;

        let mut tx_contract_call_stackaroos = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_origin.clone(),
            TransactionPayload::new_contract_call(
                addr_publisher.clone(),
                "hello-world",
                "send-stackaroos",
                vec![Value::Principal(recv_principal.clone())],
            )
            .unwrap(),
        );

        tx_contract_call_stackaroos.chain_id = 0x80000000;
        tx_contract_call_stackaroos.set_tx_fee(0);

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent ==, <=, or >= 100 stackaroos
        for pass_condition in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *pass_condition,
                100,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent >= or > 99 stackaroos
        for pass_condition in [FungibleConditionCode::SentGe, FungibleConditionCode::SentGt].iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *pass_condition,
                99,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent <= or < 101 stackaroos
        for pass_condition in [FungibleConditionCode::SentLe, FungibleConditionCode::SentLt].iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *pass_condition,
                101,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // give recv_addr 100 more stackaroos so we can test failure-to-send-back
        {
            let mut tx_contract_call_pass = tx_contract_call_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                FungibleConditionCode::SentEq,
                100,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        let mut tx_contract_call_user_stackaroos = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_recv.clone(),
            TransactionPayload::new_contract_call(
                addr_publisher.clone(),
                "hello-world",
                "user-send-stackaroos",
                vec![Value::Principal(addr_principal.clone())],
            )
            .unwrap(),
        );

        tx_contract_call_user_stackaroos.chain_id = 0x80000000;
        tx_contract_call_user_stackaroos.set_tx_fee(0);

        // recv_addr sends 100 stackaroos back to addr_publisher.
        // assert recv_addr sent ==, <=, or >= 100 stackaroos
        for pass_condition in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_user_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(recv_nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *pass_condition,
                100,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_pass_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // recv_addr sends 100 stackaroos back to addr_publisher.
        // assert recv_addr sent >= or > 99 stackaroos
        for pass_condition in [FungibleConditionCode::SentGe, FungibleConditionCode::SentGt].iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_user_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(recv_nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *pass_condition,
                99,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_pass_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // recv_addr sends 100 stackaroos back to addr_publisher
        // assert recv_addr sent <= or < 101 stackaroos
        for pass_condition in [FungibleConditionCode::SentLe, FungibleConditionCode::SentLt].iter()
        {
            let mut tx_contract_call_pass = tx_contract_call_user_stackaroos.clone();
            tx_contract_call_pass.set_origin_nonce(recv_nonce);
            tx_contract_call_pass.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *pass_condition,
                101,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_pass);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_pass_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // mint names to recv_addr, and set a post-condition on the contract-principal to check it.
        // assert contract does not possess the name
        for (_i, pass_condition) in [NonfungibleConditionCode::Sent].iter().enumerate() {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_names = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_names.chain_id = 0x80000000;
            tx_contract_call_names.set_tx_fee(0);
            tx_contract_call_names.set_origin_nonce(nonce);

            tx_contract_call_names.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                name_asset_info.clone(),
                name.clone(),
                *pass_condition,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_names);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass_nft.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent < or > 100 stackaroos (should fail)
        for fail_condition in [FungibleConditionCode::SentLt, FungibleConditionCode::SentGt].iter()
        {
            let mut tx_contract_call_fail = tx_contract_call_stackaroos.clone();
            tx_contract_call_fail.set_origin_nonce(nonce);
            tx_contract_call_fail.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *fail_condition,
                100,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_fail);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent <= or < 99 stackaroos (should fail)
        for fail_condition in [FungibleConditionCode::SentLe, FungibleConditionCode::SentLt].iter()
        {
            let mut tx_contract_call_fail = tx_contract_call_stackaroos.clone();
            tx_contract_call_fail.set_origin_nonce(nonce);
            tx_contract_call_fail.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *fail_condition,
                99,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_fail);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos to recv_addr, and set a post-condition on the contract-principal
        // to check it.
        // assert contract sent > or >= 101 stackaroos (should fail)
        for fail_condition in [FungibleConditionCode::SentGe, FungibleConditionCode::SentGt].iter()
        {
            let mut tx_contract_call_fail = tx_contract_call_stackaroos.clone();
            tx_contract_call_fail.set_origin_nonce(nonce);
            tx_contract_call_fail.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *fail_condition,
                101,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_fail);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // recv_addr tries sends 100 stackaroos back to addr_publisher
        // assert recv_addr sent < or > 100 stackaroos (should fail)
        for fail_condition in [FungibleConditionCode::SentLt, FungibleConditionCode::SentLt].iter()
        {
            let mut tx_contract_call_fail = tx_contract_call_user_stackaroos.clone();
            tx_contract_call_fail.set_origin_nonce(recv_nonce);
            tx_contract_call_fail.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *fail_condition,
                100,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_fail);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_fail_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // mint names to recv_addr, and set a post-condition on the contract-principal to check it.
        // assert contract still possesses the name (should fail)
        for (_i, fail_condition) in [NonfungibleConditionCode::NotSent].iter().enumerate() {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_names = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_names.chain_id = 0x80000000;
            tx_contract_call_names.set_tx_fee(0);
            tx_contract_call_names.set_origin_nonce(nonce);

            tx_contract_call_names.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                name_asset_info.clone(),
                name.clone(),
                *fail_condition,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_names);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail_nft.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            // make sure costs-3 is instantiated, so as-contract works in 2.1
            let mut conn = chainstate.test_genesis_block_begin_2_1(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let account_publisher =
                StacksChainState::get_account(&mut conn, &addr_publisher.to_account_principal());
            assert_eq!(account_publisher.nonce, 0);

            // no initial stackaroos balance -- there is no stackaroos token (yet)
            let _ = StacksChainState::get_account_ft(
                &mut conn,
                &contract_id,
                "stackaroos",
                &recv_principal,
            )
            .unwrap_err();

            // publish contract
            let _ = StacksChainState::process_transaction(
                &mut conn,
                &signed_contract_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // no initial stackaroos balance
            let account_stackaroos_balance = StacksChainState::get_account_ft(
                &mut conn,
                &contract_id,
                "stackaroos",
                &recv_principal,
            )
            .unwrap();
            assert_eq!(account_stackaroos_balance, 0);

            let mut expected_stackaroos_balance = 0;
            let mut expected_nonce = 1;
            let mut expected_recv_nonce = 0;
            let mut expected_payback_stackaroos_balance = 0;
            let mut expected_next_name: u64 = 0;

            for tx_pass in post_conditions_pass.iter() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_pass,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_stackaroos_balance += 100;
                expected_nonce += 1;

                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            for tx_pass in post_conditions_pass_payback.iter() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_pass,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_stackaroos_balance -= 100;
                expected_payback_stackaroos_balance += 100;
                expected_recv_nonce += 1;

                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);

                let account_recv_publisher_after =
                    StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
                assert_eq!(account_recv_publisher_after.nonce, expected_recv_nonce);
            }

            for (_i, tx_pass) in post_conditions_pass_nft.iter().enumerate() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_pass,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_nonce += 1;

                let expected_value =
                    Value::buff_from(expected_next_name.to_be_bytes().to_vec()).unwrap();
                expected_next_name += 1;

                let account_recipient_names_after = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                )
                .unwrap();
                assert_eq!(account_recipient_names_after, recv_principal);

                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            for tx_fail in post_conditions_fail.iter() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_fail,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_nonce += 1;

                // no change in balance
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                // but nonce _does_ change
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            for tx_fail in post_conditions_fail_payback.iter() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_fail,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_recv_nonce += 1;

                // no change in balance
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                // nonce for publisher doesn't change
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);

                // but nonce _does_ change for reciever, who sent back
                let account_publisher_after =
                    StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
                assert_eq!(account_publisher_after.nonce, expected_recv_nonce);
            }

            for (_i, tx_fail) in post_conditions_fail_nft.iter().enumerate() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_fail,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_nonce += 1;

                // nft shouldn't exist -- the nft-mint! should have been rolled back
                let expected_value =
                    Value::buff_from(expected_next_name.to_be_bytes().to_vec()).unwrap();
                expected_next_name += 1;

                let res = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                );
                assert!(res.is_err());

                // but nonce _does_ change
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            conn.commit_block();
        }
    }

    #[test]
    fn process_post_conditions_tokens_deny() {
        let contract = "
        (define-data-var bar int 0)
        (define-fungible-token stackaroos)
        (define-non-fungible-token names (buff 50))
        (define-public (send-stackaroos (recipient principal))
          (begin
             (as-contract  ;; used to test post-conditions on contract principal
               (begin (unwrap-panic (ft-mint? stackaroos u100 tx-sender))
                      (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
                      (ok true))
             )
           )
        )
        (define-public (send-name (name (buff 50)) (recipient principal))
          (begin
            (as-contract   ;; used to test post-conditions on contract principal
              (begin (unwrap-panic (nft-mint? names name tx-sender))
                     (unwrap-panic (nft-transfer? names name tx-sender recipient))
                     (ok true))
            )
          )
        )
        (define-public (user-send-stackaroos (recipient principal))
          (begin
             (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
             (ok true))
        )
        (define-public (user-send-name (name (buff 50)) (recipient principal))
          (begin
             (unwrap-panic (nft-transfer? names name tx-sender recipient))
             (ok true))
        )
        (define-public (send-stackaroos-and-name (name (buff 50)) (recipient principal))
          (begin
             (as-contract  ;; used to test post-conditions on contract principal
               (begin (unwrap-panic (nft-mint? names name tx-sender))
                      (unwrap-panic (nft-transfer? names name tx-sender recipient))
                      (unwrap-panic (ft-mint? stackaroos u100 tx-sender))
                      (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
                      (ok true))
             )
          )
        )
        (define-public (user-send-stackaroos-and-name (name (buff 50)) (recipient principal))
           (begin
             (unwrap-panic (ft-transfer? stackaroos u100 tx-sender recipient))
             (unwrap-panic (nft-transfer? names name tx-sender recipient))
             (ok true))
        )
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))";

        let privk_origin = StacksPrivateKey::from_hex(
            "027682d2f7b05c3801fe4467883ab4cff0568b5e36412b5289e83ea5b519de8a01",
        )
        .unwrap();
        let privk_recipient = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();
        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_recv = TransactionAuth::from_p2pkh(&privk_recipient).unwrap();
        let addr_publisher = auth_origin.origin().address_testnet();
        let addr_principal = addr_publisher.to_account_principal();

        let contract_name = ContractName::try_from("hello-world").unwrap();

        let recv_addr = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk_recipient)],
        )
        .unwrap();
        let recv_principal = recv_addr.to_account_principal();
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr_publisher.clone()),
            contract_name.clone(),
        );
        let _contract_principal = PrincipalData::Contract(contract_id.clone());

        let asset_info = AssetInfo {
            contract_address: addr_publisher.clone(),
            contract_name: contract_name.clone(),
            asset_name: ClarityName::try_from("stackaroos").unwrap(),
        };

        let name_asset_info = AssetInfo {
            contract_address: addr_publisher.clone(),
            contract_name: contract_name.clone(),
            asset_name: ClarityName::try_from("names").unwrap(),
        };

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_origin.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk_origin).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        let mut post_conditions_pass = vec![];
        let mut post_conditions_pass_payback = vec![];
        let mut post_conditions_fail = vec![];
        let mut post_conditions_fail_payback = vec![];
        let mut nonce = 1;
        let mut recv_nonce = 0;
        let mut next_name: u64 = 0;
        let mut next_recv_name: u64 = 0;
        let final_recv_name = 3;

        // mint 100 stackaroos and the name to recv_addr, and set a post-condition for each asset on the contract-principal
        // assert contract sent ==, <=, or >= 100 stackaroos
        for (_i, pass_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *pass_condition,
                100,
            ));
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                name_asset_info.clone(),
                name.clone(),
                NonfungibleConditionCode::Sent,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // give recv_addr 100 more stackaroos so we can test failure-to-send-back
        {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Allow;
            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(nonce);

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_pass.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        assert_eq!(next_name, final_recv_name + 1);

        // recv_addr sends 100 stackaroos and name back to addr_publisher.
        // assert recv_addr sent ==, <=, or >= 100 stackaroos
        for (_i, pass_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(next_recv_name.to_be_bytes().to_vec()).unwrap();
            next_recv_name += 1;

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_recv.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "user-send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(addr_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(recv_nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *pass_condition,
                100,
            ));
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                name_asset_info.clone(),
                name.clone(),
                NonfungibleConditionCode::Sent,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_pass_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // mint 100 stackaroos and the name to recv_addr, but neglect to set a fungible post-condition.
        // assert contract sent ==, <=, or >= 100 stackaroos, and that the name was removed from
        // the contract
        for (_i, fail_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            // tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()), asset_info.clone(), *fail_condition, 100));
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                name_asset_info.clone(),
                name.clone(),
                NonfungibleConditionCode::Sent,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // mint 100 stackaroos and the name to recv_addr, but neglect to set a non-fungible post-condition.
        // assert contract sent ==, <=, or >= 100 stackaroos, and that the name was removed from
        // the contract
        for (_i, fail_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(next_name.to_be_bytes().to_vec()).unwrap();
            next_name += 1;

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_origin.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(recv_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()),
                asset_info.clone(),
                *fail_condition,
                100,
            ));
            // tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(PostConditionPrincipal::Contract(addr_publisher.clone(), contract_name.clone()), name_asset_info.clone(), name.clone(), NonfungibleConditionCode::Sent));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_origin).unwrap();
            post_conditions_fail.push(signer.get_tx().unwrap());

            nonce += 1;
        }

        // recv_addr sends 100 stackaroos and name back to addr_publisher, but forgets a fungible
        // post-condition.
        // assert recv_addr sent ==, <=, or >= 100 stackaroos
        for (_i, fail_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(final_recv_name.to_be_bytes().to_vec()).unwrap();

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_recv.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "user-send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(addr_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(recv_nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            // tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(PostConditionPrincipal::Standard(recv_addr.clone()), asset_info.clone(), *fail_condition, 100));
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                name_asset_info.clone(),
                name.clone(),
                NonfungibleConditionCode::Sent,
            ));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_fail_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        // never read: next_recv_name -= 3;    // reset

        // recv_addr sends 100 stackaroos and name back to addr_publisher, but forgets a non-fungible
        // post-condition.
        // assert recv_addr sent ==, <=, or >= 100 stackaroos
        for (_i, fail_condition) in [
            FungibleConditionCode::SentEq,
            FungibleConditionCode::SentGe,
            FungibleConditionCode::SentLe,
        ]
        .iter()
        .enumerate()
        {
            let name = Value::buff_from(final_recv_name.to_be_bytes().to_vec()).unwrap();

            let mut tx_contract_call_both = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth_recv.clone(),
                TransactionPayload::new_contract_call(
                    addr_publisher.clone(),
                    "hello-world",
                    "user-send-stackaroos-and-name",
                    vec![name.clone(), Value::Principal(addr_principal.clone())],
                )
                .unwrap(),
            );

            tx_contract_call_both.chain_id = 0x80000000;
            tx_contract_call_both.set_tx_fee(0);
            tx_contract_call_both.set_origin_nonce(recv_nonce);

            tx_contract_call_both.post_condition_mode = TransactionPostConditionMode::Deny;
            tx_contract_call_both.add_post_condition(TransactionPostCondition::Fungible(
                PostConditionPrincipal::Standard(recv_addr.clone()),
                asset_info.clone(),
                *fail_condition,
                100,
            ));
            // tx_contract_call_both.add_post_condition(TransactionPostCondition::Nonfungible(PostConditionPrincipal::Standard(recv_addr.clone()), name_asset_info.clone(), name.clone(), NonfungibleConditionCode::Sent));

            let mut signer = StacksTransactionSigner::new(&tx_contract_call_both);
            signer.sign_origin(&privk_recipient).unwrap();
            post_conditions_fail_payback.push(signer.get_tx().unwrap());

            recv_nonce += 1;
        }

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            // make sure costs-3 is installed so as-contract will work in epoch 2.1
            let mut conn = chainstate.test_genesis_block_begin_2_1(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            let account_publisher =
                StacksChainState::get_account(&mut conn, &addr_publisher.to_account_principal());
            assert_eq!(account_publisher.nonce, 0);

            // no initial stackaroos balance -- there is no stackaroos token (yet)
            let _ = StacksChainState::get_account_ft(
                &mut conn,
                &contract_id,
                "stackaroos",
                &recv_principal,
            )
            .unwrap_err();

            // publish contract
            let _ = StacksChainState::process_transaction(
                &mut conn,
                &signed_contract_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // no initial stackaroos balance
            let account_stackaroos_balance = StacksChainState::get_account_ft(
                &mut conn,
                &contract_id,
                "stackaroos",
                &recv_principal,
            )
            .unwrap();
            assert_eq!(account_stackaroos_balance, 0);

            let mut expected_stackaroos_balance = 0;
            let mut expected_nonce = 1;
            let mut expected_recv_nonce = 0;
            let mut expected_payback_stackaroos_balance = 0;

            for (_i, tx_pass) in post_conditions_pass.iter().enumerate() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_pass,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_stackaroos_balance += 100;
                expected_nonce += 1;

                // should have gotten stackaroos
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                // should have gotten name we created here
                let expected_value = match tx_pass.payload {
                    TransactionPayload::ContractCall(ref cc) => cc.function_args[0].clone(),
                    _ => panic!("Not a contract call"),
                };

                let account_recipient_names_after = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                )
                .unwrap();
                assert_eq!(account_recipient_names_after, recv_principal);

                // sender's nonce increased
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            for (_i, tx_pass) in post_conditions_pass_payback.iter().enumerate() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_pass,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_stackaroos_balance -= 100;
                expected_payback_stackaroos_balance += 100;
                expected_recv_nonce += 1;

                // recipient should have sent stackaroos
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                // publisher should have gotten them
                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                // should have gotten name we created here
                let expected_value = match tx_pass.payload {
                    TransactionPayload::ContractCall(ref cc) => cc.function_args[0].clone(),
                    _ => panic!("Not a contract call"),
                };

                let account_publisher_names_after = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                )
                .unwrap();
                assert_eq!(account_publisher_names_after, addr_principal);

                // no change in nonce
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);

                // receiver nonce changed
                let account_recv_publisher_after =
                    StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
                assert_eq!(account_recv_publisher_after.nonce, expected_recv_nonce);
            }

            for (_i, tx_fail) in post_conditions_fail.iter().enumerate() {
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_fail,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_nonce += 1;

                // no change in balance
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                // new names the transaction tried to create don't exist -- transaction was aborted
                let expected_value = match tx_fail.payload {
                    TransactionPayload::ContractCall(ref cc) => cc.function_args[0].clone(),
                    _ => panic!("Not a contract call"),
                };

                let res = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                );
                assert!(res.is_err());

                // but nonce _does_ change
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);
            }

            for (_i, tx_fail) in post_conditions_fail_payback.iter().enumerate() {
                eprintln!("tx fail {:?}", &tx_fail);
                let (_fee, _) = StacksChainState::process_transaction(
                    &mut conn,
                    &tx_fail,
                    false,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
                expected_recv_nonce += 1;

                // no change in balance
                let account_recipient_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &recv_principal,
                )
                .unwrap();
                assert_eq!(
                    account_recipient_stackaroos_after,
                    expected_stackaroos_balance
                );

                let account_pub_stackaroos_after = StacksChainState::get_account_ft(
                    &mut conn,
                    &contract_id,
                    "stackaroos",
                    &addr_principal,
                )
                .unwrap();
                assert_eq!(
                    account_pub_stackaroos_after,
                    expected_payback_stackaroos_balance
                );

                // name we tried to send back is still owned by recv_addr
                let expected_value = match tx_fail.payload {
                    TransactionPayload::ContractCall(ref cc) => cc.function_args[0].clone(),
                    _ => panic!("Not a contract call"),
                };

                // name remains owned by recv_addr
                let res = StacksChainState::get_account_nft(
                    &mut conn,
                    &contract_id,
                    "names",
                    &expected_value,
                );
                assert!(res.is_ok());
                assert_eq!(res.unwrap(), recv_principal);

                // nonce for publisher doesn't change
                let account_publisher_after = StacksChainState::get_account(
                    &mut conn,
                    &addr_publisher.to_account_principal(),
                );
                assert_eq!(account_publisher_after.nonce, expected_nonce);

                // but nonce _does_ change for reciever, who sent back
                let account_publisher_after =
                    StacksChainState::get_account(&mut conn, &recv_addr.to_account_principal());
                assert_eq!(account_publisher_after.nonce, expected_recv_nonce);
            }

            conn.commit_block();
        }
    }

    #[test]
    fn process_post_conditions_tokens_deny_2097() {
        let privk_origin = StacksPrivateKey::from_hex(
            "027682d2f7b05c3801fe4467883ab4cff0568b5e36412b5289e83ea5b519de8a01",
        )
        .unwrap();
        let privk_recipient = StacksPrivateKey::from_hex(
            "7e3af4db6af6b3c67e2c6c6d7d5983b519f4d9b3a6e00580ae96dcace3bde8bc01",
        )
        .unwrap();
        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let auth_recv = TransactionAuth::from_p2pkh(&privk_recipient).unwrap();
        let addr_publisher = auth_origin.origin().address_testnet();
        let addr_principal = addr_publisher.to_account_principal();

        let contract = "
(define-constant owner 'ST3X2W2SH9XQZRHHYJ21KWGTT1N6WX3D48K1NSTPE)
(define-fungible-token connect-token)
(begin (ft-mint? connect-token u100000000 owner))
(define-public (transfer (recipient principal) (amount uint))
  (ok (ft-transfer? connect-token amount tx-sender recipient)))
"
        .to_string();

        let contract_name = ContractName::try_from("hello-world").unwrap();

        let recv_addr = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk_recipient)],
        )
        .unwrap();
        let recv_principal = recv_addr.to_account_principal();
        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr_publisher.clone()),
            contract_name.clone(),
        );
        let _contract_principal = PrincipalData::Contract(contract_id.clone());

        let asset_info = AssetInfo {
            contract_address: addr_publisher.clone(),
            contract_name: contract_name.clone(),
            asset_name: ClarityName::try_from("connect-token").unwrap(),
        };

        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_origin.clone(),
            TransactionPayload::new_smart_contract(&"hello-world".to_string(), &contract, None)
                .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract);
        signer.sign_origin(&privk_origin).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_origin.clone(),
            TransactionPayload::new_contract_call(
                addr_publisher.clone(),
                "hello-world",
                "transfer",
                vec![Value::Principal(recv_principal.clone()), Value::UInt(10)],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(0);
        tx_contract_call.set_origin_nonce(1);

        tx_contract_call.post_condition_mode = TransactionPostConditionMode::Deny;
        tx_contract_call.add_post_condition(TransactionPostCondition::Fungible(
            PostConditionPrincipal::Origin,
            asset_info.clone(),
            FungibleConditionCode::SentEq,
            10,
        ));

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk_origin).unwrap();
        let contract_call_tx = signer.get_tx().unwrap();

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());
        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            // publish contract
            let _ = StacksChainState::process_transaction(
                &mut conn,
                &signed_contract_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            let (_fee, receipt) = StacksChainState::process_transaction(
                &mut conn,
                &contract_call_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            assert_eq!(receipt.post_condition_aborted, true);
            assert_eq!(receipt.result.to_string(), "(ok (err u1))");

            conn.commit_block();
        }
    }

    fn make_account(principal: &PrincipalData, nonce: u64, balance: u128) -> StacksAccount {
        let stx_balance = STXBalance::initial(balance);
        StacksAccount {
            principal: principal.clone(),
            nonce,
            stx_balance,
        }
    }

    #[test]
    fn test_check_postconditions_multiple_fts() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let origin = addr.to_account_principal();
        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };
        let contract_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0x01; 20]),
        };

        let asset_info_1 = AssetInfo {
            contract_address: contract_addr.clone(),
            contract_name: ContractName::try_from("hello-world").unwrap(),
            asset_name: ClarityName::try_from("test-asset-1").unwrap(),
        };

        let asset_info_2 = AssetInfo {
            contract_address: contract_addr.clone(),
            contract_name: ContractName::try_from("hello-world").unwrap(),
            asset_name: ClarityName::try_from("test-asset-2").unwrap(),
        };

        let asset_info_3 = AssetInfo {
            contract_address: contract_addr.clone(),
            contract_name: ContractName::try_from("hello-world").unwrap(),
            asset_name: ClarityName::try_from("test-asset-3").unwrap(),
        };

        let asset_id_1 = AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData::from(asset_info_1.contract_address),
                asset_info_1.contract_name.clone(),
            ),
            asset_name: asset_info_1.asset_name.clone(),
        };

        let asset_id_2 = AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData::from(asset_info_2.contract_address),
                asset_info_2.contract_name.clone(),
            ),
            asset_name: asset_info_2.asset_name.clone(),
        };

        let _asset_id_3 = AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData::from(asset_info_3.contract_address),
                asset_info_3.contract_name.clone(),
            ),
            asset_name: asset_info_3.asset_name.clone(),
        };

        // multi-ft
        let mut ft_transfer_2 = AssetMap::new();
        ft_transfer_2
            .add_token_transfer(&origin, asset_id_1.clone(), 123)
            .unwrap();
        ft_transfer_2
            .add_token_transfer(&origin, asset_id_2.clone(), 123)
            .unwrap();

        let tests = vec![
            // no-postconditions in allow mode
            (
                true,
                vec![],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // three post-conditions on origin in allow mode, one with sending 0 tokens
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // four post-conditions on origin in allow mode, one with sending 0 tokens, one with
            // an unchecked address and a vacuous amount
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode, explicit origin
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // three post-conditions on origin in allow mode, one with sending 0 tokens, explicit
            // origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // four post-conditions on origin in allow mode, one with sending 0 tokens, one with
            // an unchecked address and a vacuous amount, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // no-postconditions in deny mode
            (
                false,
                vec![],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Origin,
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // three post-conditions on origin in allow mode, one with sending 0 tokens
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // four post-conditions on origin in allow mode, one with sending 0 tokens, one with
            // an unchecked address and a vacuous amount
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Origin,
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode, explicit origin
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Fungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info_1.clone(),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // three post-conditions on origin in allow mode, one with sending 0 tokens, explicit
            // origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // four post-conditions on origin in allow mode, one with sending 0 tokens, one with
            // an unchecked address and a vacuous amount, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_3.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(recv_addr.clone()),
                        asset_info_1.clone(),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::Fungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info_2.clone(),
                        FungibleConditionCode::SentGt,
                        122,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
        ];

        for test in tests {
            let expected_result = test.0;
            let post_conditions = &test.1;
            let mode = &test.2;
            let origin = &test.3;

            let result = StacksChainState::check_transaction_postconditions(
                post_conditions,
                mode,
                origin,
                &ft_transfer_2,
                Txid([0; 32]),
            )
            .unwrap();
            if result != expected_result {
                eprintln!(
                    "test failed:\nasset map: {:?}\nscenario: {:?}\n",
                    &ft_transfer_2, &test
                );
                assert!(false);
            }
        }
    }

    #[test]
    fn test_check_postconditions_multiple_nfts() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let origin = addr.to_account_principal();
        let _recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };
        let contract_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0x01; 20]),
        };

        let asset_info = AssetInfo {
            contract_address: contract_addr.clone(),
            contract_name: ContractName::try_from("hello-world").unwrap(),
            asset_name: ClarityName::try_from("test-asset").unwrap(),
        };

        let asset_id = AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData::from(asset_info.contract_address),
                asset_info.contract_name.clone(),
            ),
            asset_name: asset_info.asset_name.clone(),
        };

        // multi-nft transfer
        let mut nft_transfer_2 = AssetMap::new();
        nft_transfer_2.add_asset_transfer(&origin, asset_id.clone(), Value::Int(1));
        nft_transfer_2.add_asset_transfer(&origin, asset_id.clone(), Value::Int(2));

        let tests = vec![
            // no post-conditions in allow mode
            (
                true,
                vec![],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode
            (
                true,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Origin,
                    asset_info.clone(),
                    Value::Int(1),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Origin,
                    asset_info.clone(),
                    Value::Int(2),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // post-condition on a non-sent asset
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(3),
                        NonfungibleConditionCode::NotSent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in allow mode, explicit origin
            (
                true,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info.clone(),
                    Value::Int(1),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            (
                true,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info.clone(),
                    Value::Int(2),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // post-condition on a non-sent asset, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(3),
                        NonfungibleConditionCode::NotSent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // no post-conditions in deny mode
            (
                false,
                vec![],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in deny mode
            (
                false,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Origin,
                    asset_info.clone(),
                    Value::Int(1),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Origin,
                    asset_info.clone(),
                    Value::Int(2),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // post-condition on a non-sent asset
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Origin,
                        asset_info.clone(),
                        Value::Int(3),
                        NonfungibleConditionCode::NotSent,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // one post-condition on origin in deny mode, explicit origin
            (
                false,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info.clone(),
                    Value::Int(1),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            (
                false,
                vec![TransactionPostCondition::Nonfungible(
                    PostConditionPrincipal::Standard(addr.clone()),
                    asset_info.clone(),
                    Value::Int(2),
                    NonfungibleConditionCode::Sent,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
            // two post-conditions on origin in allow mode, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ),
            // post-condition on a non-sent asset, explicit origin
            (
                true,
                vec![
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(1),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(2),
                        NonfungibleConditionCode::Sent,
                    ),
                    TransactionPostCondition::Nonfungible(
                        PostConditionPrincipal::Standard(addr.clone()),
                        asset_info.clone(),
                        Value::Int(3),
                        NonfungibleConditionCode::NotSent,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ),
        ];

        for test in tests.iter() {
            let expected_result = test.0;
            let post_conditions = &test.1;
            let mode = &test.2;
            let origin = &test.3;

            let result = StacksChainState::check_transaction_postconditions(
                post_conditions,
                mode,
                origin,
                &nft_transfer_2,
                Txid([0; 32]),
            )
            .unwrap();
            if result != expected_result {
                eprintln!(
                    "test failed:\nasset map: {:?}\nscenario: {:?}\n",
                    &nft_transfer_2, &test
                );
                assert!(false);
            }
        }
    }

    #[test]
    fn test_check_postconditions_stx() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let origin = addr.to_account_principal();
        let _recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        // stx-transfer for 123 microstx
        let mut stx_asset_map = AssetMap::new();
        stx_asset_map.add_stx_transfer(&origin, 123).unwrap();

        // stx-burn for 123 microstx
        let mut stx_burn_asset_map = AssetMap::new();
        stx_burn_asset_map.add_stx_burn(&origin, 123).unwrap();

        // stx-transfer and stx-burn for a total of 123 microstx
        let mut stx_transfer_burn_asset_map = AssetMap::new();
        stx_transfer_burn_asset_map
            .add_stx_transfer(&origin, 100)
            .unwrap();
        stx_transfer_burn_asset_map
            .add_stx_burn(&origin, 23)
            .unwrap();

        let tests = vec![
            // no post-conditions in allow mode
            (
                true,
                vec![],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions on origin in allow mode
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions with an explicitly-set address in allow mode
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions with an unrelated contract address in allow mode
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentEq,
                    0,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentLe,
                    0,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentGe,
                    0,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentLt,
                    1,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions with both the origin and an unrelated contract address in allow mode
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions that fail since the amount is wrong
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentEq,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLe,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGe,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLt,
                    122,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGt,
                    124,
                )],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            // no post-conditions in deny mode (should fail)
            (
                false,
                vec![],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            // post-conditions on origin in deny mode (should all pass since origin is specified
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions with an explicitly-set address in deny mode (should all pass since
            // address matches the address in the asset map)
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentEq,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentLe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentGe,
                    123,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentLt,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Standard(addr.clone()),
                    FungibleConditionCode::SentGt,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions with an unrelated contract address in allow mode, with check on
            // origin (should all pass)
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Allow,
                make_account(&origin, 1, 123),
            ), // should fail
            // post-conditions with an unrelated contract address in deny mode (should all fail
            // since stx-transfer isn't covered)
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentEq,
                    0,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentLe,
                    0,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentGe,
                    0,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Contract(
                        addr.clone(),
                        ContractName::try_from("hello-world").unwrap(),
                    ),
                    FungibleConditionCode::SentLt,
                    1,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            // post-conditions with an unrelated contract address in deny mode, with check on
            // origin (should all pass)
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            // post-conditions with both the origin and an unrelated contract address in deny mode (should all pass)
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentEq,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentEq,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentLe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentGe,
                        0,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentGe,
                        123,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            (
                true,
                vec![
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Contract(
                            addr.clone(),
                            ContractName::try_from("hello-world").unwrap(),
                        ),
                        FungibleConditionCode::SentLt,
                        1,
                    ),
                    TransactionPostCondition::STX(
                        PostConditionPrincipal::Origin,
                        FungibleConditionCode::SentLt,
                        124,
                    ),
                ],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should pass
            // post-conditions that fail since the amount is wrong, even though all principals are
            // covered
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentEq,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLe,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGe,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentLt,
                    122,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
            (
                false,
                vec![TransactionPostCondition::STX(
                    PostConditionPrincipal::Origin,
                    FungibleConditionCode::SentGt,
                    124,
                )],
                TransactionPostConditionMode::Deny,
                make_account(&origin, 1, 123),
            ), // should fail
        ];

        for asset_map in &[
            &stx_asset_map,
            &stx_burn_asset_map,
            &stx_transfer_burn_asset_map,
        ] {
            for test in tests.iter() {
                let expected_result = test.0;
                let post_conditions = &test.1;
                let post_condition_mode = &test.2;
                let origin_account = &test.3;

                let result = StacksChainState::check_transaction_postconditions(
                    post_conditions,
                    post_condition_mode,
                    origin_account,
                    asset_map,
                    Txid([0; 32]),
                )
                .unwrap();
                if result != expected_result {
                    eprintln!(
                        "test failed:\nasset map: {:?}\nscenario: {:?}\n",
                        asset_map, &test
                    );
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn process_smart_contract_fee_check() {
        let contract = r#"
        (define-public (send-stx (amount uint) (recipient principal))
            (stx-transfer? amount tx-sender recipient))
        "#;

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_contract_create = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"hello-world".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_create.chain_id = 0x80000000;
        tx_contract_create.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_create);
        signer.sign_origin(&privk).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "hello-world",
                "send-stx",
                vec![
                    Value::UInt(1000000000),
                    Value::Principal(PrincipalData::from(
                        StacksAddress::from_string("ST1H1B54MY50RMBRRKS7GV2ZWG79RZ1RQ1ETW4E01")
                            .unwrap(),
                    )),
                ],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(1);
        tx_contract_call.set_origin_nonce(1);
        tx_contract_call.post_condition_mode = TransactionPostConditionMode::Allow;

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk).unwrap();

        let signed_contract_call_tx = signer.get_tx().unwrap();

        // in epoch 2.05 and earlier, this fails because we debit the fee _after_ we run the tx,
        // which leads to an InvalidFee error
        for (dbi, burn_db) in PRE_21_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );
            let (fee, _) = StacksChainState::process_transaction(
                &mut conn,
                &signed_contract_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();
            let err = StacksChainState::process_transaction(
                &mut conn,
                &signed_contract_call_tx,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap_err();

            conn.commit_block();

            eprintln!("{:?}", &err);
            assert_eq!(fee, 0);
            if let Error::InvalidFee = err {
            } else {
                assert!(false)
            };
        }

        // in epoch 2.1, this passes, since we debit the fee _before_ we run the tx, and then the
        // call to stx-transfer? fails.
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();

        assert_eq!(fee, 1);
        assert_eq!(
            StacksChainState::get_account(&mut conn, &addr.into())
                .stx_balance
                .get_available_balance_at_burn_block(0, 0, 0, 0)
                .unwrap(),
            (1000000000 - fee) as u128
        );

        conn.commit_block();
    }

    fn make_signed_microblock(
        block_privk: &StacksPrivateKey,
        tx_privk: &StacksPrivateKey,
        parent_block: BlockHeaderHash,
        seq: u16,
    ) -> StacksMicroblock {
        // make transaction
        let contract = r#"
        (define-public (send-stx (amount uint) (recipient principal))
            (stx-transfer? amount tx-sender recipient))
        "#;

        let auth = TransactionAuth::from_p2pkh(&tx_privk).unwrap();
        let addr = auth.origin().address_testnet();

        let mut rng = rand::thread_rng();

        let mut tx_contract_create = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &format!("hello-world-{}", &rng.gen::<u32>()),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_create.chain_id = 0x80000000;
        tx_contract_create.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_create);
        signer.sign_origin(&tx_privk).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        // make block
        let txs = vec![signed_contract_tx];
        let txid_vecs: Vec<_> = txs.iter().map(|tx| tx.txid().as_bytes().to_vec()).collect();
        let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
        let tx_merkle_root = merkle_tree.root();

        let mut mblock = StacksMicroblock {
            header: StacksMicroblockHeader {
                version: 0x12,
                sequence: seq,
                prev_block: parent_block,
                tx_merkle_root,
                signature: MessageSignature([0u8; 65]),
            },
            txs,
        };
        mblock.sign(block_privk).unwrap();
        mblock
    }

    #[test]
    fn process_poison_microblock_same_block() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let block_privk = StacksPrivateKey::from_hex(
            "2f90f1b148207a110aa58d1b998510407420d7a8065d4fdfc0bbe22c5d9f1c6a01",
        )
        .unwrap();

        let block_pubkh =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(&block_privk));

        let reporter_privk = StacksPrivateKey::from_hex(
            "e606e944014b2a9788d0e3c8defaf6bc44b1e3ab881aaba32faa6e32002b7e1f01",
        )
        .unwrap();
        let reporter_addr = TransactionAuth::from_p2pkh(&reporter_privk)
            .unwrap()
            .origin()
            .address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            StacksChainState::insert_microblock_pubkey_hash(&mut conn, 1, &block_pubkh).unwrap();

            let height_opt =
                StacksChainState::has_microblock_pubkey_hash(&mut conn, &block_pubkh).unwrap();
            assert_eq!(height_opt.unwrap(), 1);

            // make poison
            let mblock_1 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            let mblock_2 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            assert!(mblock_1 != mblock_2);

            // report poison (in the same block)
            let mut tx_poison_microblock = StacksTransaction::new(
                TransactionVersion::Testnet,
                TransactionAuth::from_p2pkh(&reporter_privk).unwrap(),
                TransactionPayload::PoisonMicroblock(
                    mblock_1.header.clone(),
                    mblock_2.header.clone(),
                ),
            );

            tx_poison_microblock.chain_id = 0x80000000;
            tx_poison_microblock.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx_poison_microblock);
            signer.sign_origin(&reporter_privk).unwrap();
            let signed_tx_poison_microblock = signer.get_tx().unwrap();

            // process it!
            let (fee, receipt) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_poison_microblock,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // there must be a poison record for this microblock, from the reporter, for the microblock
            // sequence.
            let report_opt = StacksChainState::get_poison_microblock_report(&mut conn, 1).unwrap();
            assert_eq!(report_opt.unwrap(), (reporter_addr, 123));

            // result must encode poison information
            let result_data = receipt.result.expect_tuple().unwrap();

            let height = result_data
                .get("block_height")
                .unwrap()
                .to_owned()
                .expect_u128()
                .unwrap();
            let mblock_pubkh = result_data
                .get("microblock_pubkey_hash")
                .unwrap()
                .to_owned()
                .expect_buff(20)
                .unwrap();
            let reporter = result_data
                .get("reporter")
                .unwrap()
                .to_owned()
                .expect_principal()
                .unwrap();
            let seq = result_data
                .get("sequence")
                .unwrap()
                .to_owned()
                .expect_u128()
                .unwrap();

            assert_eq!(height, 1);
            assert_eq!(mblock_pubkh, block_pubkh.0.to_vec());
            assert_eq!(seq, 123);
            assert_eq!(reporter, reporter_addr.to_account_principal());

            conn.commit_block();
        }
    }

    #[test]
    fn process_poison_microblock_invalid_transaction() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let block_privk = StacksPrivateKey::from_hex(
            "2f90f1b148207a110aa58d1b998510407420d7a8065d4fdfc0bbe22c5d9f1c6a01",
        )
        .unwrap();

        let block_pubkh =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(&block_privk));

        let reporter_privk = StacksPrivateKey::from_hex(
            "e606e944014b2a9788d0e3c8defaf6bc44b1e3ab881aaba32faa6e32002b7e1f01",
        )
        .unwrap();
        let reporter_addr = TransactionAuth::from_p2pkh(&reporter_privk)
            .unwrap()
            .origin()
            .address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            StacksChainState::insert_microblock_pubkey_hash(&mut conn, 1, &block_pubkh).unwrap();

            let height_opt =
                StacksChainState::has_microblock_pubkey_hash(&mut conn, &block_pubkh).unwrap();
            assert_eq!(height_opt.unwrap(), 1);

            // make poison, but for an unknown microblock fork
            let mblock_1 = make_signed_microblock(&privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            let mblock_2 = make_signed_microblock(&privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            assert!(mblock_1 != mblock_2);

            // report poison (in the same block)
            let mut tx_poison_microblock = StacksTransaction::new(
                TransactionVersion::Testnet,
                TransactionAuth::from_p2pkh(&reporter_privk).unwrap(),
                TransactionPayload::PoisonMicroblock(
                    mblock_1.header.clone(),
                    mblock_2.header.clone(),
                ),
            );

            tx_poison_microblock.chain_id = 0x80000000;
            tx_poison_microblock.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx_poison_microblock);
            signer.sign_origin(&reporter_privk).unwrap();
            let signed_tx_poison_microblock = signer.get_tx().unwrap();

            // should fail to process -- the transaction is invalid if it doesn't point to a known
            // microblock pubkey hash.
            let err = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_poison_microblock,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap_err();
            if let Error::ClarityError(clarity_error::BadTransaction(msg)) = err {
                assert!(msg.find("never seen in this fork").is_some());
            } else {
                assert!(false);
            }
            conn.commit_block();
        }
    }

    #[test]
    fn process_poison_microblock_multiple_same_block() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let block_privk = StacksPrivateKey::from_hex(
            "2f90f1b148207a110aa58d1b998510407420d7a8065d4fdfc0bbe22c5d9f1c6a01",
        )
        .unwrap();

        let block_pubkh =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(&block_privk));

        let reporter_privk_1 = StacksPrivateKey::from_hex(
            "e606e944014b2a9788d0e3c8defaf6bc44b1e3ab881aaba32faa6e32002b7e1f01",
        )
        .unwrap();
        let reporter_privk_2 = StacksPrivateKey::from_hex(
            "ca7ba28b9604418413a16d74e7dbe5c3e0012281183f590940bab0208c40faee01",
        )
        .unwrap();
        let reporter_addr_1 = TransactionAuth::from_p2pkh(&reporter_privk_1)
            .unwrap()
            .origin()
            .address_testnet();
        let reporter_addr_2 = TransactionAuth::from_p2pkh(&reporter_privk_2)
            .unwrap()
            .origin()
            .address_testnet();

        for (dbi, burn_db) in ALL_BURN_DBS.iter().enumerate() {
            let mut conn = chainstate.block_begin(
                *burn_db,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
                &ConsensusHash([(dbi + 1) as u8; 20]),
                &BlockHeaderHash([(dbi + 1) as u8; 32]),
            );

            StacksChainState::insert_microblock_pubkey_hash(&mut conn, 1, &block_pubkh).unwrap();

            let height_opt =
                StacksChainState::has_microblock_pubkey_hash(&mut conn, &block_pubkh).unwrap();
            assert_eq!(height_opt.unwrap(), 1);

            // make two sets of poisons
            let mblock_1_1 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            let mblock_1_2 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x11; 32]), 123);
            assert!(mblock_1_1 != mblock_1_2);

            // report poison (in the same block)
            let mut tx_poison_microblock_1 = StacksTransaction::new(
                TransactionVersion::Testnet,
                TransactionAuth::from_p2pkh(&reporter_privk_1).unwrap(),
                TransactionPayload::PoisonMicroblock(
                    mblock_1_1.header.clone(),
                    mblock_1_2.header.clone(),
                ),
            );

            tx_poison_microblock_1.chain_id = 0x80000000;
            tx_poison_microblock_1.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx_poison_microblock_1);
            signer.sign_origin(&reporter_privk_1).unwrap();
            let signed_tx_poison_microblock_1 = signer.get_tx().unwrap();

            // make two sets of poisons
            let mblock_2_1 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x10; 32]), 122);
            let mblock_2_2 =
                make_signed_microblock(&block_privk, &privk, BlockHeaderHash([0x10; 32]), 122);
            assert!(mblock_2_1 != mblock_2_2);

            // report poison (in the same block)
            let mut tx_poison_microblock_2 = StacksTransaction::new(
                TransactionVersion::Testnet,
                TransactionAuth::from_p2pkh(&reporter_privk_2).unwrap(),
                TransactionPayload::PoisonMicroblock(
                    mblock_2_1.header.clone(),
                    mblock_2_2.header.clone(),
                ),
            );

            tx_poison_microblock_2.chain_id = 0x80000000;
            tx_poison_microblock_2.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx_poison_microblock_2);
            signer.sign_origin(&reporter_privk_2).unwrap();
            let signed_tx_poison_microblock_2 = signer.get_tx().unwrap();

            // process it!
            let (fee, receipt) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_poison_microblock_1,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // there must be a poison record for this microblock, from the reporter, for the microblock
            // sequence.
            let report_opt = StacksChainState::get_poison_microblock_report(&mut conn, 1).unwrap();
            assert_eq!(report_opt.unwrap(), (reporter_addr_1, 123));

            // process the second one!
            let (fee, receipt) = StacksChainState::process_transaction(
                &mut conn,
                &signed_tx_poison_microblock_2,
                false,
                ASTRules::PrecheckSize,
            )
            .unwrap();

            // there must be a poison record for this microblock, from the reporter, for the microblock
            // sequence.  Moreover, since the fork was earlier in the stream, the second reporter gets
            // it.
            let report_opt = StacksChainState::get_poison_microblock_report(&mut conn, 1).unwrap();
            assert_eq!(report_opt.unwrap(), (reporter_addr_2, 122));

            // result must encode poison information
            let result_data = receipt.result.expect_tuple().unwrap();

            let height = result_data
                .get("block_height")
                .unwrap()
                .to_owned()
                .expect_u128()
                .unwrap();
            let mblock_pubkh = result_data
                .get("microblock_pubkey_hash")
                .unwrap()
                .to_owned()
                .expect_buff(20)
                .unwrap();
            let reporter = result_data
                .get("reporter")
                .unwrap()
                .to_owned()
                .expect_principal()
                .unwrap();
            let seq = result_data
                .get("sequence")
                .unwrap()
                .to_owned()
                .expect_u128()
                .unwrap();

            assert_eq!(height, 1);
            assert_eq!(mblock_pubkh, block_pubkh.0.to_vec());
            assert_eq!(seq, 122);
            assert_eq!(reporter, reporter_addr_2.to_account_principal());

            conn.commit_block();
        }
    }

    #[test]
    fn test_get_tx_clarity_version_v205() {
        struct MockedBurnDB {}

        impl BurnStateDB for MockedBurnDB {
            fn get_tip_burn_block_height(&self) -> Option<u32> {
                Some(0)
            }

            fn get_tip_sortition_id(&self) -> Option<SortitionId> {
                Some(SortitionId([0u8; 32]))
            }

            fn get_v1_unlock_height(&self) -> u32 {
                2
            }
            fn get_v2_unlock_height(&self) -> u32 {
                u32::MAX
            }
            fn get_v3_unlock_height(&self) -> u32 {
                u32::MAX
            }
            fn get_pox_3_activation_height(&self) -> u32 {
                u32::MAX
            }
            fn get_pox_4_activation_height(&self) -> u32 {
                u32::MAX
            }
            fn get_burn_block_height(&self, sortition_id: &SortitionId) -> Option<u32> {
                Some(sortition_id.0[0] as u32)
            }
            fn get_burn_start_height(&self) -> u32 {
                0
            }
            fn get_pox_prepare_length(&self) -> u32 {
                3
            }
            fn get_pox_reward_cycle_length(&self) -> u32 {
                6
            }
            fn get_pox_rejection_fraction(&self) -> u64 {
                15
            }
            fn get_burn_header_hash(
                &self,
                height: u32,
                sortition_id: &SortitionId,
            ) -> Option<BurnchainHeaderHash> {
                Some(BurnchainHeaderHash([height as u8; 32]))
            }
            fn get_sortition_id_from_consensus_hash(
                &self,
                consensus_hash: &ConsensusHash,
            ) -> Option<SortitionId> {
                Some(SortitionId([consensus_hash.0[0]; 32]))
            }
            fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch> {
                Some(match height {
                    0 => StacksEpoch {
                        epoch_id: StacksEpochId::Epoch2_05,
                        start_height: 1,
                        end_height: 2,
                        block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
                        network_epoch: PEER_VERSION_EPOCH_2_05,
                    },
                    _ => StacksEpoch {
                        epoch_id: StacksEpochId::Epoch21,
                        start_height: 2,
                        end_height: u64::MAX,
                        block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
                        network_epoch: PEER_VERSION_EPOCH_2_1,
                    },
                })
            }
            fn get_stacks_epoch_by_epoch_id(
                &self,
                epoch_id: &StacksEpochId,
            ) -> Option<StacksEpoch> {
                match epoch_id {
                    StacksEpochId::Epoch10 => Some(StacksEpoch {
                        epoch_id: StacksEpochId::Epoch10,
                        start_height: 0,
                        end_height: 0,
                        block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
                        network_epoch: PEER_VERSION_EPOCH_2_0,
                    }),
                    StacksEpochId::Epoch20 => self.get_stacks_epoch(0),
                    StacksEpochId::Epoch2_05 => self.get_stacks_epoch(1),
                    StacksEpochId::Epoch21 => self.get_stacks_epoch(2),
                    StacksEpochId::Epoch22 => self.get_stacks_epoch(3),
                    StacksEpochId::Epoch23 => self.get_stacks_epoch(4),
                    StacksEpochId::Epoch24 => self.get_stacks_epoch(5),
                    StacksEpochId::Epoch25 => self.get_stacks_epoch(6),
                    StacksEpochId::Epoch30 => self.get_stacks_epoch(7),
                    StacksEpochId::Epoch31 => self.get_stacks_epoch(8),
                }
            }
            fn get_pox_payout_addrs(
                &self,
                height: u32,
                sortition_id: &SortitionId,
            ) -> Option<(Vec<TupleData>, u128)> {
                None
            }
            fn get_ast_rules(&self, _block_height: u32) -> ASTRules {
                ASTRules::PrecheckSize
            }
        }

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        let smart_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                None,
            ),
        );
        let smart_contract_v1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                Some(ClarityVersion::Clarity1),
            ),
        );
        let smart_contract_v2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                Some(ClarityVersion::Clarity2),
            ),
        );
        let token_transfer = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let txs = vec![
            smart_contract,
            smart_contract_v1,
            smart_contract_v2,
            token_transfer,
        ];
        let mut signed_txs = vec![];
        for mut tx in txs.into_iter() {
            tx.chain_id = 0x80000000;
            tx.post_condition_mode = TransactionPostConditionMode::Allow;
            tx.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx);
            signer.sign_origin(&privk).unwrap();
            let signed_tx = signer.get_tx().unwrap();
            signed_txs.push(signed_tx);
        }

        let token_transfer = signed_txs.pop().unwrap();
        let smart_contract_v2 = signed_txs.pop().unwrap();
        let smart_contract_v1 = signed_txs.pop().unwrap();
        let smart_contract = signed_txs.pop().unwrap();

        let burndb = MockedBurnDB {};

        let mut conn = chainstate.block_begin(
            &burndb,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );

        assert_eq!(conn.get_epoch(), StacksEpochId::Epoch2_05);
        assert_eq!(
            ClarityVersion::Clarity1,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity1,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract_v1).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity2,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract_v2).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity1,
            StacksChainState::get_tx_clarity_version(&mut conn, &token_transfer).unwrap()
        );

        // verify that 2.1 gating is applied for clarity2
        if let Err(Error::InvalidStacksTransaction(msg, ..)) = StacksChainState::process_transaction(
            &mut conn,
            &smart_contract_v2,
            false,
            ASTRules::PrecheckSize,
        ) {
            assert!(msg.find("not in Stacks epoch 2.1 or later").is_some());
        } else {
            panic!("FATAL: did not recieve the appropriate error in processing a clarity2 tx in pre-2.1 epoch");
        }

        conn.commit_block();
    }

    #[test]
    fn test_get_tx_clarity_version_v210() {
        struct MockedBurnDB {}

        impl BurnStateDB for MockedBurnDB {
            fn get_tip_burn_block_height(&self) -> Option<u32> {
                Some(0)
            }

            fn get_tip_sortition_id(&self) -> Option<SortitionId> {
                Some(SortitionId([0u8; 32]))
            }

            fn get_v1_unlock_height(&self) -> u32 {
                2
            }
            fn get_v2_unlock_height(&self) -> u32 {
                u32::MAX
            }
            fn get_v3_unlock_height(&self) -> u32 {
                u32::MAX
            }
            fn get_pox_3_activation_height(&self) -> u32 {
                u32::MAX
            }
            fn get_pox_4_activation_height(&self) -> u32 {
                u32::MAX
            }
            fn get_burn_block_height(&self, sortition_id: &SortitionId) -> Option<u32> {
                Some(sortition_id.0[0] as u32)
            }
            fn get_burn_start_height(&self) -> u32 {
                0
            }
            fn get_pox_prepare_length(&self) -> u32 {
                3
            }
            fn get_pox_reward_cycle_length(&self) -> u32 {
                6
            }
            fn get_pox_rejection_fraction(&self) -> u64 {
                15
            }
            fn get_burn_header_hash(
                &self,
                height: u32,
                sortition_id: &SortitionId,
            ) -> Option<BurnchainHeaderHash> {
                Some(BurnchainHeaderHash([height as u8; 32]))
            }
            fn get_sortition_id_from_consensus_hash(
                &self,
                consensus_hash: &ConsensusHash,
            ) -> Option<SortitionId> {
                Some(SortitionId([consensus_hash.0[0]; 32]))
            }
            fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch> {
                Some(StacksEpoch {
                    epoch_id: StacksEpochId::Epoch21,
                    start_height: 0,
                    end_height: u64::MAX,
                    block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
                    network_epoch: PEER_VERSION_EPOCH_2_1,
                })
            }
            fn get_stacks_epoch_by_epoch_id(
                &self,
                epoch_id: &StacksEpochId,
            ) -> Option<StacksEpoch> {
                match epoch_id {
                    StacksEpochId::Epoch10 => Some(StacksEpoch {
                        epoch_id: StacksEpochId::Epoch10,
                        start_height: 0,
                        end_height: 0,
                        block_limit: HELIUM_BLOCK_LIMIT_20.clone(),
                        network_epoch: PEER_VERSION_EPOCH_2_0,
                    }),
                    _ => self.get_stacks_epoch(0),
                }
            }
            fn get_pox_payout_addrs(
                &self,
                height: u32,
                sortition_id: &SortitionId,
            ) -> Option<(Vec<TupleData>, u128)> {
                None
            }
            fn get_ast_rules(&self, _block_height: u32) -> ASTRules {
                ASTRules::PrecheckSize
            }
        }

        let mut chainstate = instantiate_chainstate(false, 0x80000000, function_name!());

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        let smart_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                None,
            ),
        );
        let smart_contract_v1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                Some(ClarityVersion::Clarity1),
            ),
        );
        let smart_contract_v2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::SmartContract(
                TransactionSmartContract {
                    name: ContractName::try_from("hello-world").unwrap(),
                    code_body: StacksString::from_str("(print \"hello\")").unwrap(),
                },
                Some(ClarityVersion::Clarity2),
            ),
        );
        let token_transfer = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );

        let txs = vec![
            smart_contract,
            smart_contract_v1,
            smart_contract_v2,
            token_transfer,
        ];
        let mut signed_txs = vec![];
        for mut tx in txs.into_iter() {
            tx.chain_id = 0x80000000;
            tx.post_condition_mode = TransactionPostConditionMode::Allow;
            tx.set_tx_fee(0);

            let mut signer = StacksTransactionSigner::new(&tx);
            signer.sign_origin(&privk).unwrap();
            let signed_tx = signer.get_tx().unwrap();
            signed_txs.push(signed_tx);
        }

        let token_transfer = signed_txs.pop().unwrap();
        let smart_contract_v2 = signed_txs.pop().unwrap();
        let smart_contract_v1 = signed_txs.pop().unwrap();
        let smart_contract = signed_txs.pop().unwrap();

        let burndb = MockedBurnDB {};

        let mut conn = chainstate.block_begin(
            &burndb,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );

        assert_eq!(conn.get_epoch(), StacksEpochId::Epoch21);
        assert_eq!(
            ClarityVersion::Clarity2,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity1,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract_v1).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity2,
            StacksChainState::get_tx_clarity_version(&mut conn, &smart_contract_v2).unwrap()
        );
        assert_eq!(
            ClarityVersion::Clarity2,
            StacksChainState::get_tx_clarity_version(&mut conn, &token_transfer).unwrap()
        );

        conn.commit_block();
    }

    #[test]
    fn process_fee_gating() {
        let contract = r#"
        (define-public (send-stx (amount uint) (recipient principal))
            (as-contract
                (stx-transfer? amount tx-sender recipient))
        )

        (stx-transfer? u500000000 tx-sender (as-contract tx-sender))
        "#;

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let privk_recv = StacksPrivateKey::from_hex(
            "9bb626a4b2656a31e70d7828b54ad44efb6e549ac8e59214d5ef0bbabffcc03d01",
        )
        .unwrap();
        let auth_recv = TransactionAuth::from_p2pkh(&privk_recv).unwrap();
        let addr_recv = auth_recv.origin().address_testnet();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_contract_create = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"faucet".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_create.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_contract_create.chain_id = 0x80000000;
        tx_contract_create.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_create);
        signer.sign_origin(&privk).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        // recipient tries to get some STX, but with a tx fee.
        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_recv.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "faucet",
                "send-stx",
                vec![
                    Value::UInt(100000),
                    Value::Principal(PrincipalData::from(addr_recv.clone())),
                ],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(1);
        tx_contract_call.set_origin_nonce(0);
        tx_contract_call.post_condition_mode = TransactionPostConditionMode::Allow;

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk_recv).unwrap();

        let signed_contract_call_tx = signer.get_tx().unwrap();

        // In 2.0, this will succeed since we debit the fee *after* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_20,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([1u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        conn.commit_block();

        // In 2.05, this will succeed since we debit the fee *after* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_2_05,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        conn.commit_block();

        // post-2.1, this will fail since we debit the fee *before* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let err = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        conn.commit_block();

        eprintln!("{:?}", &err);
        if let Error::InvalidFee = err {
        } else {
            assert!(false)
        };
    }

    #[test]
    fn process_fee_gating_sponsored() {
        let contract = r#"
        (define-public (send-stx (amount uint) (recipient principal))
            (as-contract
                (stx-transfer? amount tx-sender recipient))
        )

        (stx-transfer? u500000000 tx-sender (as-contract tx-sender))
        "#;

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let privk_origin = StacksPrivateKey::from_hex(
            "a469b97ccaa4553767bc1359390d1b239d2e5ec7b69dbc509fe2cd566fd55ec101",
        )
        .unwrap();
        let auth_origin = TransactionAuth::from_p2pkh(&privk_origin).unwrap();
        let addr_origin = auth_origin.origin().address_testnet();

        let privk_recv = StacksPrivateKey::from_hex(
            "9bb626a4b2656a31e70d7828b54ad44efb6e549ac8e59214d5ef0bbabffcc03d01",
        )
        .unwrap();
        let auth_recv = TransactionAuth::from_p2pkh(&privk_recv).unwrap();
        let addr_recv = auth_recv.origin().address_testnet();

        let auth_recv = auth_origin.into_sponsored(auth_recv).unwrap();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_contract_create = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"faucet".to_string(),
                &contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_contract_create.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_contract_create.chain_id = 0x80000000;
        tx_contract_create.set_tx_fee(0);

        let mut signer = StacksTransactionSigner::new(&tx_contract_create);
        signer.sign_origin(&privk).unwrap();

        let signed_contract_tx = signer.get_tx().unwrap();

        // recipient tries to get some STX, but with a tx fee.
        let mut tx_contract_call = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth_recv.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "faucet",
                "send-stx",
                vec![
                    Value::UInt(100000),
                    Value::Principal(PrincipalData::from(addr_recv.clone())),
                ],
            )
            .unwrap(),
        );

        tx_contract_call.chain_id = 0x80000000;
        tx_contract_call.set_tx_fee(1);
        tx_contract_call.set_origin_nonce(0);
        tx_contract_call.set_sponsor_nonce(0).unwrap();
        tx_contract_call.post_condition_mode = TransactionPostConditionMode::Allow;

        let mut signer = StacksTransactionSigner::new(&tx_contract_call);
        signer.sign_origin(&privk_origin).unwrap();
        signer.sign_sponsor(&privk_recv).unwrap();

        let signed_contract_call_tx = signer.get_tx().unwrap();

        // In 2.0, this will succeed since we debit the fee *after* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_20,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([1u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        conn.commit_block();

        // In 2.05, this will succeed since we debit the fee *after* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_2_05,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        conn.commit_block();

        // post-2.1, this will fail since we debit the fee *before* we run the contract
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );
        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 0);

        let err = StacksChainState::process_transaction(
            &mut conn,
            &signed_contract_call_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        conn.commit_block();

        eprintln!("{:?}", &err);
        if let Error::InvalidFee = err {
        } else {
            assert!(false)
        };
    }

    /// Call `process_transaction()` with  prechecks
    pub fn validate_transactions_static_epoch_and_process_transaction(
        clarity_block: &mut ClarityTx,
        tx: &StacksTransaction,
        quiet: bool,
        ast_rules: ASTRules,
    ) -> Result<(u64, StacksTransactionReceipt), Error> {
        let epoch = clarity_block.get_epoch();

        if !StacksBlock::validate_transactions_static_epoch(&vec![tx.clone()], epoch) {
            let msg = format!(
                "Invalid transaction {}: target epoch is not activated",
                tx.txid()
            );
            warn!("{}", &msg);
            return Err(Error::InvalidStacksTransaction(msg, false));
        }

        StacksChainState::process_transaction(clarity_block, tx, quiet, ast_rules)
    }

    #[test]
    fn test_checkerrors_at_runtime() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let runtime_checkerror_trait = "
            (define-trait foo
                (
                    (lolwut () (response bool uint))
                )
            )
            "
        .to_string();

        let runtime_checkerror_impl = "
            (impl-trait .foo.foo)

            (define-public (lolwut)
                (ok true)
            )
            "
        .to_string();

        let runtime_checkerror = "
            (use-trait trait .foo.foo)

            (define-data-var mutex bool true)
            (define-data-var executed bool false)

            (define-public (flip)
              (ok (var-set mutex (not (var-get mutex))))
            )

            ;; triggers checkerror at runtime because <trait> gets coerced
            ;; into a principal when `internal` is called.
            (define-public (test (ref <trait>))
                (ok (internal (if (var-get mutex)
                    (begin
                        (print \"some case\")
                        (var-set executed true)
                        (some ref)
                    )
                    none
                )))
            )

            (define-private (internal (ref (optional <trait>))) true)
            "
        .to_string();

        let runtime_checkerror_contract = "
            (begin
                (print \"about to contract-call with trait impl\")
                (unwrap-panic (contract-call? .trait-checkerror test .foo-impl))
                (print \"contract-call with trait impl finished\")
            )
            ";

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_runtime_checkerror_trait_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &runtime_checkerror_trait.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_runtime_checkerror_trait_no_version.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_trait_no_version.chain_id = 0x80000000;
        tx_runtime_checkerror_trait_no_version.set_tx_fee(1);
        tx_runtime_checkerror_trait_no_version.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_trait_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_trait_tx_no_version = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_trait = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &runtime_checkerror_trait.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_trait.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_trait.chain_id = 0x80000000;
        tx_runtime_checkerror_trait.set_tx_fee(1);
        tx_runtime_checkerror_trait.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_trait);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_trait_tx = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_impl = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &runtime_checkerror_impl.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_impl.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_impl.chain_id = 0x80000000;
        tx_runtime_checkerror_impl.set_tx_fee(1);
        tx_runtime_checkerror_impl.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_impl);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_impl_tx = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_impl_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &runtime_checkerror_impl.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_runtime_checkerror_impl_no_version.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_impl_no_version.chain_id = 0x80000000;
        tx_runtime_checkerror_impl_no_version.set_tx_fee(1);
        tx_runtime_checkerror_impl_no_version.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_impl_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_impl_tx_no_version = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_clar1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror".to_string(),
                &runtime_checkerror.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_clar1.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_clar1.chain_id = 0x80000000;
        tx_runtime_checkerror_clar1.set_tx_fee(1);
        tx_runtime_checkerror_clar1.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_tx_clar1 = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_clar1_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror".to_string(),
                &runtime_checkerror.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_runtime_checkerror_clar1_no_version.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_clar1_no_version.chain_id = 0x80000000;
        tx_runtime_checkerror_clar1_no_version.set_tx_fee(1);
        tx_runtime_checkerror_clar1_no_version.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_clar1_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_tx_clar1_no_version = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_clar2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror".to_string(),
                &runtime_checkerror.to_string(),
                Some(ClarityVersion::Clarity2),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_clar2.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_clar2.chain_id = 0x80000000;
        tx_runtime_checkerror_clar2.set_tx_fee(1);
        tx_runtime_checkerror_clar2.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_clar2);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_tx_clar2 = signer.get_tx().unwrap();

        let mut tx_test_trait_checkerror = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "trait-checkerror",
                "test",
                vec![Value::Principal(PrincipalData::Contract(
                    QualifiedContractIdentifier::parse(&format!("{}.foo-impl", &addr)).unwrap(),
                ))],
            )
            .unwrap(),
        );

        tx_test_trait_checkerror.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_test_trait_checkerror.chain_id = 0x80000000;
        tx_test_trait_checkerror.set_tx_fee(1);
        tx_test_trait_checkerror.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_test_trait_checkerror);
        signer.sign_origin(&privk).unwrap();

        let signed_test_trait_checkerror_tx = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_cc_contract_clar1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror-cc".to_string(),
                &runtime_checkerror_contract.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_cc_contract_clar1.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_cc_contract_clar1.chain_id = 0x80000000;
        tx_runtime_checkerror_cc_contract_clar1.set_tx_fee(1);
        tx_runtime_checkerror_cc_contract_clar1.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_cc_contract_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_cc_contract_tx_clar1 = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_cc_contract_clar1_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror-cc".to_string(),
                &runtime_checkerror_contract.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_runtime_checkerror_cc_contract_clar1_no_version.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_cc_contract_clar1_no_version.chain_id = 0x80000000;
        tx_runtime_checkerror_cc_contract_clar1_no_version.set_tx_fee(1);
        tx_runtime_checkerror_cc_contract_clar1_no_version.set_origin_nonce(3);

        let mut signer =
            StacksTransactionSigner::new(&tx_runtime_checkerror_cc_contract_clar1_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_cc_contract_tx_clar1_no_version = signer.get_tx().unwrap();

        let mut tx_runtime_checkerror_cc_contract_clar2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"trait-checkerror-cc".to_string(),
                &runtime_checkerror_contract.to_string(),
                Some(ClarityVersion::Clarity2),
            )
            .unwrap(),
        );

        tx_runtime_checkerror_cc_contract_clar2.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_runtime_checkerror_cc_contract_clar2.chain_id = 0x80000000;
        tx_runtime_checkerror_cc_contract_clar2.set_tx_fee(1);
        tx_runtime_checkerror_cc_contract_clar2.set_origin_nonce(4);

        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_cc_contract_clar2);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_cc_contract_tx_clar2 = signer.get_tx().unwrap();

        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::from("trait-checkerror"),
        );

        // in 2.0, this invalidates the block
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_20,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([1u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_trait_checkerror_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            _check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 3);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_cc_contract_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            _check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 3);

        conn.commit_block();

        // in 2.05, this invalidates the block
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_2_05,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_trait_checkerror_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            _check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 3);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_cc_contract_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            _check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 3);

        conn.commit_block();

        // in 2.1, this is a runtime error when using clarity 1
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );

        // make this mineable
        tx_runtime_checkerror_cc_contract_clar1.set_origin_nonce(4);
        let mut signer = StacksTransactionSigner::new(&tx_runtime_checkerror_cc_contract_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_runtime_checkerror_cc_contract_tx_clar1 = signer.get_tx().unwrap();

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = StacksChainState::process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_trait_checkerror_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        // nonce keeps advancing despite error
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 4);

        // no state change materialized
        let executed_var =
            StacksChainState::get_data_var(&mut conn, &contract_id, "executed").unwrap();
        assert_eq!(executed_var, Some(Value::Bool(false)));

        assert!(tx_receipt.vm_error.is_some());
        let err_str = tx_receipt.vm_error.unwrap();
        assert!(err_str
            .find("TypeValueError(OptionalType(CallableType(Trait(TraitIdentifier ")
            .is_some());

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_cc_contract_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        // nonce keeps advancing despite error
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 5);

        // no state change materialized
        let executed_var =
            StacksChainState::get_data_var(&mut conn, &contract_id, "executed").unwrap();
        assert_eq!(executed_var, Some(Value::Bool(false)));

        assert!(tx_receipt.vm_error.is_some());
        let err_str = tx_receipt.vm_error.unwrap();
        assert!(err_str
            .find("TypeValueError(OptionalType(CallableType(Trait(TraitIdentifier ")
            .is_some());

        conn.commit_block();

        // in 2.1, this is successful when using clarity 2
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([4u8; 20]),
            &BlockHeaderHash([4u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_tx_clar2,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_trait_checkerror_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        // nonce keeps advancing
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 4);

        // state change materialized
        let executed_var =
            StacksChainState::get_data_var(&mut conn, &contract_id, "executed").unwrap();
        assert_eq!(executed_var, Some(Value::Bool(true)));

        assert!(tx_receipt.vm_error.is_none());

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_runtime_checkerror_cc_contract_tx_clar2,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        // nonce keeps advancing
        let acct = StacksChainState::get_account(&mut conn, &addr.into());
        assert_eq!(acct.nonce, 5);

        // state change materialized
        let executed_var =
            StacksChainState::get_data_var(&mut conn, &contract_id, "executed").unwrap();
        assert_eq!(executed_var, Some(Value::Bool(true)));

        assert!(tx_receipt.vm_error.is_none());

        conn.commit_block();
    }

    #[test]
    fn test_embedded_trait() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let foo_trait = "
            (define-trait foo
                (
                    (do-it () (response bool uint))
                )
            )
            "
        .to_string();

        let foo_impl = "
            (impl-trait .foo.foo)

            (define-public (do-it)
                (ok true)
            )
            "
        .to_string();

        let call_foo = "
            (use-trait foo .foo.foo)
            (define-public (call-do-it (opt-f (optional <foo>)))
                (match opt-f
                    f (contract-call? f do-it)
                    (ok false)
                )
            )
            "
        .to_string();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_foo_trait = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &foo_trait.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_foo_trait.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_trait.chain_id = 0x80000000;
        tx_foo_trait.set_tx_fee(1);
        tx_foo_trait.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_foo_trait);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_trait_tx = signer.get_tx().unwrap();

        let mut tx_foo_trait_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &foo_trait.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_foo_trait_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_trait_no_version.chain_id = 0x80000000;
        tx_foo_trait_no_version.set_tx_fee(1);
        tx_foo_trait_no_version.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_foo_trait_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_trait_tx_no_version = signer.get_tx().unwrap();

        let mut tx_foo_impl = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &foo_impl.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_foo_impl.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_impl.chain_id = 0x80000000;
        tx_foo_impl.set_tx_fee(1);
        tx_foo_impl.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_foo_impl);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_impl_tx = signer.get_tx().unwrap();

        let mut tx_foo_impl_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &foo_impl.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_foo_impl_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_impl_no_version.chain_id = 0x80000000;
        tx_foo_impl_no_version.set_tx_fee(1);
        tx_foo_impl_no_version.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_foo_impl_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_impl_tx_no_version = signer.get_tx().unwrap();

        let mut tx_call_foo_clar1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_call_foo_clar1.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar1.chain_id = 0x80000000;
        tx_call_foo_clar1.set_tx_fee(1);
        tx_call_foo_clar1.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar1 = signer.get_tx().unwrap();

        let mut tx_call_foo_clar1_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_call_foo_clar1_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar1_no_version.chain_id = 0x80000000;
        tx_call_foo_clar1_no_version.set_tx_fee(1);
        tx_call_foo_clar1_no_version.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar1_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar1_no_version = signer.get_tx().unwrap();

        let mut tx_call_foo_clar2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                Some(ClarityVersion::Clarity2),
            )
            .unwrap(),
        );

        tx_call_foo_clar2.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar2.chain_id = 0x80000000;
        tx_call_foo_clar2.set_tx_fee(1);
        tx_call_foo_clar2.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar2);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar2 = signer.get_tx().unwrap();

        let mut tx_test_call_foo = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "call-foo",
                "call-do-it",
                vec![Value::some(Value::Principal(PrincipalData::Contract(
                    QualifiedContractIdentifier::parse(&format!("{}.foo-impl", &addr)).unwrap(),
                )))
                .unwrap()],
            )
            .unwrap(),
        );

        tx_test_call_foo.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_test_call_foo.chain_id = 0x80000000;
        tx_test_call_foo.set_tx_fee(1);
        tx_test_call_foo.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_test_call_foo);
        signer.sign_origin(&privk).unwrap();

        let signed_test_call_foo_tx = signer.get_tx().unwrap();

        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::from("trait-checkerror"),
        );

        // in 2.0: analysis error should cause contract publish to fail
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_20,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([1u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data: _,
            }) => (),
            _ => panic!("expected the contract publish to fail"),
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        conn.commit_block();

        // in 2.05: analysis error should cause contract publish to fail
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_2_05,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data: _,
            }) => (),
            _ => panic!("expected the contract publish to fail"),
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        conn.commit_block();

        // in 2.1, using clarity 1: analysis error should cause contract publish to fail
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data: _,
            }) => (),
            _ => panic!("expected the contract publish to fail"),
        }

        conn.commit_block();

        // in 2.1, using clarity 2: success
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([4u8; 20]),
            &BlockHeaderHash([4u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar2,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: true,
                data,
            }) => match *data {
                Value::Bool(true) => (),
                _ => panic!("expected (ok true) result"),
            },
            _ => panic!("expected successful call"),
        }

        conn.commit_block();
    }

    #[test]
    fn test_transitive_trait() {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();

        let foo_trait = "
            (define-trait foo
                (
                    (do-it () (response bool uint))
                )
            )
            "
        .to_string();

        let transitive_trait = "
            (use-trait foo .foo.foo)
            (define-trait poo
                (
                    (do-it () (response bool uint))
                )
            )
        "
        .to_string();

        let foo_impl = "
            (impl-trait .foo.foo)

            (define-public (do-it)
                (ok true)
            )
            "
        .to_string();

        let call_foo = "
            (use-trait foo .transitive.foo)
            (define-public (call-do-it (f <foo>))
                (contract-call? f do-it)
            )
            "
        .to_string();

        let balances = vec![(addr.clone(), 1000000000)];

        let mut chainstate =
            instantiate_chainstate_with_balances(false, 0x80000000, function_name!(), balances);

        let mut tx_foo_trait = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &foo_trait.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_foo_trait.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_trait.chain_id = 0x80000000;
        tx_foo_trait.set_tx_fee(1);
        tx_foo_trait.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_foo_trait);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_trait_tx = signer.get_tx().unwrap();

        let mut tx_foo_trait_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo".to_string(),
                &foo_trait.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_foo_trait_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_trait_no_version.chain_id = 0x80000000;
        tx_foo_trait_no_version.set_tx_fee(1);
        tx_foo_trait_no_version.set_origin_nonce(0);

        let mut signer = StacksTransactionSigner::new(&tx_foo_trait_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_trait_tx_no_version = signer.get_tx().unwrap();

        let mut tx_transitive_trait_clar1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"transitive".to_string(),
                &transitive_trait.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_transitive_trait_clar1.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_transitive_trait_clar1.chain_id = 0x80000000;
        tx_transitive_trait_clar1.set_tx_fee(1);
        tx_transitive_trait_clar1.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_transitive_trait_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_transitive_trait_clar1_tx = signer.get_tx().unwrap();

        let mut tx_transitive_trait_clar1_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"transitive".to_string(),
                &transitive_trait.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_transitive_trait_clar1_no_version.post_condition_mode =
            TransactionPostConditionMode::Allow;
        tx_transitive_trait_clar1_no_version.chain_id = 0x80000000;
        tx_transitive_trait_clar1_no_version.set_tx_fee(1);
        tx_transitive_trait_clar1_no_version.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_transitive_trait_clar1_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_transitive_trait_clar1_tx_no_version = signer.get_tx().unwrap();

        let mut tx_transitive_trait_clar2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"transitive".to_string(),
                &transitive_trait.to_string(),
                Some(ClarityVersion::Clarity2),
            )
            .unwrap(),
        );

        tx_transitive_trait_clar2.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_transitive_trait_clar2.chain_id = 0x80000000;
        tx_transitive_trait_clar2.set_tx_fee(1);
        tx_transitive_trait_clar2.set_origin_nonce(1);

        let mut signer = StacksTransactionSigner::new(&tx_transitive_trait_clar2);
        signer.sign_origin(&privk).unwrap();

        let signed_transitive_trait_clar2_tx = signer.get_tx().unwrap();

        let mut tx_foo_impl = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &foo_impl.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_foo_impl.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_impl.chain_id = 0x80000000;
        tx_foo_impl.set_tx_fee(1);
        tx_foo_impl.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_foo_impl);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_impl_tx = signer.get_tx().unwrap();

        let mut tx_foo_impl_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"foo-impl".to_string(),
                &foo_impl.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_foo_impl_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_foo_impl_no_version.chain_id = 0x80000000;
        tx_foo_impl_no_version.set_tx_fee(1);
        tx_foo_impl_no_version.set_origin_nonce(2);

        let mut signer = StacksTransactionSigner::new(&tx_foo_impl_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_foo_impl_tx_no_version = signer.get_tx().unwrap();

        let mut tx_call_foo_clar1 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                Some(ClarityVersion::Clarity1),
            )
            .unwrap(),
        );

        tx_call_foo_clar1.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar1.chain_id = 0x80000000;
        tx_call_foo_clar1.set_tx_fee(1);
        tx_call_foo_clar1.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar1);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar1 = signer.get_tx().unwrap();

        let mut tx_call_foo_clar1_no_version = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                None,
            )
            .unwrap(),
        );

        tx_call_foo_clar1_no_version.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar1_no_version.chain_id = 0x80000000;
        tx_call_foo_clar1_no_version.set_tx_fee(1);
        tx_call_foo_clar1_no_version.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar1_no_version);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar1_no_version = signer.get_tx().unwrap();

        let mut tx_call_foo_clar2 = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &"call-foo".to_string(),
                &call_foo.to_string(),
                Some(ClarityVersion::Clarity2),
            )
            .unwrap(),
        );

        tx_call_foo_clar2.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_call_foo_clar2.chain_id = 0x80000000;
        tx_call_foo_clar2.set_tx_fee(1);
        tx_call_foo_clar2.set_origin_nonce(3);

        let mut signer = StacksTransactionSigner::new(&tx_call_foo_clar2);
        signer.sign_origin(&privk).unwrap();

        let signed_call_foo_tx_clar2 = signer.get_tx().unwrap();

        let mut tx_test_call_foo = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_contract_call(
                addr.clone(),
                "call-foo",
                "call-do-it",
                vec![Value::Principal(PrincipalData::Contract(
                    QualifiedContractIdentifier::parse(&format!("{}.foo-impl", &addr)).unwrap(),
                ))],
            )
            .unwrap(),
        );

        tx_test_call_foo.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_test_call_foo.chain_id = 0x80000000;
        tx_test_call_foo.set_tx_fee(1);
        tx_test_call_foo.set_origin_nonce(4);

        let mut signer = StacksTransactionSigner::new(&tx_test_call_foo);
        signer.sign_origin(&privk).unwrap();

        let signed_test_call_foo_tx = signer.get_tx().unwrap();

        let contract_id = QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::from("trait-checkerror"),
        );

        // in 2.0: calling call-foo invalidates the block
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_20,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([1u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }
        assert_eq!(fee, 1);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        conn.commit_block();

        // in 2.05: calling call-foo invalidates the block
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_2_05,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([2u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1_no_version,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::ClarityError(clarity_error::Interpreter(InterpreterError::Unchecked(
            check_error,
        ))) = err
        {
        } else {
            panic!("Did not get unchecked interpreter error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        let err = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap_err();
        if let Error::InvalidStacksTransaction(msg, _ignored) = err {
            assert!(msg.find("target epoch is not activated").is_some());
        } else {
            panic!("Did not get epoch is not activated error");
        }

        conn.commit_block();

        // in 2.1, using clarity 1 for both `transitive` and `call-foo`: calling call-foo causes an analysis error
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([3u8; 20]),
            &BlockHeaderHash([3u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data,
            }) => (),
            _ => panic!("expected successful call"),
        }
        assert_eq!(
            tx_receipt.vm_error,
            Some("TraitReferenceUnknown(\"foo\")".to_string())
        );

        conn.commit_block();

        // in 2.1, using clarity 1 for `transitive` and clarity 2 for `call-foo`: calling call-foo causes an analysis error
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([4u8; 20]),
            &BlockHeaderHash([4u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar1_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar2,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_test_call_foo_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data,
            }) => (),
            _ => panic!("expected successful call"),
        }
        assert_eq!(
            tx_receipt.vm_error,
            Some("TraitReferenceUnknown(\"foo\")".to_string())
        );

        conn.commit_block();

        // in 2.1, using clarity 2 for both `transitive` and `call-foo`: publishing call-foo triggers an analysis error
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([5u8; 20]),
            &BlockHeaderHash([5u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar2_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar2,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data,
            }) => assert_eq!(*data, Value::none()),
            _ => panic!("expected error response"),
        }

        conn.commit_block();

        // in 2.1, using clarity 2 for `transitive` and clarity 1 for `call-foo`: publishing call-foo triggers an analysis error
        let mut conn = chainstate.block_begin(
            &TestBurnStateDB_21,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &ConsensusHash([6u8; 20]),
            &BlockHeaderHash([6u8; 32]),
        );

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_trait_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_transitive_trait_clar2_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, _) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_foo_impl_tx,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);

        let (fee, tx_receipt) = validate_transactions_static_epoch_and_process_transaction(
            &mut conn,
            &signed_call_foo_tx_clar1,
            false,
            ASTRules::PrecheckSize,
        )
        .unwrap();
        assert_eq!(fee, 1);
        match tx_receipt.result {
            Value::Response(ResponseData {
                committed: false,
                data,
            }) => assert_eq!(*data, Value::none()),
            _ => panic!("expected error response"),
        }

        conn.commit_block();
    }
}
