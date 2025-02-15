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

use stacks_common::consts::CHAIN_ID_TESTNET;
use stacks_common::types::chainstate::StacksBlockId;
use stacks_common::types::StacksEpochId;

use crate::vm::callables::DefineType;
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::{constants as cost_constants, runtime_cost, CostTracker, MemoryConsumer};
use crate::vm::errors::{
    check_argument_count, check_arguments_at_least, CheckErrors, InterpreterError,
    InterpreterResult as Result, RuntimeErrorType,
};
use crate::vm::representations::{SymbolicExpression, SymbolicExpressionType};
use crate::vm::types::{
    BlockInfoProperty, BuffData, BurnBlockInfoProperty, PrincipalData, SequenceData,
    StacksBlockInfoProperty, TenureInfoProperty, TupleData, TypeSignature, Value, BUFF_32,
};
use crate::vm::{eval, ClarityVersion, Environment, LocalContext};

switch_on_global_epoch!(special_fetch_variable(
    special_fetch_variable_v200,
    special_fetch_variable_v205
));
switch_on_global_epoch!(special_set_variable(
    special_set_variable_v200,
    special_set_variable_v205
));
switch_on_global_epoch!(special_fetch_entry(
    special_fetch_entry_v200,
    special_fetch_entry_v205
));
switch_on_global_epoch!(special_set_entry(
    special_set_entry_v200,
    special_set_entry_v205
));
switch_on_global_epoch!(special_insert_entry(
    special_insert_entry_v200,
    special_insert_entry_v205
));
switch_on_global_epoch!(special_delete_entry(
    special_delete_entry_v200,
    special_delete_entry_v205
));

pub fn special_contract_call(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_arguments_at_least(2, args)?;

    // the second part of the contract_call cost (i.e., the load contract cost)
    //   is checked in `execute_contract`, and the function _application_ cost
    //   is checked in callables::DefinedFunction::execute_apply.
    runtime_cost(ClarityCostFunction::ContractCall, env, 0)?;

    let function_name = args[1].match_atom().ok_or(CheckErrors::ExpectedName)?;
    let rest_args_slice = &args[2..];
    let rest_args_len = rest_args_slice.len();
    let mut rest_args = Vec::with_capacity(rest_args_len);
    let mut rest_args_sizes = Vec::with_capacity(rest_args_len);
    for arg in rest_args_slice.iter() {
        let evaluated_arg = eval(arg, env, context)?;
        rest_args_sizes.push(evaluated_arg.size()? as u64);
        rest_args.push(SymbolicExpression::atom_value(evaluated_arg));
    }

    let (contract_identifier, type_returns_constraint) = match &args[0].expr {
        SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(
            ref contract_identifier,
        ))) => {
            // Static dispatch
            (contract_identifier, None)
        }
        SymbolicExpressionType::Atom(contract_ref) => {
            // Dynamic dispatch
            match context.lookup_callable_contract(contract_ref) {
                Some(trait_data) => {
                    // Ensure that contract-call is used for inter-contract calls only
                    if trait_data.contract_identifier == env.contract_context.contract_identifier {
                        return Err(CheckErrors::CircularReference(vec![trait_data
                            .contract_identifier
                            .name
                            .to_string()])
                        .into());
                    }

                    let contract_to_check = env
                        .global_context
                        .database
                        .get_contract(&trait_data.contract_identifier)
                        .map_err(|_e| {
                            CheckErrors::NoSuchContract(trait_data.contract_identifier.to_string())
                        })?;
                    let contract_context_to_check = contract_to_check.contract_context;

                    // This error case indicates a bad implementation. Only traits should be
                    // added to callable_contracts.
                    let trait_identifier = trait_data
                        .trait_identifier
                        .as_ref()
                        .ok_or(CheckErrors::ExpectedTraitIdentifier)?;

                    // Attempt to short circuit the dynamic dispatch checks:
                    // If the contract is explicitely implementing the trait with `impl-trait`,
                    // then we can simply rely on the analysis performed at publish time.
                    if contract_context_to_check.is_explicitly_implementing_trait(trait_identifier)
                    {
                        (&trait_data.contract_identifier, None)
                    } else {
                        let trait_name = trait_identifier.name.to_string();

                        // Retrieve, from the trait definition, the expected method signature
                        let contract_defining_trait = env
                            .global_context
                            .database
                            .get_contract(&trait_identifier.contract_identifier)
                            .map_err(|_e| {
                                CheckErrors::NoSuchContract(
                                    trait_identifier.contract_identifier.to_string(),
                                )
                            })?;
                        let contract_context_defining_trait =
                            contract_defining_trait.contract_context;

                        // Retrieve the function that will be invoked
                        let function_to_check = contract_context_to_check
                            .lookup_function(function_name)
                            .ok_or(CheckErrors::BadTraitImplementation(
                                trait_name.clone(),
                                function_name.to_string(),
                            ))?;

                        // Check read/write compatibility
                        if env.global_context.is_read_only() {
                            return Err(CheckErrors::TraitBasedContractCallInReadOnly.into());
                        }

                        // Check visibility
                        if function_to_check.define_type == DefineType::Private {
                            return Err(CheckErrors::NoSuchPublicFunction(
                                trait_data.contract_identifier.to_string(),
                                function_name.to_string(),
                            )
                            .into());
                        }

                        function_to_check.check_trait_expectations(
                            env.epoch(),
                            &contract_context_defining_trait,
                            trait_identifier,
                        )?;

                        // Retrieve the expected method signature
                        let constraining_trait = contract_context_defining_trait
                            .lookup_trait_definition(&trait_name)
                            .ok_or(CheckErrors::TraitReferenceUnknown(trait_name.clone()))?;
                        let expected_sig = constraining_trait.get(function_name).ok_or(
                            CheckErrors::TraitMethodUnknown(trait_name, function_name.to_string()),
                        )?;
                        (
                            &trait_data.contract_identifier,
                            Some(expected_sig.returns.clone()),
                        )
                    }
                }
                _ => return Err(CheckErrors::ContractCallExpectName.into()),
            }
        }
        _ => return Err(CheckErrors::ContractCallExpectName.into()),
    };

    let contract_principal = env.contract_context.contract_identifier.clone().into();

    let mut nested_env = env.nest_with_caller(contract_principal);
    let result = if nested_env.short_circuit_contract_call(
        contract_identifier,
        function_name,
        &rest_args_sizes,
    )? {
        nested_env.run_free(|free_env| {
            free_env.execute_contract(contract_identifier, function_name, &rest_args, false)
        })
    } else {
        nested_env.execute_contract(contract_identifier, function_name, &rest_args, false)
    }?;

    // sanitize contract-call outputs in epochs >= 2.4
    let result_type = TypeSignature::type_of(&result)?;
    let (result, _) = Value::sanitize_value(env.epoch(), &result_type, result)
        .ok_or_else(|| CheckErrors::CouldNotDetermineType)?;

    // Ensure that the expected type from the trait spec admits
    // the type of the value returned by the dynamic dispatch.
    if let Some(returns_type_signature) = type_returns_constraint {
        let actual_returns = TypeSignature::type_of(&result)?;
        if !returns_type_signature.admits_type(env.epoch(), &actual_returns)? {
            return Err(
                CheckErrors::ReturnTypesMustMatch(returns_type_signature, actual_returns).into(),
            );
        }
    }

    Ok(result)
}

pub fn special_fetch_variable_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    _context: &LocalContext,
) -> Result<Value> {
    check_argument_count(1, args)?;

    let var_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_var
        .get(var_name)
        .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::FetchVar,
        env,
        data_types.value_type.size()?,
    )?;

    let epoch = *env.epoch();
    env.global_context
        .database
        .lookup_variable(contract, var_name, data_types, &epoch)
}

/// The Stacks v205 version of fetch_variable uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_fetch_variable_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    _context: &LocalContext,
) -> Result<Value> {
    check_argument_count(1, args)?;

    let var_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_var
        .get(var_name)
        .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .lookup_variable_with_size(contract, var_name, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => data_types.value_type.size()? as u64,
    };

    runtime_cost(ClarityCostFunction::FetchVar, env, result_size)?;

    result.map(|data| data.value)
}

pub fn special_set_variable_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(2, args)?;

    let value = eval(&args[1], env, context)?;

    let var_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_var
        .get(var_name)
        .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::SetVar,
        env,
        data_types.value_type.size()?,
    )?;

    env.add_memory(value.get_memory_use()?)?;

    let epoch = *env.epoch();
    env.global_context
        .database
        .set_variable(contract, var_name, value, data_types, &epoch)
        .map(|data| data.value)
}

/// The Stacks v205 version of set_variable uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_set_variable_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(2, args)?;

    let value = eval(&args[1], env, context)?;

    let var_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_var
        .get(var_name)
        .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .set_variable(contract, var_name, value, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => data_types.value_type.size()? as u64,
    };

    runtime_cost(ClarityCostFunction::SetVar, env, result_size)?;

    env.add_memory(result_size)?;

    result.map(|data| data.value)
}

pub fn special_fetch_entry_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let key = eval(&args[1], env, context)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::FetchEntry,
        env,
        data_types.value_type.size()? + data_types.key_type.size()?,
    )?;

    let epoch = *env.epoch();
    env.global_context
        .database
        .fetch_entry(contract, map_name, &key, data_types, &epoch)
}

/// The Stacks v205 version of fetch_entry uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_fetch_entry_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let key = eval(&args[1], env, context)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .fetch_entry_with_size(contract, map_name, &key, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
    };

    runtime_cost(ClarityCostFunction::FetchEntry, env, result_size)?;

    result.map(|data| data.value)
}

pub fn special_at_block(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    runtime_cost(ClarityCostFunction::AtBlock, env, 0)?;

    let bhh = match eval(&args[0], env, context)? {
        Value::Sequence(SequenceData::Buffer(BuffData { data })) => {
            if data.len() != 32 {
                return Err(RuntimeErrorType::BadBlockHash(data).into());
            } else {
                StacksBlockId::from(data.as_slice())
            }
        }
        x => return Err(CheckErrors::TypeValueError(BUFF_32.clone(), x).into()),
    };

    env.add_memory(cost_constants::AT_BLOCK_MEMORY)?;
    let result = env.evaluate_at_block(bhh, &args[1], context);
    env.drop_memory(cost_constants::AT_BLOCK_MEMORY)?;

    result
}

pub fn special_set_entry_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(3, args)?;

    let key = eval(&args[1], env, context)?;

    let value = eval(&args[2], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::SetEntry,
        env,
        data_types.value_type.size()? + data_types.key_type.size()?,
    )?;

    env.add_memory(key.get_memory_use()?)?;
    env.add_memory(value.get_memory_use()?)?;

    let epoch = *env.epoch();
    env.global_context
        .database
        .set_entry(contract, map_name, key, value, data_types, &epoch)
        .map(|data| data.value)
}

/// The Stacks v205 version of set_entry uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_set_entry_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(3, args)?;

    let key = eval(&args[1], env, context)?;

    let value = eval(&args[2], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .set_entry(contract, map_name, key, value, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
    };

    runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

    env.add_memory(result_size)?;

    result.map(|data| data.value)
}

pub fn special_insert_entry_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(3, args)?;

    let key = eval(&args[1], env, context)?;

    let value = eval(&args[2], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::SetEntry,
        env,
        data_types.value_type.size()? + data_types.key_type.size()?,
    )?;

    env.add_memory(key.get_memory_use()?)?;
    env.add_memory(value.get_memory_use()?)?;

    let epoch = *env.epoch();

    env.global_context
        .database
        .insert_entry(contract, map_name, key, value, data_types, &epoch)
        .map(|data| data.value)
}

/// The Stacks v205 version of insert_entry uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_insert_entry_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(3, args)?;

    let key = eval(&args[1], env, context)?;

    let value = eval(&args[2], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .insert_entry(contract, map_name, key, value, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
    };

    runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

    env.add_memory(result_size)?;

    result.map(|data| data.value)
}

pub fn special_delete_entry_v200(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(2, args)?;

    let key = eval(&args[1], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::SetEntry,
        env,
        data_types.key_type.size()?,
    )?;

    env.add_memory(key.get_memory_use()?)?;

    let epoch = *env.epoch();
    env.global_context
        .database
        .delete_entry(contract, map_name, &key, data_types, &epoch)
        .map(|data| data.value)
}

/// The Stacks v205 version of delete_entry uses the actual stored size of the
///  value as input to the cost tabulation. Otherwise identical to v200.
pub fn special_delete_entry_v205(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into());
    }

    check_argument_count(2, args)?;

    let key = eval(&args[1], env, context)?;

    let map_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let contract = &env.contract_context.contract_identifier;

    let data_types = env
        .contract_context
        .meta_data_map
        .get(map_name)
        .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?;

    let epoch = *env.epoch();
    let result = env
        .global_context
        .database
        .delete_entry(contract, map_name, &key, data_types, &epoch);

    let result_size = match &result {
        Ok(data) => data.serialized_byte_len,
        Err(_e) => data_types.key_type.size()? as u64,
    };

    runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

    env.add_memory(result_size)?;

    result.map(|data| data.value)
}

/// Handles the `get-block-info?` special function.
/// Interprets `args` as variables `[property-name, block-height]`, and returns
/// a property value determined by `property-name`:
/// - `id-header-hash` returns the index block hash at `block-height`
/// - `header-hash` returns the header hash at `block-height`
/// - `time` returns the burn block time of the block at `block-height`
/// - `vrf-seed` returns the VRF seed of the block at `block-height`
/// - `burnchain-header-hash` returns header hash of the burnchain block corresponding to `block-height`
/// - `miner-address` returns the address of the principal that mined the block at `block-height`
/// - `miner-spend-winner` returns the number of satoshis spent by the winning miner for the block at `block-height`
/// - `miner-spend-total` returns the total number of satoshis spent by all miners for the block at `block-height`
/// - `block-reward` returns the block reward for the block at `block-height`
///
/// # Errors:
/// - CheckErrors::IncorrectArgumentCount if there aren't 2 arguments.
/// - CheckErrors::GetStacksBlockInfoExpectPropertyName if `args[0]` isn't a ClarityName.
/// - CheckErrors::NoSuchStacksBlockInfoProperty if `args[0]` isn't a StacksBlockInfoProperty.
/// - CheckErrors::TypeValueError if `args[1]` isn't a `uint`.
pub fn special_get_block_info(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    // (get-block-info? property-name block-height-uint)
    runtime_cost(ClarityCostFunction::BlockInfo, env, 0)?;

    check_argument_count(2, args)?;

    // Handle the block property name input arg.
    let property_name = args[0]
        .match_atom()
        .ok_or(CheckErrors::GetBlockInfoExpectPropertyName)?;

    let version = env.contract_context.get_clarity_version();

    let block_info_prop = BlockInfoProperty::lookup_by_name_at_version(property_name, version)
        .ok_or(CheckErrors::GetBlockInfoExpectPropertyName)?;

    // Handle the block-height input arg clause.
    let height_eval = eval(&args[1], env, context)?;
    let height_value = match height_eval {
        Value::UInt(result) => Ok(result),
        x => Err(CheckErrors::TypeValueError(TypeSignature::UIntType, x)),
    }?;

    let height_value = match u32::try_from(height_value) {
        Ok(result) => result,
        _ => return Ok(Value::none()),
    };

    // interpret height as a tenure height IFF
    // * clarity version is less than Clarity3
    // * the evaluated epoch is geq 3.0
    // * we are not on (classic) primary testnet
    let interpret_height_as_tenure_height = env.contract_context.get_clarity_version()
        < &ClarityVersion::Clarity3
        && env.global_context.epoch_id >= StacksEpochId::Epoch30
        && env.global_context.chain_id != CHAIN_ID_TESTNET;

    let height_value = if !interpret_height_as_tenure_height {
        height_value
    } else {
        // interpretting height_value as a tenure height
        let height_opt = env
            .global_context
            .database
            .get_block_height_for_tenure_height(height_value)?;
        match height_opt {
            Some(x) => x,
            None => return Ok(Value::none()),
        }
    };

    let current_block_height = env.global_context.database.get_current_block_height();
    if height_value >= current_block_height {
        return Ok(Value::none());
    }

    let result = match block_info_prop {
        BlockInfoProperty::Time => {
            let block_time = env
                .global_context
                .database
                .get_burn_block_time(height_value, None)?;
            Value::UInt(u128::from(block_time))
        }
        BlockInfoProperty::VrfSeed => {
            let vrf_seed = env
                .global_context
                .database
                .get_block_vrf_seed(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: vrf_seed.as_bytes().to_vec(),
            }))
        }
        BlockInfoProperty::HeaderHash => {
            let header_hash = env
                .global_context
                .database
                .get_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: header_hash.as_bytes().to_vec(),
            }))
        }
        BlockInfoProperty::BurnchainHeaderHash => {
            let burnchain_header_hash = env
                .global_context
                .database
                .get_burnchain_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: burnchain_header_hash.as_bytes().to_vec(),
            }))
        }
        BlockInfoProperty::IdentityHeaderHash => {
            let id_header_hash = env
                .global_context
                .database
                .get_index_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: id_header_hash.as_bytes().to_vec(),
            }))
        }
        BlockInfoProperty::MinerAddress => {
            let miner_address = env
                .global_context
                .database
                .get_miner_address(height_value)?;
            Value::from(miner_address)
        }
        BlockInfoProperty::MinerSpendWinner => {
            let winner_spend = env
                .global_context
                .database
                .get_miner_spend_winner(height_value)?;
            Value::UInt(winner_spend)
        }
        BlockInfoProperty::MinerSpendTotal => {
            let total_spend = env
                .global_context
                .database
                .get_miner_spend_total(height_value)?;
            Value::UInt(total_spend)
        }
        BlockInfoProperty::BlockReward => {
            // this is already an optional
            let block_reward_opt = env.global_context.database.get_block_reward(height_value)?;
            return Ok(match block_reward_opt {
                Some(x) => Value::some(Value::UInt(x))?,
                None => Value::none(),
            });
        }
    };

    Value::some(result)
}

/// Handles the `get-burn-block-info?` special function.
/// Interprets `args` as variables `[property_name, burn_block_height]`, and returns
/// a property value determined by `property_name`:
/// - `header_hash` returns the burn block header hash at `burn_block_height`
/// - `pox_addrs` returns the list of PoX addresses paid out at `burn_block_height`
///
/// # Errors:
/// - CheckErrors::IncorrectArgumentCount if there aren't 2 arguments.
/// - CheckErrors::GetBlockInfoExpectPropertyName if `args[0]` isn't a ClarityName.
/// - CheckErrors::NoSuchBurnBlockInfoProperty if `args[0]` isn't a BurnBlockInfoProperty.
/// - CheckErrors::TypeValueError if `args[1]` isn't a `uint`.
pub fn special_get_burn_block_info(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    runtime_cost(ClarityCostFunction::GetBurnBlockInfo, env, 0)?;

    check_argument_count(2, args)?;

    // Handle the block property name input arg.
    let property_name = args[0]
        .match_atom()
        .ok_or(CheckErrors::GetBlockInfoExpectPropertyName)?;

    let block_info_prop = BurnBlockInfoProperty::lookup_by_name(property_name).ok_or(
        CheckErrors::NoSuchBurnBlockInfoProperty(property_name.to_string()),
    )?;

    // Handle the block-height input arg clause.
    let height_eval = eval(&args[1], env, context)?;
    let height_value = match height_eval {
        Value::UInt(result) => result,
        x => {
            return Err(CheckErrors::TypeValueError(TypeSignature::UIntType, x).into());
        }
    };

    // Note: We assume that we will not have a height bigger than u32::MAX.
    let Ok(height_value) = u32::try_from(height_value) else {
        return Ok(Value::none());
    };

    match block_info_prop {
        BurnBlockInfoProperty::HeaderHash => {
            let burnchain_header_hash_opt = env
                .global_context
                .database
                .get_burnchain_block_header_hash_for_burnchain_height(height_value)?;

            match burnchain_header_hash_opt {
                Some(burnchain_header_hash) => {
                    Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                        data: burnchain_header_hash.as_bytes().to_vec(),
                    })))
                }
                None => Ok(Value::none()),
            }
        }
        BurnBlockInfoProperty::PoxAddrs => {
            let pox_addrs_and_payout = env
                .global_context
                .database
                .get_pox_payout_addrs_for_burnchain_height(height_value)?;

            match pox_addrs_and_payout {
                Some((addrs, payout)) => Ok(Value::some(Value::Tuple(
                    TupleData::from_data(vec![
                        (
                            "addrs".into(),
                            Value::cons_list(
                                addrs.into_iter().map(Value::Tuple).collect(),
                                env.epoch(),
                            )
                            .map_err(|_| {
                                InterpreterError::Expect(
                                    "FATAL: could not convert address list to Value".into(),
                                )
                            })?,
                        ),
                        ("payout".into(), Value::UInt(payout)),
                    ])
                    .map_err(|_| {
                        InterpreterError::Expect(
                            "FATAL: failed to build pox addrs and payout tuple".into(),
                        )
                    })?,
                ))
                .map_err(|_| InterpreterError::Expect("FATAL: could not build Some(..)".into()))?),
                None => Ok(Value::none()),
            }
        }
    }
}

/// Handles the `get-stacks-block-info?` special function.
/// Interprets `args` as variables `[property-name, block-height]`, and returns
/// a property value determined by `property-name`:
/// - `id-header-hash` returns the index block hash at `block-height`
/// - `header-hash` returns the header hash at `block-height`
/// - `time` returns the block time at `block-height`
///
/// # Errors:
/// - CheckErrors::IncorrectArgumentCount if there aren't 2 arguments.
/// - CheckErrors::GetStacksBlockInfoExpectPropertyName if `args[0]` isn't a ClarityName.
/// - CheckErrors::NoSuchStacksBlockInfoProperty if `args[0]` isn't a StacksBlockInfoProperty.
/// - CheckErrors::TypeValueError if `args[1]` isn't a `uint`.
pub fn special_get_stacks_block_info(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    // (get-stacks-block-info? property-name block-height-uint)
    runtime_cost(ClarityCostFunction::BlockInfo, env, 0)?;

    check_argument_count(2, args)?;

    // Handle the block property name input arg.
    let property_name = args[0]
        .match_atom()
        .ok_or(CheckErrors::GetStacksBlockInfoExpectPropertyName)?;

    let block_info_prop = StacksBlockInfoProperty::lookup_by_name(property_name).ok_or(
        CheckErrors::NoSuchStacksBlockInfoProperty(property_name.to_string()),
    )?;

    // Handle the block-height input arg.
    let height_eval = eval(&args[1], env, context)?;
    let height_value = match height_eval {
        Value::UInt(result) => Ok(result),
        x => Err(CheckErrors::TypeValueError(TypeSignature::UIntType, x)),
    }?;

    let Ok(height_value) = u32::try_from(height_value) else {
        return Ok(Value::none());
    };

    let current_block_height = env.global_context.database.get_current_block_height();
    if height_value >= current_block_height {
        return Ok(Value::none());
    }

    let result = match block_info_prop {
        StacksBlockInfoProperty::Time => {
            let block_time = env.global_context.database.get_block_time(height_value)?;
            Value::UInt(u128::from(block_time))
        }
        StacksBlockInfoProperty::HeaderHash => {
            let header_hash = env
                .global_context
                .database
                .get_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: header_hash.as_bytes().to_vec(),
            }))
        }
        StacksBlockInfoProperty::IndexHeaderHash => {
            let id_header_hash = env
                .global_context
                .database
                .get_index_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: id_header_hash.as_bytes().to_vec(),
            }))
        }
    };

    Value::some(result)
}

/// Handles the function `get-tenure-info?` special function.
/// Interprets `args` as variables `[property-name, block-height]`, and returns
/// a property value determined by `property-name`:
/// - `time` returns the burn block time for the tenure of which `block-height` is a part
/// - `vrf-seed` returns the VRF seed for the tenure of which `block-height` is a part
/// - `burnchain-header-hash` returns header hash of the burnchain block corresponding to the tenure of which `block-height` is a part
/// - `miner-address` returns the address of the principal that mined the tenure of which `block-height` is a part
/// - `miner-spend-winner` returns the number of satoshis spent by the winning miner for the tenure of which `block-height` is a part
/// - `miner-spend-total` returns the total number of satoshis spent by all miners for the tenure of which `block-height` is a part
/// - `block-reward` returns the block reward for the tenure of which `block-height` is a part
///
/// # Errors:
/// - CheckErrors::IncorrectArgumentCount if there aren't 2 arguments.
/// - CheckErrors::GetTenureInfoExpectPropertyName if `args[0]` isn't a ClarityName.
/// - CheckErrors::NoSuchTenureInfoProperty if `args[0]` isn't a TenureInfoProperty.
/// - CheckErrors::TypeValueError if `args[1]` isn't a `uint`.
pub fn special_get_tenure_info(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    // (get-tenure-info? property-name block-height-uint)
    runtime_cost(ClarityCostFunction::BlockInfo, env, 0)?;

    check_argument_count(2, args)?;

    // Handle the block property name input arg.
    let property_name = args[0]
        .match_atom()
        .ok_or(CheckErrors::GetTenureInfoExpectPropertyName)?;

    let block_info_prop = TenureInfoProperty::lookup_by_name(property_name)
        .ok_or(CheckErrors::GetTenureInfoExpectPropertyName)?;

    // Handle the block-height input arg.
    let height_eval = eval(&args[1], env, context)?;
    let height_value = match height_eval {
        Value::UInt(result) => Ok(result),
        x => Err(CheckErrors::TypeValueError(TypeSignature::UIntType, x)),
    }?;

    let Ok(height_value) = u32::try_from(height_value) else {
        return Ok(Value::none());
    };

    let current_height = env.global_context.database.get_current_block_height();
    if height_value >= current_height {
        return Ok(Value::none());
    }

    let result = match block_info_prop {
        TenureInfoProperty::Time => {
            let block_time = env
                .global_context
                .database
                .get_burn_block_time(height_value, None)?;
            Value::UInt(u128::from(block_time))
        }
        TenureInfoProperty::VrfSeed => {
            let vrf_seed = env
                .global_context
                .database
                .get_block_vrf_seed(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: vrf_seed.as_bytes().to_vec(),
            }))
        }
        TenureInfoProperty::BurnchainHeaderHash => {
            let burnchain_header_hash = env
                .global_context
                .database
                .get_burnchain_block_header_hash(height_value)?;
            Value::Sequence(SequenceData::Buffer(BuffData {
                data: burnchain_header_hash.as_bytes().to_vec(),
            }))
        }
        TenureInfoProperty::MinerAddress => {
            let miner_address = env
                .global_context
                .database
                .get_miner_address(height_value)?;
            Value::from(miner_address)
        }
        TenureInfoProperty::MinerSpendWinner => {
            let winner_spend = env
                .global_context
                .database
                .get_miner_spend_winner(height_value)?;
            Value::UInt(winner_spend)
        }
        TenureInfoProperty::MinerSpendTotal => {
            let total_spend = env
                .global_context
                .database
                .get_miner_spend_total(height_value)?;
            Value::UInt(total_spend)
        }
        TenureInfoProperty::BlockReward => {
            // this is already an optional
            let block_reward_opt = env.global_context.database.get_block_reward(height_value)?;
            return Ok(match block_reward_opt {
                Some(x) => Value::some(Value::UInt(x))?,
                None => Value::none(),
            });
        }
    };

    Value::some(result)
}
