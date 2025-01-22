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
#![allow(clippy::result_large_err)]

pub mod diagnostic;
pub mod errors;

#[macro_use]
pub mod costs;

pub mod types;

pub mod contracts;

#[cfg(feature = "clarity-wasm")]
pub mod clarity_wasm;

pub mod ast;
pub mod contexts;
pub mod database;
pub mod representations;

pub mod callables;
pub mod functions;
pub mod variables;

pub mod analysis;
pub mod docs;
pub mod version;

pub mod coverage;

pub mod events;

#[cfg(feature = "canonical")]
pub mod tooling;

#[cfg(any(test, feature = "testing"))]
pub mod tests;

#[cfg(any(test, feature = "testing"))]
pub mod test_util;

pub mod clarity;

use std::collections::BTreeMap;

use serde_json;
use stacks_common::types::StacksEpochId;

use self::analysis::ContractAnalysis;
use self::ast::{ASTRules, ContractAST};
use self::costs::ExecutionCost;
use self::diagnostic::Diagnostic;
use self::events::StacksTransactionEvent;
use crate::vm::callables::CallableType;
use crate::vm::contexts::GlobalContext;
pub use crate::vm::contexts::{
    CallStack, ContractContext, Environment, LocalContext, MAX_CONTEXT_DEPTH,
};
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::{
    cost_functions, runtime_cost, CostOverflowingMath, CostTracker, LimitedCostTracker,
    MemoryConsumer,
};
// publish the non-generic StacksEpoch form for use throughout module
pub use crate::vm::database::clarity_db::StacksEpoch;
use crate::vm::errors::{
    CheckErrors, Error, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};
use crate::vm::functions::define::DefineResult;
pub use crate::vm::functions::stx_transfer_consolidated;
pub use crate::vm::representations::{
    ClarityName, ContractName, SymbolicExpression, SymbolicExpressionType,
};
pub use crate::vm::types::Value;
use crate::vm::types::{
    PrincipalData, QualifiedContractIdentifier, TraitIdentifier, TypeSignature,
};
pub use crate::vm::version::ClarityVersion;

pub const MAX_CALL_STACK_DEPTH: usize = 64;

#[derive(Debug, Clone)]
pub struct ParsedContract {
    pub contract_identifier: String,
    pub code: String,
    pub function_args: BTreeMap<String, Vec<String>>,
    pub ast: ContractAST,
    pub analysis: ContractAnalysis,
}

#[derive(Debug, Clone)]
pub struct ContractEvaluationResult {
    pub result: Option<Value>,
    pub contract: ParsedContract,
}

#[derive(Debug, Clone)]
pub struct SnippetEvaluationResult {
    pub result: Value,
}

#[derive(Debug, Clone)]
pub enum EvaluationResult {
    Contract(ContractEvaluationResult),
    Snippet(SnippetEvaluationResult),
}

#[derive(Debug, Clone)]
pub struct ExecutionResult {
    pub result: EvaluationResult,
    pub events: Vec<StacksTransactionEvent>,
    pub cost: Option<CostSynthesis>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CostSynthesis {
    pub total: ExecutionCost,
    pub limit: ExecutionCost,
    pub memory: u64,
    pub memory_limit: u64,
}

impl CostSynthesis {
    pub fn from_cost_tracker(cost_tracker: &LimitedCostTracker) -> CostSynthesis {
        CostSynthesis {
            total: cost_tracker.get_total(),
            limit: cost_tracker.get_limit(),
            memory: cost_tracker.get_memory(),
            memory_limit: cost_tracker.get_memory_limit(),
        }
    }
}

/// EvalHook defines an interface for hooks to execute during evaluation.
pub trait EvalHook {
    // Called before the expression is evaluated
    fn will_begin_eval(
        &mut self,
        _env: &mut Environment,
        _context: &LocalContext,
        _expr: &SymbolicExpression,
    );

    // Called after the expression is evaluated
    fn did_finish_eval(
        &mut self,
        _env: &mut Environment,
        _context: &LocalContext,
        _expr: &SymbolicExpression,
        _res: &core::result::Result<Value, crate::vm::errors::Error>,
    );

    // Called upon completion of the execution
    fn did_complete(&mut self, _result: core::result::Result<&mut ExecutionResult, String>);
}

fn lookup_variable(name: &str, context: &LocalContext, env: &mut Environment) -> Result<Value> {
    if name.starts_with(char::is_numeric) || name.starts_with('\'') {
        Err(InterpreterError::BadSymbolicRepresentation(format!(
            "Unexpected variable name: {}",
            name
        ))
        .into())
    } else if let Some(value) = variables::lookup_reserved_variable(name, context, env)? {
        Ok(value)
    } else {
        runtime_cost(
            ClarityCostFunction::LookupVariableDepth,
            env,
            context.depth(),
        )?;
        if let Some(value) = context.lookup_variable(name) {
            runtime_cost(ClarityCostFunction::LookupVariableSize, env, value.size()?)?;
            Ok(value.clone())
        } else if let Some(value) = env.contract_context.lookup_variable(name).cloned() {
            runtime_cost(ClarityCostFunction::LookupVariableSize, env, value.size()?)?;
            let (value, _) =
                Value::sanitize_value(env.epoch(), &TypeSignature::type_of(&value)?, value)
                    .ok_or_else(|| CheckErrors::CouldNotDetermineType)?;
            Ok(value)
        } else if let Some(callable_data) = context.lookup_callable_contract(name) {
            if env.contract_context.get_clarity_version() < &ClarityVersion::Clarity2 {
                Ok(callable_data.contract_identifier.clone().into())
            } else {
                Ok(Value::CallableContract(callable_data.clone()))
            }
        } else {
            Err(CheckErrors::UndefinedVariable(name.to_string()).into())
        }
    }
}

pub fn lookup_function(name: &str, env: &mut Environment) -> Result<CallableType> {
    runtime_cost(ClarityCostFunction::LookupFunction, env, 0)?;

    if let Some(result) =
        functions::lookup_reserved_functions(name, env.contract_context.get_clarity_version())
    {
        Ok(result)
    } else {
        let user_function = env
            .contract_context
            .lookup_function(name)
            .ok_or(CheckErrors::UndefinedFunction(name.to_string()))?;
        Ok(CallableType::UserFunction(user_function))
    }
}

fn add_stack_trace(result: &mut Result<Value>, env: &Environment) {
    if let Err(Error::Runtime(_, ref mut stack_trace)) = result {
        if stack_trace.is_none() {
            stack_trace.replace(env.call_stack.make_stack_trace());
        }
    }
}

pub fn apply(
    function: &CallableType,
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    let identifier = function.get_identifier();
    // Aaron: in non-debug executions, we shouldn't track a full call-stack.
    //        only enough to do recursion detection.

    // do recursion check on user functions.
    let track_recursion = matches!(function, CallableType::UserFunction(_));
    if track_recursion && env.call_stack.contains(&identifier) {
        return Err(CheckErrors::CircularReference(vec![identifier.to_string()]).into());
    }

    if env.call_stack.depth() >= MAX_CALL_STACK_DEPTH {
        return Err(RuntimeErrorType::MaxStackDepthReached.into());
    }

    if let CallableType::SpecialFunction(_, function) = function {
        env.call_stack.insert(&identifier, track_recursion);
        let mut resp = function(args, env, context);
        add_stack_trace(&mut resp, env);
        env.call_stack.remove(&identifier, track_recursion)?;
        resp
    } else {
        let mut used_memory = 0;
        let mut evaluated_args = Vec::with_capacity(args.len());
        env.call_stack.incr_apply_depth();
        for arg_x in args.iter() {
            let arg_value = match eval(arg_x, env, context) {
                Ok(x) => x,
                Err(e) => {
                    env.drop_memory(used_memory)?;
                    env.call_stack.decr_apply_depth();
                    return Err(e);
                }
            };
            let arg_use = arg_value.get_memory_use()?;
            match env.add_memory(arg_use) {
                Ok(_x) => {}
                Err(e) => {
                    env.drop_memory(used_memory)?;
                    env.call_stack.decr_apply_depth();
                    return Err(Error::from(e));
                }
            };
            used_memory += arg_value.get_memory_use()?;
            evaluated_args.push(arg_value);
        }
        env.call_stack.decr_apply_depth();

        env.call_stack.insert(&identifier, track_recursion);
        let mut resp = match function {
            CallableType::NativeFunction(_, function, cost_function) => {
                runtime_cost(*cost_function, env, evaluated_args.len())
                    .map_err(Error::from)
                    .and_then(|_| function.apply(evaluated_args, env))
            }
            CallableType::NativeFunction205(_, function, cost_function, cost_input_handle) => {
                let cost_input = if env.epoch() >= &StacksEpochId::Epoch2_05 {
                    cost_input_handle(evaluated_args.as_slice())?
                } else {
                    evaluated_args.len() as u64
                };
                runtime_cost(*cost_function, env, cost_input)
                    .map_err(Error::from)
                    .and_then(|_| function.apply(evaluated_args, env))
            }
            CallableType::UserFunction(function) => function.apply(&evaluated_args, env),
            _ => return Err(InterpreterError::Expect("Should be unreachable.".into()).into()),
        };
        add_stack_trace(&mut resp, env);
        env.drop_memory(used_memory)?;
        env.call_stack.remove(&identifier, track_recursion)?;
        resp
    }
}

pub fn eval(
    exp: &SymbolicExpression,
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    use crate::vm::representations::SymbolicExpressionType::{
        Atom, AtomValue, Field, List, LiteralValue, TraitReference,
    };

    if let Some(mut eval_hooks) = env.global_context.eval_hooks.take() {
        for hook in eval_hooks.iter_mut() {
            hook.will_begin_eval(env, context, exp);
        }
        env.global_context.eval_hooks = Some(eval_hooks);
    }

    let res = match exp.expr {
        AtomValue(ref value) | LiteralValue(ref value) => Ok(value.clone()),
        Atom(ref value) => lookup_variable(value, context, env),
        List(ref children) => {
            let (function_variable, rest) = children
                .split_first()
                .ok_or(CheckErrors::NonFunctionApplication)?;

            let function_name = function_variable
                .match_atom()
                .ok_or(CheckErrors::BadFunctionName)?;
            let f = lookup_function(function_name, env)?;
            apply(&f, rest, env, context)
        }
        TraitReference(_, _) | Field(_) => {
            return Err(InterpreterError::BadSymbolicRepresentation(
                "Unexpected trait reference".into(),
            )
            .into())
        }
    };

    if let Some(mut eval_hooks) = env.global_context.eval_hooks.take() {
        for hook in eval_hooks.iter_mut() {
            hook.did_finish_eval(env, context, exp, &res);
        }
        env.global_context.eval_hooks = Some(eval_hooks);
    }

    res
}

pub fn is_reserved(name: &str, version: &ClarityVersion) -> bool {
    functions::lookup_reserved_functions(name, version).is_some()
        || variables::is_reserved_name(name, version)
}

/// This function evaluates a list of expressions, sharing a global context.
/// It returns the final evaluated result.
/// Used for the initialization of a new contract.
pub fn eval_all(
    expressions: &[SymbolicExpression],
    contract_context: &mut ContractContext,
    global_context: &mut GlobalContext,
    sponsor: Option<PrincipalData>,
) -> Result<Option<Value>> {
    let mut last_executed = None;
    let context = LocalContext::new();
    let mut total_memory_use = 0;

    let publisher: PrincipalData = contract_context.contract_identifier.issuer.clone().into();

    finally_drop_memory!(global_context, total_memory_use; {
        for exp in expressions {
            let try_define = global_context.execute(|context| {
                let mut call_stack = CallStack::new();
                let mut env = Environment::new(
                    context, contract_context, &mut call_stack, Some(publisher.clone()), Some(publisher.clone()), sponsor.clone());
                functions::define::evaluate_define(exp, &mut env)
            })?;
            match try_define {
                DefineResult::Variable(name, value) => {
                    runtime_cost(ClarityCostFunction::BindName, global_context, 0)?;
                    let value_memory_use = value.get_memory_use()?;
                    global_context.add_memory(value_memory_use)?;
                    total_memory_use += value_memory_use;

                    contract_context.variables.insert(name, value);
                },
                DefineResult::Function(name, value) => {
                    runtime_cost(ClarityCostFunction::BindName, global_context, 0)?;

                    contract_context.functions.insert(name, value);
                },
                DefineResult::PersistedVariable(name, value_type, value) => {
                    runtime_cost(ClarityCostFunction::CreateVar, global_context, value_type.size()?)?;
                    contract_context.persisted_names.insert(name.clone());

                    global_context.add_memory(value_type.type_size()
                                              .map_err(|_| InterpreterError::Expect("Type size should be realizable".into()))? as u64)?;

                    global_context.add_memory(value.size()? as u64)?;

                    let data_type = global_context.database.create_variable(&contract_context.contract_identifier, &name, value_type)?;
                    global_context.database.set_variable(&contract_context.contract_identifier, &name, value, &data_type, &global_context.epoch_id)?;

                    contract_context.meta_data_var.insert(name, data_type);
                },
                DefineResult::Map(name, key_type, value_type) => {
                    runtime_cost(ClarityCostFunction::CreateMap, global_context,
                                  u64::from(key_type.size()?).cost_overflow_add(
                                      u64::from(value_type.size()?))?)?;
                    contract_context.persisted_names.insert(name.clone());

                    global_context.add_memory(key_type.type_size()
                                              .map_err(|_| InterpreterError::Expect("Type size should be realizable".into()))? as u64)?;
                    global_context.add_memory(value_type.type_size()
                                              .map_err(|_| InterpreterError::Expect("Type size should be realizable".into()))? as u64)?;

                    let data_type = global_context.database.create_map(&contract_context.contract_identifier, &name, key_type, value_type)?;

                    contract_context.meta_data_map.insert(name, data_type);
                },
                DefineResult::FungibleToken(name, total_supply) => {
                    runtime_cost(ClarityCostFunction::CreateFt, global_context, 0)?;
                    contract_context.persisted_names.insert(name.clone());

                    global_context.add_memory(TypeSignature::UIntType.type_size()
                                              .map_err(|_| InterpreterError::Expect("Type size should be realizable".into()))? as u64)?;

                    let data_type = global_context.database.create_fungible_token(&contract_context.contract_identifier, &name, &total_supply)?;

                    contract_context.meta_ft.insert(name, data_type);
                },
                DefineResult::NonFungibleAsset(name, asset_type) => {
                    runtime_cost(ClarityCostFunction::CreateNft, global_context, asset_type.size()?)?;
                    contract_context.persisted_names.insert(name.clone());

                    global_context.add_memory(asset_type.type_size()
                                              .map_err(|_| InterpreterError::Expect("Type size should be realizable".into()))? as u64)?;

                    let data_type = global_context.database.create_non_fungible_token(&contract_context.contract_identifier, &name, &asset_type)?;

                    contract_context.meta_nft.insert(name, data_type);
                },
                DefineResult::Trait(name, trait_type) => {
                    contract_context.defined_traits.insert(name, trait_type);
                },
                DefineResult::UseTrait(_name, _trait_identifier) => {},
                DefineResult::ImplTrait(trait_identifier) => {
                    contract_context.implemented_traits.insert(trait_identifier);
                },
                DefineResult::NoDefine => {
                    // not a define function, evaluate normally.
                    global_context.execute(|global_context| {
                        let mut call_stack = CallStack::new();
                        let mut env = Environment::new(
                            global_context, contract_context, &mut call_stack, Some(publisher.clone()), Some(publisher.clone()), sponsor.clone());

                        let result = eval(exp, &mut env, &context)?;
                        last_executed = Some(result);
                        Ok(())
                    })?;
                }
            }
        }

        contract_context.data_size = total_memory_use;
        Ok(last_executed)
    })
}

/// Run provided program in a brand new environment, with a transient, empty
/// database. Only used for testing
/// This method executes the program in Epoch 2.0 *and* Epoch 2.05 and asserts
/// that the result is the same before returning the result
#[cfg(any(test, feature = "testing"))]
pub fn execute_on_network(program: &str, use_mainnet: bool) -> Result<Option<Value>> {
    let epoch_200_result = execute_with_parameters(
        program,
        ClarityVersion::Clarity2,
        StacksEpochId::Epoch20,
        ast::ASTRules::PrecheckSize,
        use_mainnet,
    );
    let epoch_205_result = execute_with_parameters(
        program,
        ClarityVersion::Clarity2,
        StacksEpochId::Epoch2_05,
        ast::ASTRules::PrecheckSize,
        use_mainnet,
    );

    assert_eq!(
        epoch_200_result, epoch_205_result,
        "Epoch 2.0 and 2.05 should have same execution result, but did not for program `{}`",
        program
    );
    epoch_205_result
}

/// Runs `program` in a test environment with the provided parameters.
#[cfg(any(test, feature = "testing"))]
pub fn execute_with_parameters(
    program: &str,
    clarity_version: ClarityVersion,
    epoch: StacksEpochId,
    ast_rules: ast::ASTRules,
    use_mainnet: bool,
) -> Result<Option<Value>> {
    use crate::vm::database::MemoryBackingStore;
    use crate::vm::tests::test_only_mainnet_to_chain_id;

    let contract_id = QualifiedContractIdentifier::transient();
    let mut contract_context = ContractContext::new(contract_id.clone(), clarity_version);
    let mut marf = MemoryBackingStore::new();
    let conn = marf.as_clarity_db();
    let chain_id = test_only_mainnet_to_chain_id(use_mainnet);
    let mut global_context = GlobalContext::new(
        use_mainnet,
        chain_id,
        conn,
        LimitedCostTracker::new_free(),
        epoch,
    );
    global_context.execute(|g| {
        let parsed = ast::build_ast_with_rules(
            &contract_id,
            program,
            &mut (),
            clarity_version,
            epoch,
            ast_rules,
        )?
        .expressions;
        eval_all(&parsed, &mut contract_context, g, None)
    })
}

/// Execute for test with `version`, Epoch20, testnet.
#[cfg(any(test, feature = "testing"))]
pub fn execute_against_version(program: &str, version: ClarityVersion) -> Result<Option<Value>> {
    execute_with_parameters(
        program,
        version,
        StacksEpochId::Epoch20,
        ast::ASTRules::PrecheckSize,
        false,
    )
}

/// Execute for test in Clarity1, Epoch20, testnet.
#[cfg(any(test, feature = "testing"))]
pub fn execute(program: &str) -> Result<Option<Value>> {
    execute_with_parameters(
        program,
        ClarityVersion::Clarity1,
        StacksEpochId::Epoch20,
        ast::ASTRules::PrecheckSize,
        false,
    )
}

/// Execute for test in Clarity2, Epoch21, testnet.
#[cfg(any(test, feature = "testing"))]
pub fn execute_v2(program: &str) -> Result<Option<Value>> {
    execute_with_parameters(
        program,
        ClarityVersion::Clarity2,
        StacksEpochId::Epoch21,
        ASTRules::PrecheckSize,
        false,
    )
}

#[cfg(test)]
mod test {
    use hashbrown::HashMap;
    use stacks_common::consts::CHAIN_ID_TESTNET;
    use stacks_common::types::StacksEpochId;

    use super::ClarityVersion;
    use crate::vm::callables::{DefineType, DefinedFunction};
    use crate::vm::costs::LimitedCostTracker;
    use crate::vm::database::MemoryBackingStore;
    use crate::vm::errors::RuntimeErrorType;
    use crate::vm::types::{QualifiedContractIdentifier, TypeSignature};
    use crate::vm::{
        eval, execute, CallStack, ContractContext, Environment, GlobalContext, LocalContext,
        SymbolicExpression, Value,
    };

    #[test]
    fn test_simple_user_function() {
        //
        //  test program:
        //  (define (do_work x) (+ 5 x))
        //  (define a 59)
        //  (do_work a)
        //
        let content = [SymbolicExpression::list(vec![
            SymbolicExpression::atom("do_work".into()),
            SymbolicExpression::atom("a".into()),
        ])];

        let func_body = SymbolicExpression::list(vec![
            SymbolicExpression::atom("+".into()),
            SymbolicExpression::atom_value(Value::Int(5)),
            SymbolicExpression::atom("x".into()),
        ]);

        let func_args = vec![("x".into(), TypeSignature::IntType)];
        let user_function = DefinedFunction::new(
            func_args,
            func_body,
            DefineType::Private,
            &"do_work".into(),
            "",
            Some(TypeSignature::IntType),
        );

        let context = LocalContext::new();
        let mut contract_context = ContractContext::new(
            QualifiedContractIdentifier::transient(),
            ClarityVersion::Clarity1,
        );

        let mut marf = MemoryBackingStore::new();
        let mut global_context = GlobalContext::new(
            false,
            CHAIN_ID_TESTNET,
            marf.as_clarity_db(),
            LimitedCostTracker::new_free(),
            StacksEpochId::Epoch2_05,
        );

        contract_context
            .variables
            .insert("a".into(), Value::Int(59));
        contract_context
            .functions
            .insert("do_work".into(), user_function);

        let mut call_stack = CallStack::new();
        let mut env = Environment::new(
            &mut global_context,
            &contract_context,
            &mut call_stack,
            None,
            None,
            None,
        );
        assert_eq!(Ok(Value::Int(64)), eval(&content[0], &mut env, &context));
    }
}
