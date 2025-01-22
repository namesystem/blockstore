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

use std::collections::BTreeMap;

use crate::vm::callables::{DefineType, DefinedFunction};
use crate::vm::contexts::{ContractContext, Environment, LocalContext};
use crate::vm::errors::{
    check_argument_count, check_arguments_at_least, CheckErrors, InterpreterResult as Result,
    RuntimeErrorType,
};
use crate::vm::eval;
use crate::vm::representations::SymbolicExpressionType::{
    Atom, AtomValue, Field, List, LiteralValue,
};
use crate::vm::representations::{ClarityName, SymbolicExpression};
use crate::vm::types::signatures::FunctionSignature;
use crate::vm::types::{
    parse_name_type_pairs, PrincipalData, QualifiedContractIdentifier, TraitIdentifier,
    TupleTypeSignature, TypeSignature, Value,
};

define_named_enum!(DefineFunctions {
    Constant("define-constant"),
    PrivateFunction("define-private"),
    PublicFunction("define-public"),
    ReadOnlyFunction("define-read-only"),
    Map("define-map"),
    PersistedVariable("define-data-var"),
    FungibleToken("define-fungible-token"),
    NonFungibleToken("define-non-fungible-token"),
    Trait("define-trait"),
    UseTrait("use-trait"),
    ImplTrait("impl-trait"),
});

pub enum DefineFunctionsParsed<'a> {
    Constant {
        name: &'a ClarityName,
        value: &'a SymbolicExpression,
    },
    PrivateFunction {
        signature: &'a [SymbolicExpression],
        body: &'a SymbolicExpression,
    },
    ReadOnlyFunction {
        signature: &'a [SymbolicExpression],
        body: &'a SymbolicExpression,
    },
    PublicFunction {
        signature: &'a [SymbolicExpression],
        body: &'a SymbolicExpression,
    },
    NonFungibleToken {
        name: &'a ClarityName,
        nft_type: &'a SymbolicExpression,
    },
    BoundedFungibleToken {
        name: &'a ClarityName,
        max_supply: &'a SymbolicExpression,
    },
    UnboundedFungibleToken {
        name: &'a ClarityName,
    },
    Map {
        name: &'a ClarityName,
        key_type: &'a SymbolicExpression,
        value_type: &'a SymbolicExpression,
    },
    PersistedVariable {
        name: &'a ClarityName,
        data_type: &'a SymbolicExpression,
        initial: &'a SymbolicExpression,
    },
    Trait {
        name: &'a ClarityName,
        functions: &'a [SymbolicExpression],
    },
    UseTrait {
        name: &'a ClarityName,
        trait_identifier: &'a TraitIdentifier,
    },
    ImplTrait {
        trait_identifier: &'a TraitIdentifier,
    },
}

pub enum DefineResult {
    Variable(ClarityName, Value),
    Function(ClarityName, DefinedFunction),
    Map(ClarityName, TypeSignature, TypeSignature),
    PersistedVariable(ClarityName, TypeSignature, Value),
    FungibleToken(ClarityName, Option<u128>),
    NonFungibleAsset(ClarityName, TypeSignature),
    Trait(ClarityName, BTreeMap<ClarityName, FunctionSignature>),
    UseTrait(ClarityName, TraitIdentifier),
    ImplTrait(TraitIdentifier),
    NoDefine,
}

fn check_legal_define(name: &str, contract_context: &ContractContext) -> Result<()> {
    if contract_context.is_name_used(name) {
        Err(CheckErrors::NameAlreadyUsed(name.to_string()).into())
    } else {
        Ok(())
    }
}

fn handle_define_variable(
    variable: &ClarityName,
    expression: &SymbolicExpression,
    env: &mut Environment,
) -> Result<DefineResult> {
    // is the variable name legal?
    check_legal_define(variable, env.contract_context)?;
    let context = LocalContext::new();
    let value = eval(expression, env, &context)?;
    Ok(DefineResult::Variable(variable.clone(), value))
}

fn handle_define_function(
    signature: &[SymbolicExpression],
    expression: &SymbolicExpression,
    env: &mut Environment,
    define_type: DefineType,
) -> Result<DefineResult> {
    let (function_symbol, arg_symbols) = signature
        .split_first()
        .ok_or(CheckErrors::DefineFunctionBadSignature)?;

    let function_name = function_symbol
        .match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    check_legal_define(function_name, env.contract_context)?;

    let arguments = parse_name_type_pairs(*env.epoch(), arg_symbols, env)?;

    for (argument, _) in arguments.iter() {
        check_legal_define(argument, env.contract_context)?;
    }

    let function = DefinedFunction::new(
        arguments,
        expression.clone(),
        define_type,
        function_name,
        &env.contract_context.contract_identifier.to_string(),
        None,
    );

    Ok(DefineResult::Function(function_name.clone(), function))
}

fn handle_define_persisted_variable(
    variable_str: &ClarityName,
    value_type: &SymbolicExpression,
    value: &SymbolicExpression,
    env: &mut Environment,
) -> Result<DefineResult> {
    check_legal_define(variable_str, env.contract_context)?;

    let value_type_signature = TypeSignature::parse_type_repr(*env.epoch(), value_type, env)?;

    let context = LocalContext::new();
    let value = eval(value, env, &context)?;

    Ok(DefineResult::PersistedVariable(
        variable_str.clone(),
        value_type_signature,
        value,
    ))
}

fn handle_define_nonfungible_asset(
    asset_name: &ClarityName,
    key_type: &SymbolicExpression,
    env: &mut Environment,
) -> Result<DefineResult> {
    check_legal_define(asset_name, env.contract_context)?;

    let key_type_signature = TypeSignature::parse_type_repr(*env.epoch(), key_type, env)?;

    Ok(DefineResult::NonFungibleAsset(
        asset_name.clone(),
        key_type_signature,
    ))
}

fn handle_define_fungible_token(
    asset_name: &ClarityName,
    total_supply: Option<&SymbolicExpression>,
    env: &mut Environment,
) -> Result<DefineResult> {
    check_legal_define(asset_name, env.contract_context)?;

    if let Some(total_supply_expr) = total_supply {
        let context = LocalContext::new();
        let total_supply_value = eval(total_supply_expr, env, &context)?;
        if let Value::UInt(total_supply_int) = total_supply_value {
            Ok(DefineResult::FungibleToken(
                asset_name.clone(),
                Some(total_supply_int),
            ))
        } else {
            Err(CheckErrors::TypeValueError(TypeSignature::UIntType, total_supply_value).into())
        }
    } else {
        Ok(DefineResult::FungibleToken(asset_name.clone(), None))
    }
}

fn handle_define_map(
    map_str: &ClarityName,
    key_type: &SymbolicExpression,
    value_type: &SymbolicExpression,
    env: &mut Environment,
) -> Result<DefineResult> {
    check_legal_define(map_str, env.contract_context)?;

    let key_type_signature = TypeSignature::parse_type_repr(*env.epoch(), key_type, env)?;
    let value_type_signature = TypeSignature::parse_type_repr(*env.epoch(), value_type, env)?;

    Ok(DefineResult::Map(
        map_str.clone(),
        key_type_signature,
        value_type_signature,
    ))
}

fn handle_define_trait(
    name: &ClarityName,
    functions: &[SymbolicExpression],
    env: &mut Environment,
) -> Result<DefineResult> {
    check_legal_define(name, env.contract_context)?;

    let trait_signature = TypeSignature::parse_trait_type_repr(
        functions,
        env,
        *env.epoch(),
        *env.contract_context.get_clarity_version(),
    )?;

    Ok(DefineResult::Trait(name.clone(), trait_signature))
}

fn handle_use_trait(
    name: &ClarityName,
    trait_identifier: &TraitIdentifier,
) -> Result<DefineResult> {
    Ok(DefineResult::UseTrait(
        name.clone(),
        trait_identifier.clone(),
    ))
}

fn handle_impl_trait(trait_identifier: &TraitIdentifier) -> Result<DefineResult> {
    Ok(DefineResult::ImplTrait(trait_identifier.clone()))
}

impl DefineFunctions {
    pub fn try_parse(
        expression: &SymbolicExpression,
    ) -> Option<(DefineFunctions, &[SymbolicExpression])> {
        let expression = expression.match_list()?;
        let (function_name, args) = expression.split_first()?;
        let function_name = function_name.match_atom()?;
        let define_type = DefineFunctions::lookup_by_name(function_name)?;
        Some((define_type, args))
    }
}

impl<'a> DefineFunctionsParsed<'a> {
    /// Try to parse a Top-Level Expression (e.g., (define-private (foo) 1)) as
    /// a define-statement, returns None if the supplied expression is not a define.
    pub fn try_parse(
        expression: &'a SymbolicExpression,
    ) -> std::result::Result<Option<DefineFunctionsParsed<'a>>, CheckErrors> {
        let (define_type, args) = match DefineFunctions::try_parse(expression) {
            Some(x) => x,
            None => return Ok(None),
        };
        let result = match define_type {
            DefineFunctions::Constant => {
                check_argument_count(2, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                DefineFunctionsParsed::Constant {
                    name,
                    value: &args[1],
                }
            }
            DefineFunctions::PrivateFunction => {
                check_argument_count(2, args)?;
                let signature = args[0]
                    .match_list()
                    .ok_or(CheckErrors::DefineFunctionBadSignature)?;
                DefineFunctionsParsed::PrivateFunction {
                    signature,
                    body: &args[1],
                }
            }
            DefineFunctions::ReadOnlyFunction => {
                check_argument_count(2, args)?;
                let signature = args[0]
                    .match_list()
                    .ok_or(CheckErrors::DefineFunctionBadSignature)?;
                DefineFunctionsParsed::ReadOnlyFunction {
                    signature,
                    body: &args[1],
                }
            }
            DefineFunctions::PublicFunction => {
                check_argument_count(2, args)?;
                let signature = args[0]
                    .match_list()
                    .ok_or(CheckErrors::DefineFunctionBadSignature)?;
                DefineFunctionsParsed::PublicFunction {
                    signature,
                    body: &args[1],
                }
            }
            DefineFunctions::NonFungibleToken => {
                check_argument_count(2, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                DefineFunctionsParsed::NonFungibleToken {
                    name,
                    nft_type: &args[1],
                }
            }
            DefineFunctions::FungibleToken => {
                check_arguments_at_least(1, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                if args.len() == 1 {
                    DefineFunctionsParsed::UnboundedFungibleToken { name }
                } else if args.len() == 2 {
                    DefineFunctionsParsed::BoundedFungibleToken {
                        name,
                        max_supply: &args[1],
                    }
                } else {
                    return Err(CheckErrors::IncorrectArgumentCount(1, args.len()));
                }
            }
            DefineFunctions::Map => {
                check_argument_count(3, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                DefineFunctionsParsed::Map {
                    name,
                    key_type: &args[1],
                    value_type: &args[2],
                }
            }
            DefineFunctions::PersistedVariable => {
                check_argument_count(3, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                DefineFunctionsParsed::PersistedVariable {
                    name,
                    data_type: &args[1],
                    initial: &args[2],
                }
            }
            DefineFunctions::Trait => {
                check_argument_count(2, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                DefineFunctionsParsed::Trait {
                    name,
                    functions: &args[1..],
                }
            }
            DefineFunctions::UseTrait => {
                check_argument_count(2, args)?;
                let name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
                match &args[1].expr {
                    Field(ref field) => DefineFunctionsParsed::UseTrait {
                        name,
                        trait_identifier: field,
                    },
                    _ => return Err(CheckErrors::ExpectedTraitIdentifier),
                }
            }
            DefineFunctions::ImplTrait => {
                check_argument_count(1, args)?;
                match &args[0].expr {
                    Field(ref field) => DefineFunctionsParsed::ImplTrait {
                        trait_identifier: field,
                    },
                    _ => return Err(CheckErrors::ExpectedTraitIdentifier),
                }
            }
        };
        Ok(Some(result))
    }
}

pub fn evaluate_define(
    expression: &SymbolicExpression,
    env: &mut Environment,
) -> Result<DefineResult> {
    if let Some(define_type) = DefineFunctionsParsed::try_parse(expression)? {
        match define_type {
            DefineFunctionsParsed::Constant { name, value } => {
                handle_define_variable(name, value, env)
            }
            DefineFunctionsParsed::PrivateFunction { signature, body } => {
                handle_define_function(signature, body, env, DefineType::Private)
            }
            DefineFunctionsParsed::ReadOnlyFunction { signature, body } => {
                handle_define_function(signature, body, env, DefineType::ReadOnly)
            }
            DefineFunctionsParsed::PublicFunction { signature, body } => {
                handle_define_function(signature, body, env, DefineType::Public)
            }
            DefineFunctionsParsed::NonFungibleToken { name, nft_type } => {
                handle_define_nonfungible_asset(name, nft_type, env)
            }
            DefineFunctionsParsed::BoundedFungibleToken { name, max_supply } => {
                handle_define_fungible_token(name, Some(max_supply), env)
            }
            DefineFunctionsParsed::UnboundedFungibleToken { name } => {
                handle_define_fungible_token(name, None, env)
            }
            DefineFunctionsParsed::Map {
                name,
                key_type,
                value_type,
            } => handle_define_map(name, key_type, value_type, env),
            DefineFunctionsParsed::PersistedVariable {
                name,
                data_type,
                initial,
            } => handle_define_persisted_variable(name, data_type, initial, env),
            DefineFunctionsParsed::Trait { name, functions } => {
                handle_define_trait(name, functions, env)
            }
            DefineFunctionsParsed::UseTrait {
                name,
                trait_identifier,
            } => handle_use_trait(name, trait_identifier),
            DefineFunctionsParsed::ImplTrait { trait_identifier } => {
                handle_impl_trait(trait_identifier)
            }
        }
    } else {
        Ok(DefineResult::NoDefine)
    }
}
