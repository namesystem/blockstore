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
use std::fmt;

use stacks_common::types::StacksEpochId;

use super::costs::{CostErrors, CostOverflowingMath};
use super::errors::InterpreterError;
use super::types::signatures::CallableSubtype;
use super::ClarityVersion;
use crate::vm::analysis::errors::CheckErrors;
use crate::vm::contexts::ContractContext;
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::{cost_functions, runtime_cost};
use crate::vm::errors::{check_argument_count, Error, InterpreterResult as Result};
use crate::vm::representations::{ClarityName, Span, SymbolicExpression};
use crate::vm::types::Value::UInt;
use crate::vm::types::{
    CallableData, FunctionType, ListData, ListTypeData, OptionalData, PrincipalData,
    QualifiedContractIdentifier, ResponseData, SequenceData, SequenceSubtype, TraitIdentifier,
    TupleData, TupleTypeSignature, TypeSignature,
};
use crate::vm::{eval, Environment, LocalContext, Value};

#[allow(clippy::type_complexity)]
pub enum CallableType {
    UserFunction(DefinedFunction),
    NativeFunction(&'static str, NativeHandle, ClarityCostFunction),
    /// These native functions have a new method for calculating input size in 2.05
    /// If the global context's epoch is >= 2.05, the fn field is applied to obtain
    /// the input to the cost function.
    NativeFunction205(
        &'static str,
        NativeHandle,
        ClarityCostFunction,
        &'static dyn Fn(&[Value]) -> Result<u64>,
    ),
    SpecialFunction(
        &'static str,
        &'static dyn Fn(&[SymbolicExpression], &mut Environment, &LocalContext) -> Result<Value>,
    ),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum DefineType {
    ReadOnly,
    Public,
    Private,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinedFunction {
    identifier: FunctionIdentifier,
    name: ClarityName,
    arg_types: Vec<TypeSignature>,
    pub define_type: DefineType,
    arguments: Vec<ClarityName>,
    body: SymbolicExpression,
    /// Return type of the function
    /// This field is unused in the interpreter, and set to `None`.
    /// When using the Wasm runtime, it should contain the return type.
    return_type: Option<TypeSignature>,
}

/// This enum handles the actual invocation of the method
/// implementing a native function. Each variant handles
/// different expected number of arguments.
pub enum NativeHandle {
    SingleArg(&'static dyn Fn(Value) -> Result<Value>),
    DoubleArg(&'static dyn Fn(Value, Value) -> Result<Value>),
    MoreArg(&'static dyn Fn(Vec<Value>) -> Result<Value>),
    MoreArgEnv(&'static dyn Fn(Vec<Value>, &mut Environment) -> Result<Value>),
}

impl NativeHandle {
    pub fn apply(&self, mut args: Vec<Value>, env: &mut Environment) -> Result<Value> {
        match self {
            Self::SingleArg(function) => {
                check_argument_count(1, &args)?;
                function(
                    args.pop()
                        .ok_or_else(|| InterpreterError::Expect("Unexpected list length".into()))?,
                )
            }
            Self::DoubleArg(function) => {
                check_argument_count(2, &args)?;
                let second = args
                    .pop()
                    .ok_or_else(|| InterpreterError::Expect("Unexpected list length".into()))?;
                let first = args
                    .pop()
                    .ok_or_else(|| InterpreterError::Expect("Unexpected list length".into()))?;
                function(first, second)
            }
            Self::MoreArg(function) => function(args),
            Self::MoreArgEnv(function) => function(args, env),
        }
    }
}

pub fn cost_input_sized_vararg(args: &[Value]) -> Result<u64> {
    args.iter()
        .try_fold(0, |sum, value| {
            (value
                .serialized_size()
                .map_err(|e| CostErrors::Expect(format!("{e:?}")))? as u64)
                .cost_overflow_add(sum)
        })
        .map_err(Error::from)
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct FunctionIdentifier {
    identifier: String,
}

impl fmt::Display for FunctionIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.identifier)
    }
}

impl DefinedFunction {
    pub fn new(
        arguments: Vec<(ClarityName, TypeSignature)>,
        body: SymbolicExpression,
        define_type: DefineType,
        name: &ClarityName,
        context_name: &str,
        return_type: Option<TypeSignature>,
    ) -> DefinedFunction {
        let (argument_names, types) = arguments.into_iter().unzip();

        DefinedFunction {
            identifier: FunctionIdentifier::new_user_function(name, context_name),
            name: name.clone(),
            arguments: argument_names,
            define_type,
            body,
            arg_types: types,
            return_type,
        }
    }

    pub fn execute_apply(&self, args: &[Value], env: &mut Environment) -> Result<Value> {
        runtime_cost(
            ClarityCostFunction::UserFunctionApplication,
            env,
            self.arguments.len(),
        )?;

        for arg_type in self.arg_types.iter() {
            runtime_cost(
                ClarityCostFunction::InnerTypeCheckCost,
                env,
                arg_type.size()?,
            )?;
        }

        let mut context = LocalContext::new();
        if args.len() != self.arguments.len() {
            Err(CheckErrors::IncorrectArgumentCount(
                self.arguments.len(),
                args.len(),
            ))?
        }

        let arg_iterator: Vec<_> = self
            .arguments
            .iter()
            .zip(self.arg_types.iter())
            .zip(args.iter())
            .collect();

        for arg in arg_iterator.into_iter() {
            let ((name, type_sig), value) = arg;

            // Clarity 1 behavior
            if *env.contract_context.get_clarity_version() < ClarityVersion::Clarity2 {
                match (type_sig, value) {
                    // Epoch < 2.1 uses TraitReferenceType
                    (
                        TypeSignature::TraitReferenceType(trait_identifier),
                        Value::Principal(PrincipalData::Contract(callee_contract_id)),
                    ) if *env.epoch() < StacksEpochId::Epoch21 => {
                        // Argument is a trait reference, probably leading to a dynamic contract call
                        // We keep a reference of the mapping (var-name: (callee_contract_id, trait_id)) in the context.
                        // The code fetching and checking the trait is implemented in the contract_call eval function.
                        context.callable_contracts.insert(
                            name.clone(),
                            CallableData {
                                contract_identifier: callee_contract_id.clone(),
                                trait_identifier: Some(trait_identifier.clone()),
                            },
                        );
                    }
                    // Epoch >= 2.1 uses CallableType
                    (
                        TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)),
                        Value::Principal(PrincipalData::Contract(callee_contract_id)),
                    ) if *env.epoch() >= StacksEpochId::Epoch21 => {
                        // Argument is a trait reference, probably leading to a dynamic contract call
                        // We keep a reference of the mapping (var-name: (callee_contract_id, trait_id)) in the context.
                        // The code fetching and checking the trait is implemented in the contract_call eval function.
                        context.callable_contracts.insert(
                            name.clone(),
                            CallableData {
                                contract_identifier: callee_contract_id.clone(),
                                trait_identifier: Some(trait_identifier.clone()),
                            },
                        );
                    }
                    // Since this Clarity 1 contract may be called from a Clarity 2 contract,
                    // we need to handle Clarity 2 values as well. Clarity 2 contracts can only
                    // be executed in epoch 2.1, so we only need to handle `CallableType` here.
                    (
                        TypeSignature::CallableType(CallableSubtype::Trait(_)),
                        Value::CallableContract(CallableData {
                            contract_identifier,
                            trait_identifier,
                        }),
                    ) => {
                        context.callable_contracts.insert(
                            name.clone(),
                            CallableData {
                                contract_identifier: contract_identifier.clone(),
                                trait_identifier: trait_identifier.clone(),
                            },
                        );
                    }
                    _ => {
                        if !type_sig.admits(env.epoch(), value)? {
                            return Err(CheckErrors::TypeValueError(
                                type_sig.clone(),
                                value.clone(),
                            )
                            .into());
                        }
                        if context
                            .variables
                            .insert(name.clone(), value.clone())
                            .is_some()
                        {
                            return Err(CheckErrors::NameAlreadyUsed(name.to_string()).into());
                        }
                    }
                }
            } else {
                // Clarity 2+ behavior
                // Arguments containing principal literals can be implicitly cast to traits
                // to match parameter types.
                // e.g. `(some .foo)` to `(optional <trait>`)
                // and traits can be implicitly cast to sub-traits
                // e.g. `<foo-and-bar>` to `<foo>`
                let cast_value = clarity2_implicit_cast(type_sig, value)?;

                match (&type_sig, &cast_value) {
                    (
                        TypeSignature::CallableType(CallableSubtype::Trait(_)),
                        Value::CallableContract(CallableData {
                            contract_identifier,
                            trait_identifier,
                        }),
                    ) => {
                        // Argument is a trait reference, probably leading to a dynamic contract call.
                        // We keep a reference of the mapping (var-name: (callee_contract_id, trait_id)) in the context.
                        // The trait compatibility has been checked by the type-checker.
                        context.callable_contracts.insert(
                            name.clone(),
                            CallableData {
                                contract_identifier: contract_identifier.clone(),
                                trait_identifier: trait_identifier.clone(),
                            },
                        );
                    }
                    _ => {
                        if !type_sig.admits(env.epoch(), &cast_value)? {
                            return Err(
                                CheckErrors::TypeValueError(type_sig.clone(), cast_value).into()
                            );
                        }
                    }
                }

                if context.variables.insert(name.clone(), cast_value).is_some() {
                    return Err(CheckErrors::NameAlreadyUsed(name.to_string()).into());
                }
            }
        }

        let result = eval(&self.body, env, &context);

        // if the error wasn't actually an error, but a function return,
        //    pull that out and return it.
        match result {
            Ok(r) => Ok(r),
            Err(e) => match e {
                Error::ShortReturn(v) => Ok(v.into()),
                _ => Err(e),
            },
        }
    }

    pub fn check_trait_expectations(
        &self,
        epoch: &StacksEpochId,
        contract_defining_trait: &ContractContext,
        trait_identifier: &TraitIdentifier,
    ) -> Result<()> {
        let trait_name = trait_identifier.name.to_string();
        let constraining_trait = contract_defining_trait
            .lookup_trait_definition(&trait_name)
            .ok_or(CheckErrors::TraitReferenceUnknown(trait_name.to_string()))?;
        let expected_sig =
            constraining_trait
                .get(&self.name)
                .ok_or(CheckErrors::TraitMethodUnknown(
                    trait_name.to_string(),
                    self.name.to_string(),
                ))?;

        let args = self.arg_types.to_vec();
        if !expected_sig.check_args_trait_compliance(epoch, args)? {
            return Err(
                CheckErrors::BadTraitImplementation(trait_name, self.name.to_string()).into(),
            );
        }

        Ok(())
    }

    pub fn is_read_only(&self) -> bool {
        self.define_type == DefineType::ReadOnly
    }

    pub fn apply(&self, args: &[Value], env: &mut Environment) -> Result<Value> {
        match self.define_type {
            DefineType::Private => self.execute_apply(args, env),
            DefineType::Public => env.execute_function_as_transaction(self, args, None, false),
            DefineType::ReadOnly => env.execute_function_as_transaction(self, args, None, false),
        }
    }

    pub fn is_public(&self) -> bool {
        match self.define_type {
            DefineType::Public => true,
            DefineType::Private => false,
            DefineType::ReadOnly => true,
        }
    }

    pub fn get_identifier(&self) -> FunctionIdentifier {
        self.identifier.clone()
    }

    pub fn get_name(&self) -> &ClarityName {
        &self.name
    }

    pub fn get_arguments(&self) -> &Vec<ClarityName> {
        &self.arguments
    }

    pub fn get_arg_types(&self) -> &Vec<TypeSignature> {
        &self.arg_types
    }

    pub fn get_return_type(&self) -> &Option<TypeSignature> {
        &self.return_type
    }

    pub fn canonicalize_types(&mut self, epoch: &StacksEpochId) {
        for i in 0..self.arguments.len() {
            self.arg_types[i] = self.arg_types[i].canonicalize(epoch);
        }
    }

    pub fn as_str(&self) -> &str {
        &self.identifier.identifier
    }

    #[cfg(feature = "developer-mode")]
    pub fn get_span(&self) -> Span {
        self.body.span.clone()
    }
}

impl CallableType {
    pub fn get_identifier(&self) -> FunctionIdentifier {
        match self {
            CallableType::UserFunction(f) => f.get_identifier(),
            CallableType::NativeFunction(s, _, _) => FunctionIdentifier::new_native_function(s),
            CallableType::SpecialFunction(s, _) => FunctionIdentifier::new_native_function(s),
            CallableType::NativeFunction205(s, _, _, _) => {
                FunctionIdentifier::new_native_function(s)
            }
        }
    }
}

impl FunctionIdentifier {
    fn new_native_function(name: &str) -> FunctionIdentifier {
        let identifier = format!("_native_:{}", name);
        FunctionIdentifier { identifier }
    }

    fn new_user_function(name: &str, context: &str) -> FunctionIdentifier {
        let identifier = format!("{}:{}", context, name);
        FunctionIdentifier { identifier }
    }
}

// Implicitly cast principals to traits and traits to other traits as needed,
// recursing into compound types. This function does not check for legality of
// these casts, as that is done in the type-checker. Note: depth of recursion
// should be capped by earlier checks on the types/values.
fn clarity2_implicit_cast(type_sig: &TypeSignature, value: &Value) -> Result<Value> {
    Ok(match (type_sig, value) {
        (
            TypeSignature::OptionalType(inner_type),
            Value::Optional(OptionalData {
                data: Some(inner_value),
            }),
        ) => Value::Optional(OptionalData {
            data: Some(Box::new(clarity2_implicit_cast(inner_type, inner_value)?)),
        }),
        (
            TypeSignature::ResponseType(inner_types),
            Value::Response(ResponseData { committed, data }),
        ) => Value::Response(ResponseData {
            committed: *committed,
            data: Box::new(clarity2_implicit_cast(
                if *committed {
                    &inner_types.0
                } else {
                    &inner_types.1
                },
                data,
            )?),
        }),
        (
            TypeSignature::SequenceType(SequenceSubtype::ListType(list_type)),
            Value::Sequence(SequenceData::List(ListData {
                data,
                type_signature,
            })),
        ) => {
            let mut values = Vec::with_capacity(data.len());
            for elem in data {
                values.push(clarity2_implicit_cast(
                    list_type.get_list_item_type(),
                    elem,
                )?);
            }
            let cast_list_type_data = ListTypeData::new_list(
                list_type.get_list_item_type().clone(),
                type_signature.get_max_len(),
            )?;
            Value::Sequence(SequenceData::List(ListData {
                data: values,
                type_signature: cast_list_type_data,
            }))
        }
        (
            TypeSignature::TupleType(tuple_type),
            Value::Tuple(TupleData {
                type_signature: _,
                data_map,
            }),
        ) => {
            let mut cast_data_map = BTreeMap::new();
            for (name, field_value) in data_map {
                let to_type = match tuple_type.get_type_map().get(name) {
                    Some(ty) => ty,
                    None => {
                        // This should be unreachable if the type-checker has already run successfully
                        return Err(
                            CheckErrors::TypeValueError(type_sig.clone(), value.clone()).into()
                        );
                    }
                };
                cast_data_map.insert(name.clone(), clarity2_implicit_cast(to_type, field_value)?);
            }
            Value::Tuple(TupleData {
                type_signature: tuple_type.clone(),
                data_map: cast_data_map,
            })
        }
        (
            TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)),
            Value::CallableContract(callable_data),
        ) => Value::CallableContract(CallableData {
            contract_identifier: callable_data.contract_identifier.clone(),
            trait_identifier: Some(trait_identifier.clone()),
        }),
        // N.B. it seems like this should be illegal, since it is converting a
        // principal to a callable trait, and only principal literals should be
        // allowed to do that. The case that this is handling is when principal
        // values are passed in from the initial contract-call, which by
        // definition must be a literal. Other scenarios where a principal is
        // passed will have been caught by the type checker. This could
        // alternatively be checked with
        // `FunctionType::check_args_by_allowing_trait_cast` before execution.
        (
            TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)),
            Value::Principal(PrincipalData::Contract(contract_identifier)),
        ) => Value::CallableContract(CallableData {
            contract_identifier: contract_identifier.clone(),
            trait_identifier: Some(trait_identifier.clone()),
        }),
        _ => value.clone(),
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::vm::types::StandardPrincipalData;

    #[test]
    fn test_implicit_cast() {
        // principal -> <trait>
        let trait_identifier = TraitIdentifier::parse_fully_qualified(
            "SP2PABAF9FTAJYNFZH93XENAJ8FVY99RRM50D2JG9.nft-trait.nft-trait",
        )
        .unwrap();
        let trait_ty =
            TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier.clone()));
        let contract_identifier = QualifiedContractIdentifier::parse(
            "SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR.contract",
        )
        .unwrap();
        let contract_identifier2 = QualifiedContractIdentifier::parse(
            "SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR.contract2",
        )
        .unwrap();
        let contract = Value::CallableContract(CallableData {
            contract_identifier: contract_identifier.clone(),
            trait_identifier: None,
        });
        let contract2 = Value::CallableContract(CallableData {
            contract_identifier: contract_identifier2,
            trait_identifier: None,
        });
        let cast_contract = clarity2_implicit_cast(&trait_ty, &contract).unwrap();
        let cast_trait = cast_contract.expect_callable().unwrap();
        assert_eq!(&cast_trait.contract_identifier, &contract_identifier);
        assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);

        // (optional principal) -> (optional <trait>)
        let optional_ty = TypeSignature::new_option(trait_ty.clone()).unwrap();
        let optional_contract = Value::some(contract.clone()).unwrap();
        let cast_optional = clarity2_implicit_cast(&optional_ty, &optional_contract).unwrap();
        match &cast_optional.expect_optional().unwrap().unwrap() {
            Value::CallableContract(CallableData {
                contract_identifier: contract_id,
                trait_identifier: trait_id,
            }) => {
                assert_eq!(contract_id, &contract_identifier);
                assert_eq!(trait_id.as_ref().unwrap(), &trait_identifier);
            }
            other => panic!("expected Value::CallableContract, got {:?}", other),
        }

        // (ok principal) -> (ok <trait>)
        let response_ok_ty =
            TypeSignature::new_response(trait_ty.clone(), TypeSignature::UIntType).unwrap();
        let response_contract = Value::okay(contract.clone()).unwrap();
        let cast_response = clarity2_implicit_cast(&response_ok_ty, &response_contract).unwrap();
        let cast_trait = cast_response
            .expect_result_ok()
            .unwrap()
            .expect_callable()
            .unwrap();
        assert_eq!(&cast_trait.contract_identifier, &contract_identifier);
        assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);

        // (err principal) -> (err <trait>)
        let response_err_ty =
            TypeSignature::new_response(TypeSignature::UIntType, trait_ty.clone()).unwrap();
        let response_contract = Value::error(contract.clone()).unwrap();
        let cast_response = clarity2_implicit_cast(&response_err_ty, &response_contract).unwrap();
        let cast_trait = cast_response
            .expect_result_err()
            .unwrap()
            .expect_callable()
            .unwrap();
        assert_eq!(&cast_trait.contract_identifier, &contract_identifier);
        assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);

        // (list principal) -> (list <trait>)
        let list_ty = TypeSignature::list_of(trait_ty.clone(), 4).unwrap();
        let list_contract = Value::list_from(vec![contract.clone(), contract2.clone()]).unwrap();
        let cast_list = clarity2_implicit_cast(&list_ty, &list_contract).unwrap();
        let items = cast_list.expect_list().unwrap();
        for item in items {
            let cast_trait = item.expect_callable().unwrap();
            assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);
        }

        // {a: principal} -> {a: <trait>}
        let a_name = ClarityName::from("a");
        let tuple_ty = TypeSignature::TupleType(
            TupleTypeSignature::try_from(vec![(a_name.clone(), trait_ty)]).unwrap(),
        );
        let contract_tuple_ty = TypeSignature::TupleType(
            TupleTypeSignature::try_from(vec![(a_name.clone(), TypeSignature::PrincipalType)])
                .unwrap(),
        );
        let mut data_map = BTreeMap::new();
        data_map.insert(a_name.clone(), contract.clone());
        let tuple_contract = Value::Tuple(TupleData {
            type_signature: TupleTypeSignature::try_from(vec![(
                a_name.clone(),
                TypeSignature::PrincipalType,
            )])
            .unwrap(),
            data_map,
        });
        let cast_tuple = clarity2_implicit_cast(&tuple_ty, &tuple_contract).unwrap();
        let cast_trait = cast_tuple
            .expect_tuple()
            .unwrap()
            .get(&a_name)
            .unwrap()
            .clone()
            .expect_callable()
            .unwrap();
        assert_eq!(&cast_trait.contract_identifier, &contract_identifier);
        assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);

        // (list (optional principal)) -> (list (optional <trait>))
        let list_opt_ty = TypeSignature::list_of(optional_ty.clone(), 4).unwrap();
        let list_opt_contract = Value::list_from(vec![
            Value::some(contract.clone()).unwrap(),
            Value::some(contract2.clone()).unwrap(),
            Value::none(),
        ])
        .unwrap();
        let cast_list = clarity2_implicit_cast(&list_opt_ty, &list_opt_contract).unwrap();
        let items = cast_list.expect_list().unwrap();
        for item in items {
            if let Some(cast_opt) = item.expect_optional().unwrap() {
                let cast_trait = cast_opt.expect_callable().unwrap();
                assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);
            }
        }

        // (list (response principal uint)) -> (list (response <trait> uint))
        let list_res_ty = TypeSignature::list_of(response_ok_ty, 4).unwrap();
        let list_res_contract = Value::list_from(vec![
            Value::okay(contract.clone()).unwrap(),
            Value::okay(contract2.clone()).unwrap(),
            Value::okay(contract2.clone()).unwrap(),
        ])
        .unwrap();
        let cast_list = clarity2_implicit_cast(&list_res_ty, &list_res_contract).unwrap();
        let items = cast_list.expect_list().unwrap();
        for item in items {
            let cast_trait = item.expect_result_ok().unwrap().expect_callable().unwrap();
            assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);
        }

        // (list (response uint principal)) -> (list (response uint <trait>))
        let list_res_ty = TypeSignature::list_of(response_err_ty.clone(), 4).unwrap();
        let list_res_contract = Value::list_from(vec![
            Value::error(contract.clone()).unwrap(),
            Value::error(contract2.clone()).unwrap(),
            Value::error(contract2.clone()).unwrap(),
        ])
        .unwrap();
        let cast_list = clarity2_implicit_cast(&list_res_ty, &list_res_contract).unwrap();
        let items = cast_list.expect_list().unwrap();
        for item in items {
            let cast_trait = item.expect_result_err().unwrap().expect_callable().unwrap();
            assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);
        }

        // (optional (list (response uint principal))) -> (optional (list (response uint <trait>)))
        let list_res_ty = TypeSignature::list_of(response_err_ty, 4).unwrap();
        let opt_list_res_ty = TypeSignature::new_option(list_res_ty).unwrap();
        let list_res_contract = Value::list_from(vec![
            Value::error(contract.clone()).unwrap(),
            Value::error(contract2.clone()).unwrap(),
            Value::error(contract2).unwrap(),
        ])
        .unwrap();
        let opt_list_res_contract = Value::some(list_res_contract).unwrap();
        let cast_opt = clarity2_implicit_cast(&opt_list_res_ty, &opt_list_res_contract).unwrap();
        let inner = cast_opt.expect_optional().unwrap().unwrap();
        let items = inner.expect_list().unwrap();
        for item in items {
            let cast_trait = item.expect_result_err().unwrap().expect_callable().unwrap();
            assert_eq!(&cast_trait.trait_identifier.unwrap(), &trait_identifier);
        }

        // (optional (optional principal)) -> (optional (optional <trait>))
        let optional_optional_ty = TypeSignature::new_option(optional_ty).unwrap();
        let optional_contract = Value::some(contract).unwrap();
        let optional_optional_contract = Value::some(optional_contract).unwrap();
        let cast_optional =
            clarity2_implicit_cast(&optional_optional_ty, &optional_optional_contract).unwrap();

        match &cast_optional
            .expect_optional()
            .unwrap()
            .unwrap()
            .expect_optional()
            .unwrap()
            .unwrap()
        {
            Value::CallableContract(CallableData {
                contract_identifier: contract_id,
                trait_identifier: trait_id,
            }) => {
                assert_eq!(contract_id, &contract_identifier);
                assert_eq!(trait_id.as_ref().unwrap(), &trait_identifier);
            }
            other => panic!("expected Value::CallableContract, got {:?}", other),
        }
    }

    #[test]
    fn test_canonicalize_defined_function() {
        let trait_id = TraitIdentifier::new(
            StandardPrincipalData::transient(),
            "my-contract".into(),
            "my-trait".into(),
        );
        let mut f = DefinedFunction::new(
            vec![(
                "a".into(),
                TypeSignature::TraitReferenceType(trait_id.clone()),
            )],
            SymbolicExpression::atom_value(Value::Int(3)),
            DefineType::Public,
            &"foo".into(),
            "testing",
            Some(TypeSignature::IntType),
        );
        f.canonicalize_types(&StacksEpochId::Epoch21);
        assert_eq!(
            f.arg_types[0],
            TypeSignature::CallableType(CallableSubtype::Trait(trait_id))
        );
    }
}
