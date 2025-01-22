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

pub mod contexts;
pub mod natives;

use std::collections::BTreeMap;

use hashbrown::HashMap;
use stacks_common::types::StacksEpochId;

use self::contexts::ContractContext;
pub use self::natives::{SimpleNativeFunction, TypedNativeFunction};
use super::contexts::{TypeMap, TypingContext};
use super::{AnalysisPass, ContractAnalysis};
pub use crate::vm::analysis::errors::{
    check_argument_count, check_arguments_at_least, check_arguments_at_most, CheckError,
    CheckErrors, CheckResult,
};
use crate::vm::analysis::AnalysisDatabase;
use crate::vm::contexts::Environment;
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::{
    analysis_typecheck_cost, cost_functions, runtime_cost, ClarityCostFunctionReference,
    CostErrors, CostOverflowingMath, CostTracker, ExecutionCost, LimitedCostTracker,
};
use crate::vm::diagnostic::Diagnostic;
use crate::vm::functions::define::DefineFunctionsParsed;
use crate::vm::functions::NativeFunctions;
use crate::vm::representations::SymbolicExpressionType::{
    Atom, AtomValue, Field, List, LiteralValue, TraitReference,
};
use crate::vm::representations::{depth_traverse, ClarityName, SymbolicExpression};
use crate::vm::types::signatures::{
    CallableSubtype, FunctionArgSignature, FunctionReturnsSignature, FunctionSignature, BUFF_20,
};
use crate::vm::types::{
    parse_name_type_pairs, CallableData, FixedFunction, FunctionArg, FunctionType, ListData,
    ListTypeData, OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData,
    SequenceData, SequenceSubtype, StringSubtype, TraitIdentifier, TupleData, TupleTypeSignature,
    TypeSignature, Value, MAX_TYPE_DEPTH,
};
use crate::vm::variables::NativeVariables;
use crate::vm::ClarityVersion;

#[cfg(test)]
pub mod tests;

/*

Type-checking in our language is achieved through a single-direction inference.
This leads to efficient type-checking. This form of type-checking is only possible
due to the rules of our language. In particular, functions define their input types,
and any given intermediate in the language has a strict type as well, meaning something
of the form:

(if x
   true
   -1)

Is illegally typed in our language.

*/

pub struct TypeChecker<'a, 'b> {
    epoch: StacksEpochId,
    pub type_map: TypeMap,
    contract_context: ContractContext,
    function_return_tracker: Option<Option<TypeSignature>>,
    db: &'a mut AnalysisDatabase<'b>,
    pub cost_track: LimitedCostTracker,
    clarity_version: ClarityVersion,
}

impl CostTracker for TypeChecker<'_, '_> {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> Result<ExecutionCost, CostErrors> {
        self.cost_track.compute_cost(cost_function, input)
    }

    fn add_cost(&mut self, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        self.cost_track.add_cost(cost)
    }
    fn add_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        self.cost_track.add_memory(memory)
    }
    fn drop_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        self.cost_track.drop_memory(memory)
    }
    fn reset_memory(&mut self) {
        self.cost_track.reset_memory()
    }
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> std::result::Result<bool, CostErrors> {
        self.cost_track
            .short_circuit_contract_call(contract, function, input)
    }
}

impl TypeChecker<'_, '_> {
    pub fn run_pass(
        epoch: &StacksEpochId,
        contract_analysis: &mut ContractAnalysis,
        analysis_db: &mut AnalysisDatabase,
        build_type_map: bool,
    ) -> CheckResult<()> {
        let cost_track = contract_analysis.take_contract_cost_tracker();
        let mut command = TypeChecker::new(
            epoch,
            analysis_db,
            cost_track,
            &contract_analysis.contract_identifier,
            &contract_analysis.clarity_version,
            build_type_map,
        );
        // run the analysis, and replace the cost tracker whether or not the
        //   analysis succeeded.
        match command.run(contract_analysis) {
            Ok(_) => {
                let cost_track = command.into_contract_analysis(contract_analysis);
                contract_analysis.replace_contract_cost_tracker(cost_track);
                Ok(())
            }
            err => {
                let TypeChecker { cost_track, .. } = command;
                contract_analysis.replace_contract_cost_tracker(cost_track);
                err
            }
        }
    }
}

pub type TypeResult = CheckResult<TypeSignature>;

pub fn compute_typecheck_cost<T: CostTracker>(
    track: &mut T,
    t1: &TypeSignature,
    t2: &TypeSignature,
) -> Result<ExecutionCost, CostErrors> {
    let t1_size = t1.type_size().map_err(|_| CostErrors::CostOverflow)?;
    let t2_size = t2.type_size().map_err(|_| CostErrors::CostOverflow)?;
    track.compute_cost(
        ClarityCostFunction::AnalysisTypeCheck,
        &[std::cmp::max(t1_size, t2_size).into()],
    )
}

pub fn check_argument_len(expected: usize, args_len: usize) -> Result<(), CheckErrors> {
    if args_len != expected {
        Err(CheckErrors::IncorrectArgumentCount(expected, args_len))
    } else {
        Ok(())
    }
}

impl FunctionType {
    pub fn check_args_visitor_2_1<T: CostTracker>(
        &self,
        accounting: &mut T,
        arg_type: &TypeSignature,
        arg_index: usize,
        accumulated_type: Option<&TypeSignature>,
    ) -> (
        Option<Result<ExecutionCost, CostErrors>>,
        CheckResult<Option<TypeSignature>>,
    ) {
        match self {
            // variadic stops checking cost at the first error...
            FunctionType::Variadic(expected_type, _) => {
                let cost = Some(compute_typecheck_cost(accounting, expected_type, arg_type));
                let admitted = match expected_type.admits_type(&StacksEpochId::Epoch21, arg_type) {
                    Ok(admitted) => admitted,
                    Err(e) => return (cost, Err(e.into())),
                };
                if !admitted {
                    return (
                        cost,
                        Err(CheckErrors::TypeError(expected_type.clone(), arg_type.clone()).into()),
                    );
                }
                (cost, Ok(None))
            }
            FunctionType::ArithmeticVariadic => {
                let cost = Some(compute_typecheck_cost(
                    accounting,
                    &TypeSignature::IntType,
                    arg_type,
                ));
                if arg_index == 0 {
                    let return_type = match arg_type {
                        TypeSignature::IntType => Ok(Some(TypeSignature::IntType)),
                        TypeSignature::UIntType => Ok(Some(TypeSignature::UIntType)),
                        _ => Err(CheckErrors::UnionTypeError(
                            vec![TypeSignature::IntType, TypeSignature::UIntType],
                            arg_type.clone(),
                        )
                        .into()),
                    };
                    (cost, return_type)
                } else {
                    let return_type = accumulated_type
                        .ok_or_else(|| CheckErrors::Expects("Failed to set accumulated type for arg indices >= 1 in variadic arithmetic".into()).into());
                    let check_result = return_type.and_then(|return_type| {
                        if arg_type != return_type {
                            Err(
                                CheckErrors::TypeError(return_type.clone(), arg_type.clone())
                                    .into(),
                            )
                        } else {
                            Ok(None)
                        }
                    });
                    (cost, check_result)
                }
            }
            // For the fixed function types, the visitor will just
            //  tell the processor that any results greater than the args len
            //  do not need to be stored, because an error will occur before
            //  further checking anyways
            FunctionType::Fixed(FixedFunction {
                args: arg_types, ..
            }) => {
                if arg_index >= arg_types.len() {
                    // note: argument count will be wrong?
                    return (
                        None,
                        Err(CheckErrors::IncorrectArgumentCount(arg_types.len(), arg_index).into()),
                    );
                }
                (None, Ok(None))
            }
            // For the following function types, the visitor will just
            //  tell the processor that any results greater than len 1 or 2
            //  do not need to be stored, because an error will occur before
            //  further checking anyways
            FunctionType::ArithmeticUnary | FunctionType::UnionArgs(..) => {
                if arg_index >= 1 {
                    return (
                        None,
                        Err(CheckErrors::IncorrectArgumentCount(1, arg_index).into()),
                    );
                }
                (None, Ok(None))
            }
            FunctionType::ArithmeticBinary
            | FunctionType::ArithmeticComparison
            | FunctionType::Binary(..) => {
                if arg_index >= 2 {
                    return (
                        None,
                        Err(CheckErrors::IncorrectArgumentCount(2, arg_index).into()),
                    );
                }
                (None, Ok(None))
            }
        }
    }

    pub fn check_args_2_1<T: CostTracker>(
        &self,
        accounting: &mut T,
        args: &[TypeSignature],
        clarity_version: ClarityVersion,
    ) -> CheckResult<TypeSignature> {
        match self {
            FunctionType::Variadic(expected_type, return_type) => {
                check_arguments_at_least(1, args)?;
                for found_type in args.iter() {
                    analysis_typecheck_cost(accounting, expected_type, found_type)?;
                    if !expected_type.admits_type(&StacksEpochId::Epoch21, found_type)? {
                        return Err(CheckErrors::TypeError(
                            expected_type.clone(),
                            found_type.clone(),
                        )
                        .into());
                    }
                }
                Ok(return_type.clone())
            }
            FunctionType::Fixed(FixedFunction {
                args: arg_types,
                returns,
            }) => {
                check_argument_count(arg_types.len(), args)?;
                for (expected_type, found_type) in arg_types.iter().map(|x| &x.signature).zip(args)
                {
                    analysis_typecheck_cost(accounting, expected_type, found_type)?;
                    if !expected_type.admits_type(&StacksEpochId::Epoch21, found_type)? {
                        return Err(CheckErrors::TypeError(
                            expected_type.clone(),
                            found_type.clone(),
                        )
                        .into());
                    }
                }
                Ok(returns.clone())
            }
            FunctionType::UnionArgs(arg_types, return_type) => {
                check_argument_count(1, args)?;
                let found_type = &args[0];
                for expected_type in arg_types.iter() {
                    analysis_typecheck_cost(accounting, expected_type, found_type)?;
                    if expected_type.admits_type(&StacksEpochId::Epoch21, found_type)? {
                        return Ok(return_type.clone());
                    }
                }
                Err(CheckErrors::UnionTypeError(arg_types.clone(), found_type.clone()).into())
            }
            FunctionType::Binary(left_arg_sig, right_arg_sig, return_sig) => {
                check_argument_count(2, args)?;

                let found_left_type = &args[0];
                let found_right_type = &args[1];

                check_function_arg_signature(accounting, left_arg_sig, found_left_type)?;
                check_function_arg_signature(accounting, right_arg_sig, found_right_type)?;

                match return_sig {
                    FunctionReturnsSignature::TypeOfArgAtPosition(pos) => Ok(args[*pos].clone()),
                    FunctionReturnsSignature::Fixed(return_type) => Ok(return_type.clone()),
                }
            }
            FunctionType::ArithmeticVariadic
            | FunctionType::ArithmeticBinary
            | FunctionType::ArithmeticUnary => {
                if self == &FunctionType::ArithmeticUnary {
                    check_argument_count(1, args)?;
                }
                if self == &FunctionType::ArithmeticBinary {
                    check_argument_count(2, args)?;
                }
                let (first, rest) = args
                    .split_first()
                    .ok_or(CheckErrors::RequiresAtLeastArguments(1, args.len()))?;
                analysis_typecheck_cost(accounting, &TypeSignature::IntType, first)?;
                let return_type = match first {
                    TypeSignature::IntType => Ok(TypeSignature::IntType),
                    TypeSignature::UIntType => Ok(TypeSignature::UIntType),
                    _ => Err(CheckErrors::UnionTypeError(
                        vec![TypeSignature::IntType, TypeSignature::UIntType],
                        first.clone(),
                    )),
                }?;
                for found_type in rest.iter() {
                    analysis_typecheck_cost(accounting, &TypeSignature::IntType, found_type)?;
                    if found_type != &return_type {
                        return Err(CheckErrors::TypeError(return_type, found_type.clone()).into());
                    }
                }
                Ok(return_type)
            }
            FunctionType::ArithmeticComparison => {
                check_argument_count(2, args)?;
                let (first, second) = (&args[0], &args[1]);
                analysis_typecheck_cost(accounting, &TypeSignature::IntType, first)?;
                analysis_typecheck_cost(accounting, &TypeSignature::IntType, second)?;

                // Note: Clarity2 expanded the comparable types to include ASCII, UTF8 and Buffer.
                // Int and UInt have been present since Clarity1.
                let is_clarity2: bool = clarity_version >= ClarityVersion::Clarity2;
                // Step 1: Check the first argument on its own, to see that the first argument
                // has a supported type according to this ClarityVersion.
                let first_type_supported = match first {
                    TypeSignature::IntType => true,
                    TypeSignature::UIntType => true,
                    TypeSignature::SequenceType(SequenceSubtype::StringType(
                        StringSubtype::ASCII(_),
                    )) => is_clarity2,
                    TypeSignature::SequenceType(SequenceSubtype::StringType(
                        StringSubtype::UTF8(_),
                    )) => is_clarity2,
                    TypeSignature::SequenceType(SequenceSubtype::BufferType(_)) => is_clarity2,
                    _ => false,
                };

                if !first_type_supported {
                    return Err(CheckErrors::UnionTypeError(
                        vec![
                            TypeSignature::IntType,
                            TypeSignature::UIntType,
                            TypeSignature::max_string_ascii()?,
                            TypeSignature::max_string_utf8()?,
                            TypeSignature::max_buffer()?,
                        ],
                        first.clone(),
                    )
                    .into());
                }

                // Step 2: Assuming the first argument has a supported type, now check that
                // both of the types are matching.
                let pair_of_types_matches = match (first, second) {
                    (TypeSignature::IntType, TypeSignature::IntType) => true,
                    (TypeSignature::UIntType, TypeSignature::UIntType) => true,
                    (
                        TypeSignature::SequenceType(SequenceSubtype::StringType(
                            StringSubtype::ASCII(_),
                        )),
                        TypeSignature::SequenceType(SequenceSubtype::StringType(
                            StringSubtype::ASCII(_),
                        )),
                    ) => true,
                    (
                        TypeSignature::SequenceType(SequenceSubtype::StringType(
                            StringSubtype::UTF8(_),
                        )),
                        TypeSignature::SequenceType(SequenceSubtype::StringType(
                            StringSubtype::UTF8(_),
                        )),
                    ) => true,
                    (
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(_)),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(_)),
                    ) => true,
                    (_, _) => false,
                };

                if !pair_of_types_matches {
                    return Err(CheckErrors::TypeError(first.clone(), second.clone()).into());
                }

                Ok(TypeSignature::BoolType)
            }
        }
    }

    /// Returns the type of `value`, after converting any contract principal
    /// types to callable types. In an initial transaction, arguments are typed
    /// as contract principals, but they must be principal literals, so they
    /// may be used to call into a contract.
    pub fn principal_to_callable_type(
        &self,
        value: &Value,
        depth: u8,
        clarity_version: ClarityVersion,
    ) -> TypeResult {
        if clarity_version >= ClarityVersion::Clarity2 {
            // In Clarity2, we recurse into complex data types
            self.clarity2_principal_to_callable_type(value, depth)
        } else {
            // In Clarity1, we just need to convert the top-level principal
            Ok(match value {
                Value::Principal(PrincipalData::Contract(contract_identifier)) => {
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        contract_identifier.clone(),
                    ))
                }
                _ => TypeSignature::type_of(value)?,
            })
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn clarity2_principal_to_callable_type(&self, value: &Value, depth: u8) -> TypeResult {
        if depth > MAX_TYPE_DEPTH {
            return Err(CheckErrors::TypeSignatureTooDeep.into());
        }

        Ok(match value {
            Value::Principal(PrincipalData::Contract(contract_identifier)) => {
                TypeSignature::CallableType(CallableSubtype::Principal(contract_identifier.clone()))
            }
            Value::Optional(OptionalData {
                data: Some(inner_value),
            }) => TypeSignature::new_option(
                self.clarity2_principal_to_callable_type(inner_value, depth + 1)?,
            )?,
            Value::Response(ResponseData { committed, data }) => {
                let (ok_type, err_type) = if *committed {
                    (
                        self.clarity2_principal_to_callable_type(data, depth + 1)?,
                        TypeSignature::NoType,
                    )
                } else {
                    (
                        TypeSignature::NoType,
                        self.clarity2_principal_to_callable_type(data, depth + 1)?,
                    )
                };
                TypeSignature::new_response(ok_type, err_type)?
            }
            Value::Sequence(SequenceData::List(ListData {
                data,
                type_signature: _,
            })) => {
                let inner_type = match data.first() {
                    Some(inner_val) => {
                        self.clarity2_principal_to_callable_type(inner_val, depth + 1)?
                    }
                    None => TypeSignature::NoType,
                };
                TypeSignature::SequenceType(SequenceSubtype::ListType(ListTypeData::new_list(
                    inner_type,
                    data.len() as u32,
                )?))
            }
            Value::Tuple(TupleData {
                type_signature: _,
                data_map,
            }) => {
                let mut type_map = BTreeMap::new();
                for (name, field_value) in data_map {
                    type_map.insert(
                        name.clone(),
                        self.clarity2_principal_to_callable_type(field_value, depth + 1)?,
                    );
                }
                TypeSignature::TupleType(TupleTypeSignature::try_from(type_map)?)
            }
            _ => TypeSignature::type_of(value)?,
        })
    }

    /// This method is only used by StacksChainState::can_include_tx. The
    /// cost of evaluating these type checks are not tracked.
    /// WARNING: This is not consensus-critical code, and should never be
    ///          called from consensus-critical code.
    pub fn check_args_by_allowing_trait_cast_2_1(
        &self,
        db: &mut AnalysisDatabase,
        clarity_version: ClarityVersion,
        func_args: &[Value],
    ) -> CheckResult<TypeSignature> {
        let (expected_args, returns) = match self {
            FunctionType::Fixed(FixedFunction { args, returns }) => (args, returns),
            _ => return Err(CheckErrors::Expects("Unexpected function type".into()).into()),
        };
        check_argument_count(expected_args.len(), func_args)?;

        if clarity_version < ClarityVersion::Clarity2 {
            for (expected_arg, arg) in expected_args.iter().zip(func_args.iter()) {
                match (&expected_arg.signature, arg) {
                    (
                        TypeSignature::CallableType(CallableSubtype::Trait(trait_id)),
                        Value::Principal(PrincipalData::Contract(contract)),
                    ) => {
                        let contract_to_check = db
                            .load_contract(contract, &StacksEpochId::Epoch21)?
                            .ok_or_else(|| {
                                CheckErrors::NoSuchContract(contract.name.to_string())
                            })?;
                        let trait_definition = db
                            .get_defined_trait(
                                &trait_id.contract_identifier,
                                &trait_id.name,
                                &StacksEpochId::Epoch21,
                            )
                            .map_err(|_| CheckErrors::Expects("Failed to get trait".into()))?
                            .ok_or(CheckErrors::NoSuchContract(
                                trait_id.contract_identifier.to_string(),
                            ))?;
                        contract_to_check.check_trait_compliance(
                            &StacksEpochId::Epoch21,
                            trait_id,
                            &trait_definition,
                        )?;
                    }
                    (expected_type, value) => {
                        if !expected_type.admits(&StacksEpochId::Epoch21, value)? {
                            let actual_type = TypeSignature::type_of(value)?;
                            return Err(
                                CheckErrors::TypeError(expected_type.clone(), actual_type).into()
                            );
                        }
                    }
                }
            }
        } else {
            let mut arg_types = Vec::with_capacity(func_args.len());
            for arg in func_args {
                arg_types.push(self.principal_to_callable_type(arg, 1, clarity_version)?);
            }

            for (expected_arg, arg_type) in expected_args.iter().zip(arg_types.iter()) {
                clarity2_inner_type_check_type(
                    db,
                    None,
                    arg_type,
                    &expected_arg.signature,
                    1,
                    &mut LimitedCostTracker::new_free(),
                )?;
            }
        }
        Ok(returns.clone())
    }
}

fn check_function_arg_signature<T: CostTracker>(
    cost_tracker: &mut T,
    expected_sig: &FunctionArgSignature,
    actual_type: &TypeSignature,
) -> CheckResult<()> {
    match expected_sig {
        FunctionArgSignature::Single(expected_type) => {
            analysis_typecheck_cost(cost_tracker, expected_type, actual_type)?;
            if !expected_type.admits_type(&StacksEpochId::Epoch21, actual_type)? {
                return Err(
                    CheckErrors::TypeError(expected_type.clone(), actual_type.clone()).into(),
                );
            }
        }
        FunctionArgSignature::Union(expected_types) => {
            let mut admitted = false;
            for expected_type in expected_types.iter() {
                analysis_typecheck_cost(cost_tracker, expected_type, actual_type)?;
                if expected_type.admits_type(&StacksEpochId::Epoch21, actual_type)? {
                    admitted = true;
                    break;
                }
            }
            if !admitted {
                return Err(CheckErrors::UnionTypeError(
                    expected_types.clone(),
                    actual_type.clone(),
                )
                .into());
            }
        }
    }

    Ok(())
}

/// Used to check if a function signature is compatible with the function
/// signature required for a trait.
fn clarity2_check_functions_compatible<T: CostTracker>(
    db: &mut AnalysisDatabase,
    contract_context: Option<&ContractContext>,
    expected_sig: &FunctionSignature,
    actual_sig: &FunctionSignature,
    tracker: &mut T,
) -> bool {
    if expected_sig.args.len() != actual_sig.args.len() {
        return false;
    }
    let args_iter = expected_sig.args.iter().zip(actual_sig.args.iter());
    for (expected_type, actual_type) in args_iter {
        if clarity2_inner_type_check_type(
            db,
            contract_context,
            actual_type,
            expected_type,
            1,
            tracker,
        )
        .is_err()
        {
            return false;
        }
    }
    if clarity2_inner_type_check_type(
        db,
        contract_context,
        &actual_sig.returns,
        &expected_sig.returns,
        1,
        tracker,
    )
    .is_err()
    {
        return false;
    }
    true
}

/// Returns Ok if actual_trait is compliant with expected_trait.
/// This means that actual_trait implements all functions from expected_trait
/// with compatible functions, and may optionally include other functions not
/// included in expected_trait.
pub fn clarity2_trait_check_trait_compliance<T: CostTracker>(
    db: &mut AnalysisDatabase,
    contract_context: Option<&ContractContext>,
    actual_trait_identifier: &TraitIdentifier,
    actual_trait: &BTreeMap<ClarityName, FunctionSignature>,
    expected_trait_identifier: &TraitIdentifier,
    expected_trait: &BTreeMap<ClarityName, FunctionSignature>,
    tracker: &mut T,
) -> CheckResult<()> {
    // Shortcut for the simple case when the two traits are the same.
    if actual_trait_identifier == expected_trait_identifier {
        return Ok(());
    }

    for (func_name, expected_sig) in expected_trait.iter() {
        if let Some(func) = actual_trait.get(func_name) {
            if !clarity2_check_functions_compatible(
                db,
                contract_context,
                expected_sig,
                func,
                tracker,
            ) {
                return Err(CheckErrors::IncompatibleTrait(
                    expected_trait_identifier.clone(),
                    actual_trait_identifier.clone(),
                )
                .into());
            }
        } else {
            return Err(CheckErrors::IncompatibleTrait(
                expected_trait_identifier.clone(),
                actual_trait_identifier.clone(),
            )
            .into());
        }
    }
    Ok(())
}

/// Check if `expected_type` admits `actual_type`, handling traits and callable types
/// through invoking trait compliance checks.
fn clarity2_inner_type_check_type<T: CostTracker>(
    db: &mut AnalysisDatabase,
    contract_context: Option<&ContractContext>,
    actual_type: &TypeSignature,
    expected_type: &TypeSignature,
    depth: u8,
    tracker: &mut T,
) -> TypeResult {
    if depth > MAX_TYPE_DEPTH {
        return Err(CheckErrors::TypeSignatureTooDeep.into());
    }

    // Recurse into values to check embedded traits properly
    match (actual_type, expected_type) {
        (
            TypeSignature::OptionalType(atom_inner_type),
            TypeSignature::OptionalType(expected_inner_type),
        ) => {
            clarity2_inner_type_check_type(
                db,
                contract_context,
                atom_inner_type,
                expected_inner_type,
                depth + 1,
                tracker,
            )?;
        }
        (
            TypeSignature::ResponseType(atom_inner_types),
            TypeSignature::ResponseType(expected_inner_types),
        ) => {
            clarity2_inner_type_check_type(
                db,
                contract_context,
                &atom_inner_types.0,
                &expected_inner_types.0,
                depth + 1,
                tracker,
            )?;
            clarity2_inner_type_check_type(
                db,
                contract_context,
                &atom_inner_types.1,
                &expected_inner_types.1,
                depth + 1,
                tracker,
            )?;
        }
        (
            TypeSignature::SequenceType(SequenceSubtype::ListType(atom_list_type)),
            TypeSignature::SequenceType(SequenceSubtype::ListType(expected_list_type)),
        ) => {
            if atom_list_type.get_max_len() <= expected_list_type.get_max_len() {
                clarity2_inner_type_check_type(
                    db,
                    contract_context,
                    atom_list_type.get_list_item_type(),
                    expected_list_type.get_list_item_type(),
                    depth + 1,
                    tracker,
                )?;
            } else {
                return Err(
                    CheckErrors::TypeError(expected_type.clone(), actual_type.clone()).into(),
                );
            }
        }
        (
            TypeSignature::TupleType(atom_tuple_type),
            TypeSignature::TupleType(expected_tuple_type),
        ) => {
            if expected_tuple_type.get_type_map().len() != atom_tuple_type.get_type_map().len() {
                return Err(
                    CheckErrors::TypeError(expected_type.clone(), actual_type.clone()).into(),
                );
            }

            for (name, expected_field_type) in expected_tuple_type.get_type_map() {
                match atom_tuple_type.field_type(name) {
                    Some(atom_field_type) => {
                        clarity2_inner_type_check_type(
                            db,
                            contract_context,
                            atom_field_type,
                            expected_field_type,
                            depth + 1,
                            tracker,
                        )?;
                    }
                    None => {
                        return Err(CheckErrors::TypeError(
                            expected_type.clone(),
                            actual_type.clone(),
                        )
                        .into());
                    }
                }
            }
        }
        (
            TypeSignature::CallableType(CallableSubtype::Trait(atom_trait_id)),
            TypeSignature::CallableType(CallableSubtype::Trait(expected_trait_id)),
        ) => {
            if atom_trait_id != expected_trait_id {
                let atom_trait =
                    clarity2_lookup_trait(db, contract_context, atom_trait_id, tracker)?;
                let expected_trait =
                    clarity2_lookup_trait(db, contract_context, expected_trait_id, tracker)?;
                clarity2_trait_check_trait_compliance(
                    db,
                    contract_context,
                    atom_trait_id,
                    &atom_trait,
                    expected_trait_id,
                    &expected_trait,
                    tracker,
                )?;
            }
        }
        (
            TypeSignature::CallableType(CallableSubtype::Principal(contract_identifier)),
            TypeSignature::CallableType(CallableSubtype::Trait(expected_trait_id)),
        ) => {
            let contract_to_check = match db
                .load_contract(contract_identifier, &StacksEpochId::Epoch21)?
            {
                Some(contract) => {
                    runtime_cost(
                        ClarityCostFunction::AnalysisFetchContractEntry,
                        tracker,
                        contract_analysis_size(&contract)?,
                    )?;
                    contract
                }
                None => {
                    runtime_cost(ClarityCostFunction::AnalysisFetchContractEntry, tracker, 1)?;
                    return Err(CheckErrors::NoSuchContract(contract_identifier.to_string()).into());
                }
            };
            let expected_trait =
                clarity2_lookup_trait(db, contract_context, expected_trait_id, tracker)?;
            contract_to_check.check_trait_compliance(
                &StacksEpochId::Epoch21,
                expected_trait_id,
                &expected_trait,
            )?;
        }
        (
            TypeSignature::ListUnionType(types),
            TypeSignature::CallableType(CallableSubtype::Trait(_)),
        ) => {
            // Verify that all types in the union implement this trait
            for subtype in types {
                clarity2_inner_type_check_type(
                    db,
                    contract_context,
                    &TypeSignature::CallableType(subtype.clone()),
                    expected_type,
                    depth + 1,
                    tracker,
                )?;
            }
        }
        (TypeSignature::NoType, _) => (),
        (_, _) => {
            if !expected_type.admits_type(&StacksEpochId::Epoch21, actual_type)? {
                return Err(
                    CheckErrors::TypeError(expected_type.clone(), actual_type.clone()).into(),
                );
            }
        }
    }
    Ok(expected_type.clone())
}

fn clarity2_lookup_trait<T: CostTracker>(
    db: &mut AnalysisDatabase,
    contract_context: Option<&ContractContext>,
    trait_id: &TraitIdentifier,
    tracker: &mut T,
) -> CheckResult<BTreeMap<ClarityName, FunctionSignature>> {
    if let Some(contract_context) = contract_context {
        // If the trait is from this contract, then it must be in the context or it doesn't exist.
        if contract_context.is_contract(&trait_id.contract_identifier) {
            return Ok(contract_context
                .get_trait(trait_id)
                .ok_or(CheckErrors::NoSuchTrait(
                    trait_id.contract_identifier.to_string(),
                    trait_id.name.to_string(),
                ))?
                .clone());
        }
        if let Some(trait_sig) = contract_context.get_trait(trait_id) {
            return Ok(trait_sig.clone());
        }
    }

    match db.get_defined_trait(
        &trait_id.contract_identifier,
        &trait_id.name,
        &StacksEpochId::Epoch21,
    ) {
        Ok(Some(trait_sig)) => {
            let type_size = trait_type_size(&trait_sig)?;
            runtime_cost(
                ClarityCostFunction::AnalysisUseTraitEntry,
                tracker,
                type_size,
            )?;
            Ok(trait_sig)
        }
        Ok(None) => {
            runtime_cost(ClarityCostFunction::AnalysisUseTraitEntry, tracker, 1)?;
            Err(CheckErrors::NoSuchTrait(
                trait_id.contract_identifier.to_string(),
                trait_id.name.to_string(),
            )
            .into())
        }
        Err(e) => {
            runtime_cost(ClarityCostFunction::AnalysisUseTraitEntry, tracker, 1)?;
            Err(e)
        }
    }
}

fn trait_type_size(trait_sig: &BTreeMap<ClarityName, FunctionSignature>) -> CheckResult<u64> {
    let mut total_size = 0;
    for (_func_name, value) in trait_sig.iter() {
        total_size = total_size.cost_overflow_add(value.total_type_size()?)?;
    }
    Ok(total_size)
}

fn contract_analysis_size(contract: &ContractAnalysis) -> CheckResult<u64> {
    let mut total_size = contract.public_function_types.len() as u64;
    total_size = total_size.cost_overflow_add(contract.read_only_function_types.len() as u64)?;
    Ok(total_size)
}

fn type_reserved_variable(
    variable_name: &str,
    version: &ClarityVersion,
) -> CheckResult<Option<TypeSignature>> {
    if let Some(variable) = NativeVariables::lookup_by_name_at_version(variable_name, version) {
        use crate::vm::variables::NativeVariables::*;
        let var_type = match variable {
            TxSender => TypeSignature::PrincipalType,
            TxSponsor => TypeSignature::new_option(TypeSignature::PrincipalType)
                .map_err(|_| CheckErrors::Expects("Bad construction".into()))?,
            ContractCaller => TypeSignature::PrincipalType,
            BlockHeight => TypeSignature::UIntType,
            StacksBlockHeight => TypeSignature::UIntType,
            TenureHeight => TypeSignature::UIntType,
            BurnBlockHeight => TypeSignature::UIntType,
            NativeNone => TypeSignature::new_option(no_type())
                .map_err(|_| CheckErrors::Expects("Bad construction".into()))?,
            NativeTrue => TypeSignature::BoolType,
            NativeFalse => TypeSignature::BoolType,
            TotalLiquidMicroSTX => TypeSignature::UIntType,
            Regtest => TypeSignature::BoolType,
            Mainnet => TypeSignature::BoolType,
            ChainId => TypeSignature::UIntType,
        };
        Ok(Some(var_type))
    } else {
        Ok(None)
    }
}

pub fn no_type() -> TypeSignature {
    TypeSignature::NoType
}

impl<'a, 'b> TypeChecker<'a, 'b> {
    pub fn new(
        epoch: &StacksEpochId,
        db: &'a mut AnalysisDatabase<'b>,
        cost_track: LimitedCostTracker,
        contract_identifier: &QualifiedContractIdentifier,
        clarity_version: &ClarityVersion,
        build_type_map: bool,
    ) -> TypeChecker<'a, 'b> {
        Self {
            epoch: *epoch,
            db,
            cost_track,
            contract_context: ContractContext::new(contract_identifier.clone(), *clarity_version),
            function_return_tracker: None,
            type_map: TypeMap::new(build_type_map),
            clarity_version: *clarity_version,
        }
    }

    fn into_contract_analysis(
        self,
        contract_analysis: &mut ContractAnalysis,
    ) -> LimitedCostTracker {
        self.contract_context
            .into_contract_analysis(contract_analysis);
        contract_analysis.type_map = Some(self.type_map);
        self.cost_track
    }

    pub fn track_return_type(&mut self, return_type: TypeSignature) -> CheckResult<()> {
        runtime_cost(
            ClarityCostFunction::AnalysisTypeCheck,
            self,
            return_type.type_size()?,
        )?;

        match self.function_return_tracker {
            Some(ref mut tracker) => {
                let new_type = match tracker.take() {
                    Some(expected_type) => TypeSignature::least_supertype(
                        &StacksEpochId::Epoch21,
                        &expected_type,
                        &return_type,
                    )
                    .map_err(|_| CheckErrors::ReturnTypesMustMatch(expected_type, return_type))?,
                    None => return_type,
                };

                tracker.replace(new_type);
                Ok(())
            }
            None => {
                // not in a defining function, so it's okay if aborts, etc., are trying
                //   to return random things, as it'll just error in any case.
                Ok(())
            }
        }
    }

    pub fn run(&mut self, contract_analysis: &ContractAnalysis) -> CheckResult<()> {
        // charge for the eventual storage cost of the analysis --
        //  it is linear in the size of the AST.
        let mut size: u64 = 0;
        for exp in contract_analysis.expressions.iter() {
            depth_traverse(exp, |_x| match size.cost_overflow_add(1) {
                Ok(new_size) => {
                    size = new_size;
                    Ok(())
                }
                Err(e) => Err(e),
            })?
            .ok_or_else(|| CheckErrors::Expects("Expected a depth result".into()))?;
        }

        runtime_cost(ClarityCostFunction::AnalysisStorage, self, size)?;

        let mut local_context = TypingContext::new(StacksEpochId::Epoch21, self.clarity_version);

        for exp in contract_analysis.expressions.iter() {
            let mut result_res = self.try_type_check_define(exp, &mut local_context);
            if let Err(ref mut error) = result_res {
                if !error.has_expression() {
                    error.set_expression(exp);
                }
            }
            let result = result_res?;
            if result.is_none() {
                // was _not_ a define statement, so handle like a normal statement.
                self.type_check(exp, &local_context)?;
            }
        }
        Ok(())
    }

    // Type check an expression, with an expected_type that should _admit_ the expression.
    pub fn type_check_expects(
        &mut self,
        expr: &SymbolicExpression,
        context: &TypingContext,
        expected_type: &TypeSignature,
    ) -> TypeResult {
        // Clarity 2 allows traits embedded in compound types and allows
        // implicit casts between compatible traits, while Clarity 1 does not.
        if self.clarity_version >= ClarityVersion::Clarity2 {
            self.clarity2_type_check_expects(expr, context, expected_type)
                .map_err(|mut e| {
                    if !e.has_expression() {
                        e.set_expression(expr)
                    }
                    e
                })
        } else {
            self.clarity1_type_check_expects(expr, context, expected_type)
        }
    }

    // Type checks an expression, recursively type checking its subexpressions
    pub fn type_check(&mut self, expr: &SymbolicExpression, context: &TypingContext) -> TypeResult {
        runtime_cost(ClarityCostFunction::AnalysisVisit, self, 0)?;

        let mut result = self.inner_type_check(expr, context);

        if let Err(ref mut error) = result {
            if !error.has_expression() {
                error.set_expression(expr);
            }
        }

        result
    }

    fn type_check_consecutive_statements(
        &mut self,
        args: &[SymbolicExpression],
        context: &TypingContext,
    ) -> TypeResult {
        let mut last_return = None;
        let mut return_failure = Ok(());
        for ix in 0..args.len() {
            let type_return = self.type_check(&args[ix], context)?;
            if ix + 1 < args.len() {
                if type_return.is_response_type() {
                    return_failure = Err(CheckErrors::UncheckedIntermediaryResponses);
                }
            } else {
                last_return = Some(type_return);
            }
        }

        let last_return = last_return
            .ok_or_else(|| CheckError::new(CheckErrors::CheckerImplementationFailure))?;
        return_failure?;

        Ok(last_return)
    }

    fn type_check_all(
        &mut self,
        args: &[SymbolicExpression],
        context: &TypingContext,
    ) -> CheckResult<Vec<TypeSignature>> {
        let mut result = Vec::with_capacity(args.len());
        for arg in args.iter() {
            // don't use map here, since type_check has side-effects.
            result.push(self.type_check(arg, context)?)
        }
        Ok(result)
    }

    fn type_check_function_type(
        &mut self,
        func_type: &FunctionType,
        args: &[SymbolicExpression],
        context: &TypingContext,
        epoch: StacksEpochId,
        clarity_version: ClarityVersion,
    ) -> TypeResult {
        if epoch <= StacksEpochId::Epoch2_05 {
            let typed_args = self.type_check_all(args, context)?;
            return func_type.check_args(self, &typed_args, epoch, clarity_version);
        }
        // use func_type visitor pattern
        let mut accumulated_type = None;
        let mut total_costs = vec![];
        let mut check_result = Ok(());
        let mut accumulated_types = Vec::new();
        for (arg_ix, arg_expr) in args.iter().enumerate() {
            let arg_type = self.type_check(arg_expr, context)?;
            if check_result.is_ok() {
                let (costs, result) = func_type.check_args_visitor_2_1(
                    self,
                    &arg_type,
                    arg_ix,
                    accumulated_type.as_ref(),
                );
                // add the accumulated type and total cost *before*
                //  checking for an error: we want the subsequent error handling
                //  to account for this cost
                accumulated_types.push(arg_type);
                total_costs.extend(costs);

                match result {
                    Ok(Some(returned_type)) => {
                        accumulated_type = Some(returned_type);
                    }
                    Ok(None) => {}
                    Err(e) => {
                        check_result = Err(e);
                    }
                };
            }
        }
        if let Err(mut check_error) = check_result {
            if let CheckErrors::IncorrectArgumentCount(expected, _actual) = check_error.err {
                check_error.err = CheckErrors::IncorrectArgumentCount(expected, args.len());
                check_error.diagnostic = Diagnostic::err(&check_error.err)
            }
            // accumulate the checking costs
            // the reason we do this now (instead of within the loop) is for backwards compatibility
            for cost in total_costs.into_iter() {
                self.add_cost(cost?)?;
            }

            return Err(check_error);
        }
        // otherwise, just invoke the normal checking routine
        func_type.check_args(self, &accumulated_types, epoch, clarity_version)
    }

    fn get_function_type(&self, function_name: &str) -> Option<FunctionType> {
        self.contract_context
            .get_function_type(function_name)
            .cloned()
    }

    #[allow(clippy::unnecessary_lazy_evaluations)]
    fn type_check_define_function(
        &mut self,
        signature: &[SymbolicExpression],
        body: &SymbolicExpression,
        context: &TypingContext,
    ) -> CheckResult<(ClarityName, FixedFunction)> {
        let (function_name, args) = signature
            .split_first()
            .ok_or(CheckErrors::RequiresAtLeastArguments(1, 0))?;
        let function_name = function_name
            .match_atom()
            .ok_or(CheckErrors::BadFunctionName)?;
        let args = parse_name_type_pairs::<()>(StacksEpochId::Epoch21, args, &mut ())
            .map_err(|_| CheckErrors::BadSyntaxBinding)?;

        if self.function_return_tracker.is_some() {
            return Err(CheckErrors::Expects(
                "Interpreter error: Previous function define left dirty typecheck state.".into(),
            )
            .into());
        }

        let mut function_context = context.extend()?;
        let mut tracked_mem = 0u64;
        for (arg_name, arg_type) in args.iter() {
            self.contract_context.check_name_used(arg_name)?;

            if self.epoch.analysis_memory() {
                let added_memory = u64::from(arg_name.len())
                    .checked_add(arg_type.type_size()?.into())
                    .ok_or_else(|| CostErrors::CostOverflow)?;
                self.add_memory(added_memory)?;
                tracked_mem = tracked_mem
                    .checked_add(added_memory)
                    .ok_or_else(|| CostErrors::CostOverflow)?;
            }

            match arg_type {
                TypeSignature::CallableType(CallableSubtype::Trait(trait_id)) => {
                    function_context.add_trait_reference(arg_name, trait_id);
                }
                _ => {
                    function_context
                        .variable_types
                        .insert(arg_name.clone(), arg_type.clone());
                }
            }
        }

        self.function_return_tracker = Some(None);

        let return_result = self.type_check(body, &function_context);

        drop(function_context);
        self.drop_memory(tracked_mem)?;

        match return_result {
            Err(e) => {
                self.function_return_tracker = None;
                Err(e)
            }
            Ok(return_type) => {
                let return_type = {
                    if let Some(Some(ref expected)) = self.function_return_tracker {
                        // check if the computed return type matches the return type
                        //   of any early exits from the call graph (e.g., (expects ...) calls)
                        TypeSignature::least_supertype(
                            &StacksEpochId::Epoch21,
                            expected,
                            &return_type,
                        )
                        .map_err(|_| {
                            CheckErrors::ReturnTypesMustMatch(expected.clone(), return_type)
                        })?
                    } else {
                        return_type
                    }
                    .concretize()?
                };

                self.function_return_tracker = None;

                let func_args: Vec<FunctionArg> = args
                    .into_iter()
                    .map(|(arg_name, arg_type)| FunctionArg::new(arg_type, arg_name))
                    .collect();

                Ok((
                    function_name.clone(),
                    FixedFunction {
                        args: func_args,
                        returns: return_type,
                    },
                ))
            }
        }
    }

    fn type_check_define_map(
        &mut self,
        map_name: &ClarityName,
        key_type: &SymbolicExpression,
        value_type: &SymbolicExpression,
    ) -> CheckResult<(ClarityName, (TypeSignature, TypeSignature))> {
        self.type_map.set_type(key_type, no_type())?;
        self.type_map.set_type(value_type, no_type())?;
        // should we set the type of the subexpressions of the signature to no-type as well?

        let key_type = TypeSignature::parse_type_repr(StacksEpochId::Epoch21, key_type, &mut ())
            .map_err(|_| CheckErrors::BadMapTypeDefinition)?;
        let value_type =
            TypeSignature::parse_type_repr(StacksEpochId::Epoch21, value_type, &mut ())
                .map_err(|_| CheckErrors::BadMapTypeDefinition)?;

        Ok((map_name.clone(), (key_type, value_type)))
    }

    // Aaron: note, using lazy statics here would speed things up a bit and reduce clone()s
    fn try_native_function_check(
        &mut self,
        function: &str,
        args: &[SymbolicExpression],
        context: &TypingContext,
    ) -> Option<TypeResult> {
        if let Some(ref native_function) =
            NativeFunctions::lookup_by_name_at_version(function, &self.clarity_version)
        {
            let typed_function = match TypedNativeFunction::type_native_function(native_function) {
                Ok(f) => f,
                Err(e) => return Some(Err(e.into())),
            };
            Some(typed_function.type_check_application(self, args, context))
        } else {
            None
        }
    }

    fn type_check_function_application(
        &mut self,
        expression: &[SymbolicExpression],
        context: &TypingContext,
    ) -> TypeResult {
        let (function_name, args) = expression
            .split_first()
            .ok_or(CheckErrors::NonFunctionApplication)?;

        self.type_map.set_type(function_name, no_type())?;
        let function_name = function_name
            .match_atom()
            .ok_or(CheckErrors::NonFunctionApplication)?;

        if let Some(type_result) = self.try_native_function_check(function_name, args, context) {
            type_result
        } else {
            let function = match self.get_function_type(function_name) {
                Some(FunctionType::Fixed(function)) => Ok(function),
                _ => Err(CheckErrors::UnknownFunction(function_name.to_string())),
            }?;

            for (expected_type, found_type) in function.args.iter().map(|x| &x.signature).zip(args)
            {
                self.type_check_expects(found_type, context, expected_type)?;
            }

            Ok(function.returns)
        }
    }

    fn lookup_variable(&mut self, name: &str, context: &TypingContext) -> TypeResult {
        runtime_cost(ClarityCostFunction::AnalysisLookupVariableConst, self, 0)?;

        if let Some(type_result) = type_reserved_variable(name, &self.clarity_version)? {
            Ok(type_result)
        } else if let Some(type_result) = self.contract_context.get_variable_type(name) {
            Ok(type_result.clone())
        } else if let Some(type_result) = context.lookup_trait_reference_type(name) {
            Ok(TypeSignature::CallableType(CallableSubtype::Trait(
                type_result.clone(),
            )))
        } else {
            runtime_cost(
                ClarityCostFunction::AnalysisLookupVariableDepth,
                self,
                context.depth,
            )?;

            if let Some(type_result) = context.lookup_variable_type(name) {
                Ok(type_result.clone())
            } else {
                Err(CheckErrors::UndefinedVariable(name.to_string()).into())
            }
        }
    }

    fn clarity1_type_check_expects(
        &mut self,
        expr: &SymbolicExpression,
        context: &TypingContext,
        expected_type: &TypeSignature,
    ) -> TypeResult {
        if let (
            LiteralValue(Value::Principal(PrincipalData::Contract(ref contract_identifier))),
            TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)),
        ) = (&expr.expr, expected_type)
        {
            let contract_to_check = self
                .db
                .load_contract(contract_identifier, &StacksEpochId::Epoch21)?
                .ok_or(CheckErrors::NoSuchContract(contract_identifier.to_string()))?;

            let contract_defining_trait = self
                .db
                .load_contract(
                    &trait_identifier.contract_identifier,
                    &StacksEpochId::Epoch21,
                )?
                .ok_or(CheckErrors::NoSuchContract(
                    trait_identifier.contract_identifier.to_string(),
                ))?;

            let trait_definition = contract_defining_trait
                .get_defined_trait(&trait_identifier.name)
                .ok_or(CheckErrors::NoSuchTrait(
                    trait_identifier.contract_identifier.to_string(),
                    trait_identifier.name.to_string(),
                ))?;

            contract_to_check.check_trait_compliance(
                &StacksEpochId::Epoch21,
                trait_identifier,
                trait_definition,
            )?;
            return Ok(expected_type.clone());
        }

        let actual_type = self.type_check(expr, context)?;
        analysis_typecheck_cost(self, expected_type, &actual_type)?;

        if !expected_type.admits_type(&StacksEpochId::Epoch21, &actual_type)? {
            let mut err: CheckError =
                CheckErrors::TypeError(expected_type.clone(), actual_type).into();
            err.set_expression(expr);
            Err(err)
        } else {
            Ok(actual_type)
        }
    }

    fn clarity2_type_check_expects(
        &mut self,
        expr: &SymbolicExpression,
        context: &TypingContext,
        expected_type: &TypeSignature,
    ) -> TypeResult {
        let mut expr_type = match expr.expr {
            AtomValue(ref value) => TypeSignature::type_of(value)?,
            LiteralValue(ref value) => TypeSignature::literal_type_of(value)?,
            Atom(ref name) => self.lookup_variable(name, context)?,
            List(ref expression) => self.type_check_function_application(expression, context)?,
            TraitReference(_, _) | Field(_) => {
                return Err(CheckErrors::UnexpectedTraitOrFieldReference.into());
            }
        };

        analysis_typecheck_cost(self, expected_type, &expr_type)?;
        clarity2_inner_type_check_type(
            self.db,
            Some(&self.contract_context),
            &expr_type,
            expected_type,
            1,
            &mut self.cost_track,
        )?;

        // If we reach here with no errors, then the expression can be
        // treated as the expected type.
        expr_type = expected_type.clone();

        runtime_cost(
            ClarityCostFunction::AnalysisTypeAnnotate,
            self,
            expr_type.type_size()?,
        )?;
        self.type_map.set_type(expr, expr_type.clone())?;
        Ok(expr_type)
    }

    fn inner_type_check(
        &mut self,
        expr: &SymbolicExpression,
        context: &TypingContext,
    ) -> TypeResult {
        let expr_type = match expr.expr {
            AtomValue(ref value) => TypeSignature::type_of(value)?,
            LiteralValue(ref value) => TypeSignature::literal_type_of(value)?,
            Atom(ref name) => self.lookup_variable(name, context)?,
            List(ref expression) => self.type_check_function_application(expression, context)?,
            TraitReference(_, _) | Field(_) => {
                return Err(CheckErrors::UnexpectedTraitOrFieldReference.into());
            }
        };

        runtime_cost(
            ClarityCostFunction::AnalysisTypeAnnotate,
            self,
            expr_type.type_size()?,
        )?;
        self.type_map.set_type(expr, expr_type.clone())?;
        Ok(expr_type)
    }

    fn type_check_define_variable(
        &mut self,
        var_name: &ClarityName,
        var_type: &SymbolicExpression,
        context: &mut TypingContext,
    ) -> CheckResult<(ClarityName, TypeSignature)> {
        let var_type = self.type_check(var_type, context)?;
        Ok((var_name.clone(), var_type))
    }

    fn type_check_define_persisted_variable(
        &mut self,
        var_name: &ClarityName,
        var_type: &SymbolicExpression,
        initial: &SymbolicExpression,
        context: &mut TypingContext,
    ) -> CheckResult<(ClarityName, TypeSignature)> {
        let expected_type =
            TypeSignature::parse_type_repr::<()>(StacksEpochId::Epoch21, var_type, &mut ())
                .map_err(|_e| CheckErrors::DefineVariableBadSignature)?;

        self.type_check_expects(initial, context, &expected_type)?;

        Ok((var_name.clone(), expected_type))
    }

    fn type_check_define_ft(
        &mut self,
        token_name: &ClarityName,
        bound: Option<&SymbolicExpression>,
        context: &mut TypingContext,
    ) -> CheckResult<ClarityName> {
        if let Some(bound) = bound {
            self.type_check_expects(bound, context, &TypeSignature::UIntType)?;
        }

        Ok(token_name.clone())
    }

    fn type_check_define_nft(
        &mut self,
        asset_name: &ClarityName,
        nft_type: &SymbolicExpression,
        _context: &mut TypingContext,
    ) -> CheckResult<(ClarityName, TypeSignature)> {
        let asset_type =
            TypeSignature::parse_type_repr::<()>(StacksEpochId::Epoch21, nft_type, &mut ())
                .map_err(|_| CheckErrors::DefineNFTBadSignature)?;

        Ok((asset_name.clone(), asset_type))
    }

    fn type_check_define_trait(
        &mut self,
        trait_name: &ClarityName,
        function_types: &[SymbolicExpression],
        _context: &mut TypingContext,
    ) -> CheckResult<(ClarityName, BTreeMap<ClarityName, FunctionSignature>)> {
        let trait_signature = TypeSignature::parse_trait_type_repr(
            function_types,
            &mut (),
            StacksEpochId::Epoch21,
            self.clarity_version,
        )?;

        Ok((trait_name.clone(), trait_signature))
    }

    // Checks if an expression is a _define_ expression, and if so, typechecks it. Otherwise, it returns Ok(None)
    fn try_type_check_define(
        &mut self,
        expression: &SymbolicExpression,
        context: &mut TypingContext,
    ) -> CheckResult<Option<()>> {
        if let Some(define_type) = DefineFunctionsParsed::try_parse(expression)? {
            match define_type {
                DefineFunctionsParsed::Constant { name, value } => {
                    let (v_name, v_type) = self.type_check_define_variable(name, value, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        v_type.type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(v_name.len().into())?;
                        self.add_memory(v_type.type_size()?.into())?;
                    }
                    self.contract_context.add_variable_type(v_name, v_type)?;
                }
                DefineFunctionsParsed::PrivateFunction { signature, body } => {
                    let (f_name, f_type) =
                        self.type_check_define_function(signature, body, context)?;

                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        f_type.total_type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(f_name.len().into())?;
                        self.add_memory(f_type.total_type_size()?)?;
                    }
                    self.contract_context
                        .add_private_function_type(f_name, FunctionType::Fixed(f_type))?;
                }
                DefineFunctionsParsed::PublicFunction { signature, body } => {
                    let (f_name, f_type) =
                        self.type_check_define_function(signature, body, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        f_type.total_type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(f_name.len().into())?;
                        self.add_memory(f_type.total_type_size()?)?;
                    }
                    if f_type.returns.is_response_type() {
                        self.contract_context
                            .add_public_function_type(f_name, FunctionType::Fixed(f_type))?;
                        return Ok(Some(()));
                    } else {
                        return Err(
                            CheckErrors::PublicFunctionMustReturnResponse(f_type.returns).into(),
                        );
                    }
                }
                DefineFunctionsParsed::ReadOnlyFunction { signature, body } => {
                    let (f_name, f_type) =
                        self.type_check_define_function(signature, body, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        f_type.total_type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(f_name.len().into())?;
                        self.add_memory(f_type.total_type_size()?)?;
                    }
                    self.contract_context
                        .add_read_only_function_type(f_name, FunctionType::Fixed(f_type))?;
                }
                DefineFunctionsParsed::Map {
                    name,
                    key_type,
                    value_type,
                } => {
                    let (f_name, map_type) =
                        self.type_check_define_map(name, key_type, value_type)?;
                    let total_type_size = u64::from(map_type.0.type_size()?)
                        .cost_overflow_add(u64::from(map_type.1.type_size()?))?;
                    runtime_cost(ClarityCostFunction::AnalysisBindName, self, total_type_size)?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(f_name.len().into())?;
                        self.add_memory(map_type.0.type_size()?.into())?;
                        self.add_memory(map_type.1.type_size()?.into())?;
                    }
                    self.contract_context.add_map_type(f_name, map_type)?;
                }
                DefineFunctionsParsed::PersistedVariable {
                    name,
                    data_type,
                    initial,
                } => {
                    let (v_name, v_type) = self
                        .type_check_define_persisted_variable(name, data_type, initial, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        v_type.type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(v_name.len().into())?;
                        self.add_memory(v_type.type_size()?.into())?;
                    }
                    self.contract_context
                        .add_persisted_variable_type(v_name, v_type)?;
                }
                DefineFunctionsParsed::BoundedFungibleToken { name, max_supply } => {
                    let token_name = self.type_check_define_ft(name, Some(max_supply), context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        TypeSignature::UIntType.type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(token_name.len().into())?;
                        self.add_memory(TypeSignature::UIntType.type_size()?.into())?;
                    }
                    self.contract_context.add_ft(token_name)?;
                }
                DefineFunctionsParsed::UnboundedFungibleToken { name } => {
                    let token_name = self.type_check_define_ft(name, None, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        TypeSignature::UIntType.type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(token_name.len().into())?;
                        self.add_memory(TypeSignature::UIntType.type_size()?.into())?;
                    }
                    self.contract_context.add_ft(token_name)?;
                }
                DefineFunctionsParsed::NonFungibleToken { name, nft_type } => {
                    let (token_name, token_type) =
                        self.type_check_define_nft(name, nft_type, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        token_type.type_size()?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(token_name.len().into())?;
                        self.add_memory(token_type.type_size()?.into())?;
                    }
                    self.contract_context.add_nft(token_name, token_type)?;
                }
                DefineFunctionsParsed::Trait { name, functions } => {
                    let (trait_name, trait_signature) =
                        self.type_check_define_trait(name, functions, context)?;
                    runtime_cost(
                        ClarityCostFunction::AnalysisBindName,
                        self,
                        trait_type_size(&trait_signature)?,
                    )?;
                    if self.epoch.analysis_memory() {
                        self.add_memory(trait_name.len().into())?;
                        self.add_memory(trait_type_size(&trait_signature)?)?;
                    }
                    self.contract_context
                        .add_defined_trait(trait_name, trait_signature)?;
                }
                DefineFunctionsParsed::UseTrait {
                    name,
                    trait_identifier,
                } => {
                    let result = self.db.get_defined_trait(
                        &trait_identifier.contract_identifier,
                        &trait_identifier.name,
                        &StacksEpochId::Epoch21,
                    )?;
                    match result {
                        Some(trait_sig) => {
                            let type_size = trait_type_size(&trait_sig)?;
                            runtime_cost(
                                ClarityCostFunction::AnalysisUseTraitEntry,
                                self,
                                type_size,
                            )?;
                            runtime_cost(ClarityCostFunction::AnalysisBindName, self, type_size)?;
                            if self.epoch.analysis_memory() {
                                self.add_memory(trait_identifier.name.len().into())?;
                                self.add_memory(type_size)?;
                            }
                            self.contract_context.add_used_trait(
                                name.clone(),
                                trait_identifier.clone(),
                                trait_sig,
                            )?
                        }
                        None => {
                            // still had to do a db read, even if it didn't exist!
                            runtime_cost(ClarityCostFunction::AnalysisUseTraitEntry, self, 1)?;
                            return Err(CheckErrors::TraitReferenceUnknown(name.to_string()).into());
                        }
                    }
                }
                DefineFunctionsParsed::ImplTrait { trait_identifier } => {
                    if self.epoch.analysis_memory() {
                        self.add_memory(trait_identifier.name.len().into())?;
                    }
                    self.contract_context
                        .add_implemented_trait(trait_identifier.clone())?;
                }
            };
            Ok(Some(()))
        } else {
            // not a define.
            Ok(None)
        }
    }
}
