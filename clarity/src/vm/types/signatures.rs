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

use std::collections::btree_map::Entry;
use std::collections::{hash_map, BTreeMap};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::Arc;
use std::{cmp, fmt};

// TypeSignatures
use hashbrown::HashSet;
use lazy_static::lazy_static;
use stacks_common::address::c32;
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash;

use crate::vm::costs::{cost_functions, runtime_cost, CostOverflowingMath};
use crate::vm::errors::{CheckErrors, Error as VMError, IncomparableError, RuntimeErrorType};
use crate::vm::representations::{
    ClarityName, ContractName, SymbolicExpression, SymbolicExpressionType, TraitDefinition,
    CONTRACT_MAX_NAME_LENGTH,
};
use crate::vm::types::{
    CharType, PrincipalData, QualifiedContractIdentifier, SequenceData, SequencedValue,
    StandardPrincipalData, TraitIdentifier, Value, MAX_TYPE_DEPTH, MAX_VALUE_SIZE,
    WRAPPER_VALUE_SIZE,
};

type Result<R> = std::result::Result<R, CheckErrors>;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Serialize, Deserialize, Hash)]
pub struct AssetIdentifier {
    pub contract_identifier: QualifiedContractIdentifier,
    pub asset_name: ClarityName,
}

impl AssetIdentifier {
    #[allow(clippy::unwrap_used)]
    pub fn STX() -> AssetIdentifier {
        AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData(0, [0u8; 20]),
                ContractName::try_from("STX".to_string()).unwrap(),
            ),
            asset_name: ClarityName::try_from("STX".to_string()).unwrap(),
        }
    }

    #[allow(clippy::unwrap_used)]
    pub fn STX_burned() -> AssetIdentifier {
        AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData(0, [0u8; 20]),
                ContractName::try_from("BURNED".to_string()).unwrap(),
            ),
            asset_name: ClarityName::try_from("BURNED".to_string()).unwrap(),
        }
    }

    pub fn sugared(&self) -> String {
        format!(".{}.{}", self.contract_identifier.name, self.asset_name)
    }
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TupleTypeSignature {
    #[serde(with = "tuple_type_map_serde")]
    type_map: Arc<BTreeMap<ClarityName, TypeSignature>>,
}

mod tuple_type_map_serde {
    use std::collections::BTreeMap;
    use std::ops::Deref;
    use std::sync::Arc;

    use serde::{Deserializer, Serializer};

    use super::TypeSignature;
    use crate::vm::ClarityName;

    pub fn serialize<S: Serializer>(
        map: &Arc<BTreeMap<ClarityName, TypeSignature>>,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        serde::Serialize::serialize(map.deref(), ser)
    }

    pub fn deserialize<'de, D>(
        deser: D,
    ) -> Result<Arc<BTreeMap<ClarityName, TypeSignature>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let map = serde::Deserialize::deserialize(deser)?;
        Ok(Arc::new(map))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BufferLength(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct StringUTF8Length(u32);

// INVARIANTS enforced by the Type Signatures.
//   1. A TypeSignature constructor will always fail rather than construct a
//        type signature for a too large or invalid type. This is why any variable length
//        type signature has a guarded constructor.
//   2. The only methods which may be called on TypeSignatures that are too large
//        (i.e., the only function that can be called by the constructor before
//         it fails) is the `.size()` method, which may be used to check the size.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeSignature {
    NoType,
    IntType,
    UIntType,
    BoolType,
    SequenceType(SequenceSubtype),
    PrincipalType,
    TupleType(TupleTypeSignature),
    OptionalType(Box<TypeSignature>),
    ResponseType(Box<(TypeSignature, TypeSignature)>),
    CallableType(CallableSubtype),
    // Suppose we have a list of contract principal literals, e.g.
    // `(list .foo .bar)`. This list could be used as a list of `principal`
    // types, or it could be passed into a function where it is used a list of
    // some trait type, which every contract in the list implements, e.g.
    // `(list 4 <my-trait>)`. There could also be a trait value, `t`, in that
    // list. In that case, the list could no longer be coerced to a list of
    // principals, but it could be coerced to a list of traits, either the type
    // of `t`, or a compatible sub-trait of that type. `ListUnionType` is a
    // data structure to maintain the set of types in the list, so that when
    // we reach the place where the coercion needs to happen, we can perform
    // the check -- see `concretize` method.
    ListUnionType(HashSet<CallableSubtype>),
    // This is used only below epoch 2.1. It has been replaced by CallableType.
    TraitReferenceType(TraitIdentifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SequenceSubtype {
    BufferType(BufferLength),
    ListType(ListTypeData),
    StringType(StringSubtype),
}

impl SequenceSubtype {
    pub fn unit_type(&self) -> Result<TypeSignature> {
        match &self {
            SequenceSubtype::ListType(ref list_data) => Ok(list_data.clone().destruct().0),
            SequenceSubtype::BufferType(_) => TypeSignature::min_buffer(),
            SequenceSubtype::StringType(StringSubtype::ASCII(_)) => {
                TypeSignature::min_string_ascii()
            }
            SequenceSubtype::StringType(StringSubtype::UTF8(_)) => TypeSignature::min_string_utf8(),
        }
    }

    pub fn is_list_type(&self) -> bool {
        matches!(self, SequenceSubtype::ListType(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StringSubtype {
    ASCII(BufferLength),
    UTF8(StringUTF8Length),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum CallableSubtype {
    Principal(QualifiedContractIdentifier),
    Trait(TraitIdentifier),
}

use self::TypeSignature::{
    BoolType, CallableType, IntType, ListUnionType, NoType, OptionalType, PrincipalType,
    ResponseType, SequenceType, TraitReferenceType, TupleType, UIntType,
};

lazy_static! {
    pub static ref BUFF_64: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(64u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_65: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(65u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_32: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(32u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_33: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(33u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_20: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(20u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_21: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(21u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_1: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(1u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
    pub static ref BUFF_16: TypeSignature = {
        #[allow(clippy::expect_used)]
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(16u32).expect("BUG: Legal Clarity buffer length marked invalid"),
        ))
    };
}

pub const ASCII_40: TypeSignature = SequenceType(SequenceSubtype::StringType(
    StringSubtype::ASCII(BufferLength(40)),
));
pub const UTF8_40: TypeSignature = SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
    StringUTF8Length(40),
)));

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ListTypeData {
    max_len: u32,
    entry_type: Box<TypeSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub args: Vec<TypeSignature>,
    pub returns: TypeSignature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixedFunction {
    pub args: Vec<FunctionArg>,
    pub returns: TypeSignature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionArgSignature {
    Union(Vec<TypeSignature>),
    Single(TypeSignature),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionReturnsSignature {
    TypeOfArgAtPosition(usize),
    Fixed(TypeSignature),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionType {
    Variadic(TypeSignature, TypeSignature),
    Fixed(FixedFunction),
    // Functions where the single input is a union type, e.g., Buffer or Int
    UnionArgs(Vec<TypeSignature>, TypeSignature),
    ArithmeticVariadic,
    ArithmeticUnary,
    ArithmeticBinary,
    ArithmeticComparison,
    Binary(
        FunctionArgSignature,
        FunctionArgSignature,
        FunctionReturnsSignature,
    ),
}

impl FunctionArgSignature {
    pub fn canonicalize(&self, epoch: &StacksEpochId) -> FunctionArgSignature {
        match self {
            FunctionArgSignature::Union(arg_types) => {
                let arg_types = arg_types
                    .iter()
                    .map(|arg_type| arg_type.canonicalize(epoch))
                    .collect();
                FunctionArgSignature::Union(arg_types)
            }
            FunctionArgSignature::Single(arg_type) => {
                let arg_type = arg_type.canonicalize(epoch);
                FunctionArgSignature::Single(arg_type)
            }
        }
    }
}

impl FunctionReturnsSignature {
    pub fn canonicalize(&self, epoch: &StacksEpochId) -> FunctionReturnsSignature {
        match self {
            FunctionReturnsSignature::TypeOfArgAtPosition(_) => self.clone(),
            FunctionReturnsSignature::Fixed(return_type) => {
                let return_type = return_type.canonicalize(epoch);
                FunctionReturnsSignature::Fixed(return_type)
            }
        }
    }
}

impl FunctionType {
    pub fn canonicalize(&self, epoch: &StacksEpochId) -> FunctionType {
        match self {
            FunctionType::Variadic(arg_type, return_type) => {
                let arg_type = arg_type.canonicalize(epoch);
                let return_type = return_type.canonicalize(epoch);
                FunctionType::Variadic(arg_type, return_type)
            }
            FunctionType::Fixed(fixed_function) => {
                let args = fixed_function
                    .args
                    .iter()
                    .map(|arg| FunctionArg {
                        signature: arg.signature.canonicalize(epoch),
                        name: arg.name.clone(),
                    })
                    .collect();
                let returns = fixed_function.returns.canonicalize(epoch);
                FunctionType::Fixed(FixedFunction { args, returns })
            }
            FunctionType::UnionArgs(arg_types, return_type) => {
                let arg_types = arg_types
                    .iter()
                    .map(|arg_type| arg_type.canonicalize(epoch))
                    .collect();
                let return_type = return_type.canonicalize(epoch);
                FunctionType::UnionArgs(arg_types, return_type)
            }
            FunctionType::ArithmeticVariadic => FunctionType::ArithmeticVariadic,
            FunctionType::ArithmeticUnary => FunctionType::ArithmeticUnary,
            FunctionType::ArithmeticBinary => FunctionType::ArithmeticBinary,
            FunctionType::ArithmeticComparison => FunctionType::ArithmeticComparison,
            FunctionType::Binary(arg1, arg2, return_type) => {
                let arg1 = arg1.canonicalize(epoch);
                let arg2 = arg2.canonicalize(epoch);
                let return_type = return_type.canonicalize(epoch);
                FunctionType::Binary(arg1, arg2, return_type)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionArg {
    pub signature: TypeSignature,
    pub name: ClarityName,
}

impl From<FixedFunction> for FunctionSignature {
    fn from(data: FixedFunction) -> FunctionSignature {
        let FixedFunction { args, returns } = data;
        let args = args.into_iter().map(|x| x.signature).collect();
        FunctionSignature { args, returns }
    }
}

impl From<ListTypeData> for TypeSignature {
    fn from(data: ListTypeData) -> Self {
        SequenceType(SequenceSubtype::ListType(data))
    }
}

impl From<TupleTypeSignature> for TypeSignature {
    fn from(data: TupleTypeSignature) -> Self {
        TupleType(data)
    }
}

impl From<&BufferLength> for u32 {
    fn from(v: &BufferLength) -> u32 {
        v.0
    }
}

impl From<BufferLength> for u32 {
    fn from(v: BufferLength) -> u32 {
        v.0
    }
}

impl TryFrom<u32> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: u32) -> Result<BufferLength> {
        if data > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(BufferLength(data))
        }
    }
}

impl TryFrom<usize> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: usize) -> Result<BufferLength> {
        if data > (MAX_VALUE_SIZE as usize) {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(BufferLength(data as u32))
        }
    }
}

impl TryFrom<i128> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: i128) -> Result<BufferLength> {
        if data > (MAX_VALUE_SIZE as i128) {
            Err(CheckErrors::ValueTooLarge)
        } else if data < 0 {
            Err(CheckErrors::ValueOutOfBounds)
        } else {
            Ok(BufferLength(data as u32))
        }
    }
}

impl From<&StringUTF8Length> for u32 {
    fn from(v: &StringUTF8Length) -> u32 {
        v.0
    }
}

impl From<StringUTF8Length> for u32 {
    fn from(v: StringUTF8Length) -> u32 {
        v.0
    }
}

impl TryFrom<u32> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: u32) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(StringUTF8Length(data))
        }
    }
}

impl TryFrom<usize> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: usize) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > (MAX_VALUE_SIZE as usize) {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(StringUTF8Length(data as u32))
        }
    }
}

impl TryFrom<i128> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: i128) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > (MAX_VALUE_SIZE as i128) {
            Err(CheckErrors::ValueTooLarge)
        } else if data < 0 {
            Err(CheckErrors::ValueOutOfBounds)
        } else {
            Ok(StringUTF8Length(data as u32))
        }
    }
}

impl ListTypeData {
    pub fn new_list(entry_type: TypeSignature, max_len: u32) -> Result<ListTypeData> {
        let would_be_depth = 1 + entry_type.depth();
        if would_be_depth > MAX_TYPE_DEPTH {
            return Err(CheckErrors::TypeSignatureTooDeep);
        }

        let list_data = ListTypeData {
            entry_type: Box::new(entry_type),
            max_len,
        };
        let would_be_size = list_data
            .inner_size()?
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if would_be_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(list_data)
        }
    }

    pub fn destruct(self) -> (TypeSignature, u32) {
        (*self.entry_type, self.max_len)
    }

    // if checks like as-max-len pass, they may _reduce_
    //   but should not increase the type signatures max length
    pub fn reduce_max_len(&mut self, new_max_len: u32) {
        if new_max_len <= self.max_len {
            self.max_len = new_max_len;
        }
    }

    pub fn get_max_len(&self) -> u32 {
        self.max_len
    }

    pub fn get_list_item_type(&self) -> &TypeSignature {
        &self.entry_type
    }
}

impl TypeSignature {
    pub fn new_option(inner_type: TypeSignature) -> Result<TypeSignature> {
        let new_size = WRAPPER_VALUE_SIZE + inner_type.size()?;
        let new_depth = 1 + inner_type.depth();
        if new_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else if new_depth > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep)
        } else {
            Ok(OptionalType(Box::new(inner_type)))
        }
    }

    pub fn new_response(ok_type: TypeSignature, err_type: TypeSignature) -> Result<TypeSignature> {
        let new_size = WRAPPER_VALUE_SIZE + cmp::max(ok_type.size()?, err_type.size()?);
        let new_depth = 1 + cmp::max(ok_type.depth(), err_type.depth());

        if new_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else if new_depth > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep)
        } else {
            Ok(ResponseType(Box::new((ok_type, err_type))))
        }
    }

    pub fn is_response_type(&self) -> bool {
        matches!(self, TypeSignature::ResponseType(_))
    }

    pub fn is_no_type(&self) -> bool {
        &TypeSignature::NoType == self
    }

    pub fn admits(&self, epoch: &StacksEpochId, x: &Value) -> Result<bool> {
        let x_type = TypeSignature::type_of(x)?;
        self.admits_type(epoch, &x_type)
    }

    pub fn admits_type(&self, epoch: &StacksEpochId, other: &TypeSignature) -> Result<bool> {
        match epoch {
            StacksEpochId::Epoch20 | StacksEpochId::Epoch2_05 => self.admits_type_v2_0(other),
            StacksEpochId::Epoch21
            | StacksEpochId::Epoch22
            | StacksEpochId::Epoch23
            | StacksEpochId::Epoch24
            | StacksEpochId::Epoch25
            | StacksEpochId::Epoch30
            | StacksEpochId::Epoch31 => self.admits_type_v2_1(other),
            StacksEpochId::Epoch10 => Err(CheckErrors::Expects("epoch 1.0 not supported".into())),
        }
    }

    pub fn admits_type_v2_0(&self, other: &TypeSignature) -> Result<bool> {
        match self {
            SequenceType(SequenceSubtype::ListType(ref my_list_type)) => {
                if let SequenceType(SequenceSubtype::ListType(other_list_type)) = other {
                    if other_list_type.max_len == 0 {
                        // if other is an empty list, a list type should always admit.
                        Ok(true)
                    } else if my_list_type.max_len >= other_list_type.max_len {
                        my_list_type
                            .entry_type
                            .admits_type_v2_0(&other_list_type.entry_type)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::BufferType(ref my_len)) => {
                if let SequenceType(SequenceSubtype::BufferType(ref other_len)) = other {
                    Ok(my_len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(other_len))) =
                    other
                {
                    Ok(len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(other_len))) =
                    other
                {
                    Ok(len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            OptionalType(ref my_inner_type) => {
                if let OptionalType(other_inner_type) = other {
                    // Option types will always admit a "NoType" OptionalType -- which
                    //   can only be a None
                    if other_inner_type.is_no_type() {
                        Ok(true)
                    } else {
                        my_inner_type.admits_type_v2_0(other_inner_type)
                    }
                } else {
                    Ok(false)
                }
            }
            ResponseType(ref my_inner_type) => {
                if let ResponseType(other_inner_type) = other {
                    // ResponseTypes admit according to the following rule:
                    //   if other.ErrType is NoType, and other.OkType admits => admit
                    //   if other.OkType is NoType, and other.ErrType admits => admit
                    //   if both OkType and ErrType admit => admit
                    //   otherwise fail.
                    if other_inner_type.0.is_no_type() {
                        my_inner_type.1.admits_type_v2_0(&other_inner_type.1)
                    } else if other_inner_type.1.is_no_type() {
                        my_inner_type.0.admits_type_v2_0(&other_inner_type.0)
                    } else {
                        Ok(my_inner_type.1.admits_type_v2_0(&other_inner_type.1)?
                            && my_inner_type.0.admits_type_v2_0(&other_inner_type.0)?)
                    }
                } else {
                    Ok(false)
                }
            }
            TupleType(ref tuple_sig) => {
                if let TupleType(ref other_tuple_sig) = other {
                    tuple_sig.admits(&StacksEpochId::Epoch2_05, other_tuple_sig)
                } else {
                    Ok(false)
                }
            }
            NoType => Err(CheckErrors::CouldNotDetermineType),
            CallableType(_) => Err(CheckErrors::Expects(
                "CallableType should not be used in epoch v2.0".into(),
            )),
            ListUnionType(_) => Err(CheckErrors::Expects(
                "ListUnionType should not be used in epoch v2.0".into(),
            )),
            _ => Ok(other == self),
        }
    }

    fn admits_type_v2_1(&self, other: &TypeSignature) -> Result<bool> {
        let other = match other.concretize() {
            Ok(other) => other,
            Err(_) => {
                return Ok(false);
            }
        };

        match self {
            SequenceType(SequenceSubtype::ListType(ref my_list_type)) => {
                if let SequenceType(SequenceSubtype::ListType(other_list_type)) = &other {
                    if other_list_type.max_len == 0 {
                        // if other is an empty list, a list type should always admit.
                        Ok(true)
                    } else if my_list_type.max_len >= other_list_type.max_len {
                        my_list_type
                            .entry_type
                            .admits_type_v2_1(&other_list_type.entry_type)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::BufferType(ref my_len)) => {
                if let SequenceType(SequenceSubtype::BufferType(ref other_len)) = &other {
                    Ok(my_len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(other_len))) =
                    &other
                {
                    Ok(len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(other_len))) =
                    &other
                {
                    Ok(len.0 >= other_len.0)
                } else {
                    Ok(false)
                }
            }
            OptionalType(ref my_inner_type) => {
                if let OptionalType(other_inner_type) = &other {
                    // Option types will always admit a "NoType" OptionalType -- which
                    //   can only be a None
                    if other_inner_type.is_no_type() {
                        Ok(true)
                    } else {
                        my_inner_type.admits_type_v2_1(other_inner_type)
                    }
                } else {
                    Ok(false)
                }
            }
            ResponseType(ref my_inner_type) => {
                if let ResponseType(other_inner_type) = &other {
                    // ResponseTypes admit according to the following rule:
                    //   if other.ErrType is NoType, and other.OkType admits => admit
                    //   if other.OkType is NoType, and other.ErrType admits => admit
                    //   if both OkType and ErrType admit => admit
                    //   otherwise fail.
                    if other_inner_type.0.is_no_type() {
                        my_inner_type.1.admits_type_v2_1(&other_inner_type.1)
                    } else if other_inner_type.1.is_no_type() {
                        my_inner_type.0.admits_type_v2_1(&other_inner_type.0)
                    } else {
                        Ok(my_inner_type.1.admits_type_v2_1(&other_inner_type.1)?
                            && my_inner_type.0.admits_type_v2_1(&other_inner_type.0)?)
                    }
                } else {
                    Ok(false)
                }
            }
            TupleType(ref tuple_sig) => {
                if let TupleType(ref other_tuple_sig) = &other {
                    tuple_sig.admits(&StacksEpochId::Epoch21, other_tuple_sig)
                } else {
                    Ok(false)
                }
            }
            NoType => Err(CheckErrors::CouldNotDetermineType),
            _ => Ok(&other == self),
        }
    }

    /// Canonicalize a type.
    /// This method will convert types from previous epochs with the appropriate
    /// types for the specified epoch.
    pub fn canonicalize(&self, epoch: &StacksEpochId) -> TypeSignature {
        match epoch {
            StacksEpochId::Epoch10
            | StacksEpochId::Epoch20
            | StacksEpochId::Epoch2_05
            // Epoch-2.2 had a regression in canonicalization, so it must be preserved here.
            | StacksEpochId::Epoch22 => self.clone(),
            // Note for future epochs: Epochs >= 2.3 should use the canonicalize_v2_1() routine
            StacksEpochId::Epoch21
            | StacksEpochId::Epoch23
            | StacksEpochId::Epoch24
            | StacksEpochId::Epoch25
            | StacksEpochId::Epoch30
            | StacksEpochId::Epoch31 => self.canonicalize_v2_1(),
        }
    }

    pub fn canonicalize_v2_1(&self) -> TypeSignature {
        match self {
            SequenceType(SequenceSubtype::ListType(ref list_type)) => {
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: list_type.max_len,
                    entry_type: Box::new(list_type.entry_type.canonicalize_v2_1()),
                }))
            }
            OptionalType(ref inner_type) => OptionalType(Box::new(inner_type.canonicalize_v2_1())),
            ResponseType(ref inner_type) => ResponseType(Box::new((
                inner_type.0.canonicalize_v2_1(),
                inner_type.1.canonicalize_v2_1(),
            ))),
            TupleType(ref tuple_sig) => {
                let mut canonicalized_fields = BTreeMap::new();
                for (field_name, field_type) in tuple_sig.get_type_map() {
                    canonicalized_fields.insert(field_name.clone(), field_type.canonicalize_v2_1());
                }
                TypeSignature::from(TupleTypeSignature {
                    type_map: Arc::new(canonicalized_fields),
                })
            }
            TraitReferenceType(trait_id) => CallableType(CallableSubtype::Trait(trait_id.clone())),
            _ => self.clone(),
        }
    }

    /// Concretize the type. The input to this method may include
    /// `ListUnionType` and the `CallableType` variant for a `principal.
    /// This method turns these "temporary" types into actual types.
    pub fn concretize(&self) -> Result<TypeSignature> {
        match self {
            ListUnionType(types) => {
                let mut is_trait = None;
                let mut is_principal = true;
                for partial in types {
                    match partial {
                        CallableSubtype::Principal(_) => {
                            if is_trait.is_some() {
                                return Err(CheckErrors::TypeError(
                                    TypeSignature::CallableType(partial.clone()),
                                    TypeSignature::PrincipalType,
                                ));
                            } else {
                                is_principal = true;
                            }
                        }
                        CallableSubtype::Trait(t) => {
                            if is_principal {
                                return Err(CheckErrors::TypeError(
                                    TypeSignature::PrincipalType,
                                    TypeSignature::CallableType(partial.clone()),
                                ));
                            } else {
                                is_trait = Some(t.clone());
                            }
                        }
                    }
                }
                if let Some(t) = is_trait {
                    Ok(TypeSignature::CallableType(CallableSubtype::Trait(t)))
                } else {
                    Ok(TypeSignature::PrincipalType)
                }
            }
            CallableType(CallableSubtype::Principal(_)) => Ok(TypeSignature::PrincipalType),
            _ => Ok(self.clone()),
        }
    }

    /// Goes recursively through a type to [concretize](TypeSignature::concretize)
    /// the inner [ListUnionType] and [CallableType] variants.
    pub fn concretize_deep(self) -> Result<Self> {
        match self {
            TypeSignature::NoType
            | TypeSignature::IntType
            | TypeSignature::UIntType
            | TypeSignature::BoolType
            | TypeSignature::PrincipalType
            | TypeSignature::SequenceType(SequenceSubtype::BufferType(_))
            | TypeSignature::SequenceType(SequenceSubtype::StringType(_))
            | TypeSignature::TraitReferenceType(_) => Ok(self),
            TypeSignature::OptionalType(opt_ty) => Ok(TypeSignature::OptionalType(Box::new(
                opt_ty.concretize_deep()?,
            ))),
            TypeSignature::ResponseType(resp_ty) => {
                let (ok_ty, err_ty) = *resp_ty;
                Ok(TypeSignature::ResponseType(Box::new((
                    ok_ty.concretize_deep()?,
                    err_ty.concretize_deep()?,
                ))))
            }
            TypeSignature::SequenceType(SequenceSubtype::ListType(ListTypeData {
                max_len,
                entry_type,
            })) => Ok(TypeSignature::SequenceType(SequenceSubtype::ListType(
                ListTypeData {
                    max_len,
                    entry_type: Box::new(entry_type.concretize_deep()?),
                },
            ))),
            TypeSignature::TupleType(TupleTypeSignature { type_map }) => {
                let mut type_map_ref = type_map.as_ref().clone();
                for ty in type_map_ref.values_mut() {
                    *ty = ty.clone().concretize_deep()?;
                }
                Ok(TupleTypeSignature {
                    type_map: Arc::new(type_map_ref),
                }
                .into())
            }
            TypeSignature::ListUnionType(_) | TypeSignature::CallableType(_) => self.concretize(),
        }
    }
}

impl TryFrom<Vec<(ClarityName, TypeSignature)>> for TupleTypeSignature {
    type Error = CheckErrors;
    fn try_from(type_data: Vec<(ClarityName, TypeSignature)>) -> Result<TupleTypeSignature> {
        if type_data.is_empty() {
            return Err(CheckErrors::EmptyTuplesNotAllowed);
        }

        let mut type_map = BTreeMap::new();
        for (name, type_info) in type_data.into_iter() {
            if let Entry::Vacant(e) = type_map.entry(name.clone()) {
                e.insert(type_info);
            } else {
                return Err(CheckErrors::NameAlreadyUsed(name.into()));
            }
        }
        TupleTypeSignature::try_from(type_map)
    }
}

impl TryFrom<BTreeMap<ClarityName, TypeSignature>> for TupleTypeSignature {
    type Error = CheckErrors;
    fn try_from(type_map: BTreeMap<ClarityName, TypeSignature>) -> Result<TupleTypeSignature> {
        if type_map.is_empty() {
            return Err(CheckErrors::EmptyTuplesNotAllowed);
        }
        for child_sig in type_map.values() {
            if (1 + child_sig.depth()) > MAX_TYPE_DEPTH {
                return Err(CheckErrors::TypeSignatureTooDeep);
            }
        }
        let type_map = Arc::new(type_map.into_iter().collect());
        let result = TupleTypeSignature { type_map };
        let would_be_size = result
            .inner_size()?
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if would_be_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(result)
        }
    }
}

impl TupleTypeSignature {
    /// Return the number of fields in this tuple type
    pub fn len(&self) -> u64 {
        self.type_map.len() as u64
    }

    /// Returns whether the tuple type is empty
    pub fn is_empty(&self) -> bool {
        self.type_map.is_empty()
    }

    pub fn field_type(&self, field: &str) -> Option<&TypeSignature> {
        self.type_map.get(field)
    }

    pub fn get_type_map(&self) -> &BTreeMap<ClarityName, TypeSignature> {
        &self.type_map
    }

    pub fn admits(&self, epoch: &StacksEpochId, other: &TupleTypeSignature) -> Result<bool> {
        if self.type_map.len() != other.type_map.len() {
            return Ok(false);
        }

        for (name, my_type_sig) in self.type_map.iter() {
            if let Some(other_type_sig) = other.type_map.get(name) {
                if !my_type_sig.admits_type(epoch, other_type_sig)? {
                    return Ok(false);
                }
            } else {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn parse_name_type_pair_list<A: CostTracker>(
        epoch: StacksEpochId,
        type_def: &SymbolicExpression,
        accounting: &mut A,
    ) -> Result<TupleTypeSignature> {
        if let SymbolicExpressionType::List(ref name_type_pairs) = type_def.expr {
            let mapped_key_types = parse_name_type_pairs(epoch, name_type_pairs, accounting)?;
            TupleTypeSignature::try_from(mapped_key_types)
        } else {
            Err(CheckErrors::BadSyntaxExpectedListOfPairs)
        }
    }

    pub fn shallow_merge(&mut self, update: &mut TupleTypeSignature) {
        Arc::make_mut(&mut self.type_map).append(Arc::make_mut(&mut update.type_map));
    }
}

impl FixedFunction {
    pub fn total_type_size(&self) -> Result<u64> {
        let mut function_type_size = u64::from(self.returns.type_size()?);
        for arg in self.args.iter() {
            function_type_size =
                function_type_size.cost_overflow_add(u64::from(arg.signature.type_size()?))?;
        }
        Ok(function_type_size)
    }
}

impl FunctionSignature {
    pub fn total_type_size(&self) -> Result<u64> {
        let mut function_type_size = u64::from(self.returns.type_size()?);
        for arg in self.args.iter() {
            function_type_size =
                function_type_size.cost_overflow_add(u64::from(arg.type_size()?))?;
        }
        Ok(function_type_size)
    }

    pub fn check_args_trait_compliance(
        &self,
        epoch: &StacksEpochId,
        args: Vec<TypeSignature>,
    ) -> Result<bool> {
        if args.len() != self.args.len() {
            return Ok(false);
        }
        let args_iter = self.args.iter().zip(args.iter());
        for (expected_arg, arg) in args_iter {
            if !arg.admits_type(epoch, expected_arg)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub fn canonicalize(&self, epoch: &StacksEpochId) -> FunctionSignature {
        let canonicalized_args = self
            .args
            .iter()
            .map(|arg| arg.canonicalize(epoch))
            .collect();

        FunctionSignature {
            args: canonicalized_args,
            returns: self.returns.canonicalize(epoch),
        }
    }
}

impl FunctionArg {
    pub fn new(signature: TypeSignature, name: ClarityName) -> FunctionArg {
        FunctionArg { signature, name }
    }
}

impl TypeSignature {
    pub fn empty_buffer() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::BufferType(
            0_u32.try_into().map_err(|_| {
                CheckErrors::Expects("FAIL: Empty clarity value size is not realizable".into())
            })?,
        )))
    }

    pub fn min_buffer() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::BufferType(
            1_u32.try_into().map_err(|_| {
                CheckErrors::Expects("FAIL: Min clarity value size is not realizable".into())
            })?,
        )))
    }

    pub fn min_string_ascii() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(1_u32.try_into().map_err(|_| {
                CheckErrors::Expects("FAIL: Min clarity value size is not realizable".into())
            })?),
        )))
    }

    pub fn min_string_utf8() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::StringType(
            StringSubtype::UTF8(1_u32.try_into().map_err(|_| {
                CheckErrors::Expects("FAIL: Min clarity value size is not realizable".into())
            })?),
        )))
    }

    pub fn max_string_ascii() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(BufferLength::try_from(MAX_VALUE_SIZE).map_err(|_| {
                CheckErrors::Expects(
                    "FAIL: Max Clarity Value Size is no longer realizable in ASCII Type".into(),
                )
            })?),
        )))
    }

    pub fn max_string_utf8() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::StringType(
            StringSubtype::UTF8(StringUTF8Length::try_from(MAX_VALUE_SIZE / 4).map_err(|_| {
                CheckErrors::Expects(
                    "FAIL: Max Clarity Value Size is no longer realizable in UTF8 Type".into(),
                )
            })?),
        )))
    }

    pub fn max_buffer() -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(MAX_VALUE_SIZE).map_err(|_| {
                CheckErrors::Expects(
                    "FAIL: Max Clarity Value Size is no longer realizable in Buffer Type".into(),
                )
            })?,
        )))
    }

    pub fn contract_name_string_ascii_type() -> Result<TypeSignature> {
        TypeSignature::bound_string_ascii_type(CONTRACT_MAX_NAME_LENGTH.try_into().map_err(
            |_| CheckErrors::Expects("FAIL: contract name max length exceeds u32 space".into()),
        )?)
    }

    pub fn bound_string_ascii_type(max_len: u32) -> Result<TypeSignature> {
        Ok(SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(BufferLength::try_from(max_len).map_err(|_| {
                CheckErrors::Expects(
                    "FAIL: Max Clarity Value Size is no longer realizable in ASCII Type".into(),
                )
            })?),
        )))
    }

    /// If one of the types is a NoType, return Ok(the other type), otherwise return least_supertype(a, b)
    pub fn factor_out_no_type(
        epoch: &StacksEpochId,
        a: &TypeSignature,
        b: &TypeSignature,
    ) -> Result<TypeSignature> {
        if a.is_no_type() {
            Ok(b.clone())
        } else if b.is_no_type() {
            Ok(a.clone())
        } else {
            Self::least_supertype(epoch, a, b)
        }
    }

    ///
    /// This function returns the most-restrictive type that admits _both_ A and B (something like a least common supertype),
    /// or Errors if no such type exists. On error, it throws NoSuperType(A,B), unless a constructor error'ed -- in which case,
    /// it throws the constructor's error.
    ///
    ///  For two Tuples:
    ///      least_supertype(A, B) := (tuple \for_each(key k) least_supertype(type_a_k, type_b_k))
    ///  For two Lists:
    ///      least_supertype(A, B) := (list max_len: max(max_len A, max_len B), entry: least_supertype(entry_a, entry_b))
    ///        if max_len A | max_len B is 0: entry := Non-empty list entry
    ///  For two responses:
    ///      least_supertype(A, B) := (response least_supertype(ok_a, ok_b), least_supertype(err_a, err_b))
    ///        if any entries are NoType, use the other type's entry
    ///  For two options:
    ///      least_supertype(A, B) := (option least_supertype(some_a, some_b))
    ///        if some_a | some_b is NoType, use the other type's entry.
    ///  For buffers:
    ///      least_supertype(A, B) := (buff len: max(len A, len B))
    ///  For ints, uints, principals, bools:
    ///      least_supertype(A, B) := if A != B, error, else A
    ///
    pub fn least_supertype(
        epoch: &StacksEpochId,
        a: &TypeSignature,
        b: &TypeSignature,
    ) -> Result<TypeSignature> {
        match epoch {
            StacksEpochId::Epoch20 | StacksEpochId::Epoch2_05 => Self::least_supertype_v2_0(a, b),
            StacksEpochId::Epoch21
            | StacksEpochId::Epoch22
            | StacksEpochId::Epoch23
            | StacksEpochId::Epoch24
            | StacksEpochId::Epoch25
            | StacksEpochId::Epoch30
            | StacksEpochId::Epoch31 => Self::least_supertype_v2_1(a, b),
            StacksEpochId::Epoch10 => Err(CheckErrors::Expects("epoch 1.0 not supported".into())),
        }
    }

    pub fn least_supertype_v2_0(a: &TypeSignature, b: &TypeSignature) -> Result<TypeSignature> {
        match (a, b) {
            (
                TupleType(TupleTypeSignature { type_map: types_a }),
                TupleType(TupleTypeSignature { type_map: types_b }),
            ) => {
                let mut type_map_out = BTreeMap::new();
                for (name, entry_a) in types_a.iter() {
                    let entry_b = types_b
                        .get(name)
                        .ok_or(CheckErrors::TypeError(a.clone(), b.clone()))?;
                    let entry_out = Self::least_supertype_v2_0(entry_a, entry_b)?;
                    type_map_out.insert(name.clone(), entry_out);
                }
                Ok(TupleTypeSignature::try_from(type_map_out)
                    .map(|x| x.into())
                    .map_err(|_| CheckErrors::SupertypeTooLarge)?)
            }
            (
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_a,
                    entry_type: entry_a,
                })),
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_b,
                    entry_type: entry_b,
                })),
            ) => {
                let entry_type = if *len_a == 0 {
                    *(entry_b.clone())
                } else if *len_b == 0 {
                    *(entry_a.clone())
                } else {
                    Self::least_supertype_v2_0(entry_a, entry_b)?
                };
                let max_len = cmp::max(len_a, len_b);
                Ok(Self::list_of(entry_type, *max_len)
                    .map_err(|_| CheckErrors::SupertypeTooLarge)?)
            }
            (ResponseType(resp_a), ResponseType(resp_b)) => {
                let ok_type =
                    Self::factor_out_no_type(&StacksEpochId::Epoch2_05, &resp_a.0, &resp_b.0)?;
                let err_type =
                    Self::factor_out_no_type(&StacksEpochId::Epoch2_05, &resp_a.1, &resp_b.1)?;
                Ok(Self::new_response(ok_type, err_type)?)
            }
            (OptionalType(some_a), OptionalType(some_b)) => {
                let some_type =
                    Self::factor_out_no_type(&StacksEpochId::Epoch2_05, some_a, some_b)?;
                Ok(Self::new_option(some_type)?)
            }
            (
                SequenceType(SequenceSubtype::BufferType(buff_a)),
                SequenceType(SequenceSubtype::BufferType(buff_b)),
            ) => {
                let buff_len = if u32::from(buff_a) > u32::from(buff_b) {
                    buff_a
                } else {
                    buff_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::BufferType(buff_len)))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::ASCII(str_len),
                )))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::UTF8(str_len),
                )))
            }
            (NoType, x) | (x, NoType) => Ok(x.clone()),
            (x, y) => {
                if x == y {
                    Ok(x.clone())
                } else {
                    Err(CheckErrors::TypeError(a.clone(), b.clone()))
                }
            }
        }
    }

    pub fn least_supertype_v2_1(a: &TypeSignature, b: &TypeSignature) -> Result<TypeSignature> {
        match (a, b) {
            (
                TupleType(TupleTypeSignature { type_map: types_a }),
                TupleType(TupleTypeSignature { type_map: types_b }),
            ) => {
                let mut type_map_out = BTreeMap::new();
                for (name, entry_a) in types_a.iter() {
                    let entry_b = types_b
                        .get(name)
                        .ok_or(CheckErrors::TypeError(a.clone(), b.clone()))?;
                    let entry_out = Self::least_supertype_v2_1(entry_a, entry_b)?;
                    type_map_out.insert(name.clone(), entry_out);
                }
                Ok(TupleTypeSignature::try_from(type_map_out)
                    .map(|x| x.into())
                    .map_err(|_| CheckErrors::SupertypeTooLarge)?)
            }
            (
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_a,
                    entry_type: entry_a,
                })),
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_b,
                    entry_type: entry_b,
                })),
            ) => {
                let entry_type = if *len_a == 0 {
                    *(entry_b.clone())
                } else if *len_b == 0 {
                    *(entry_a.clone())
                } else {
                    Self::least_supertype_v2_1(entry_a, entry_b)?
                };
                let max_len = cmp::max(len_a, len_b);
                Ok(Self::list_of(entry_type, *max_len)
                    .map_err(|_| CheckErrors::SupertypeTooLarge)?)
            }
            (ResponseType(resp_a), ResponseType(resp_b)) => {
                let ok_type =
                    Self::factor_out_no_type(&StacksEpochId::Epoch21, &resp_a.0, &resp_b.0)?;
                let err_type =
                    Self::factor_out_no_type(&StacksEpochId::Epoch21, &resp_a.1, &resp_b.1)?;
                Ok(Self::new_response(ok_type, err_type)?)
            }
            (OptionalType(some_a), OptionalType(some_b)) => {
                let some_type = Self::factor_out_no_type(&StacksEpochId::Epoch21, some_a, some_b)?;
                Ok(Self::new_option(some_type)?)
            }
            (
                SequenceType(SequenceSubtype::BufferType(buff_a)),
                SequenceType(SequenceSubtype::BufferType(buff_b)),
            ) => {
                let buff_len = if u32::from(buff_a) > u32::from(buff_b) {
                    buff_a
                } else {
                    buff_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::BufferType(buff_len)))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::ASCII(str_len),
                )))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::UTF8(str_len),
                )))
            }
            (NoType, x) | (x, NoType) => Ok(x.clone()),
            (CallableType(x), CallableType(y)) => {
                if x == y {
                    Ok(a.clone())
                } else {
                    Ok(ListUnionType(HashSet::from([x.clone(), y.clone()])))
                }
            }
            (ListUnionType(l), CallableType(c)) | (CallableType(c), ListUnionType(l)) => {
                let mut l1 = l.clone();
                l1.insert(c.clone());
                Ok(ListUnionType(l1))
            }
            (PrincipalType, CallableType(CallableSubtype::Principal(_)))
            | (CallableType(CallableSubtype::Principal(_)), PrincipalType) => Ok(PrincipalType),
            (PrincipalType, ListUnionType(l)) | (ListUnionType(l), PrincipalType) => {
                let mut all_principals = true;
                for ty in l {
                    match ty {
                        CallableSubtype::Trait(_) => {
                            all_principals = false;
                        }
                        CallableSubtype::Principal(_) => (),
                    }
                }
                if all_principals {
                    Ok(PrincipalType)
                } else {
                    Err(CheckErrors::TypeError(a.clone(), b.clone()))
                }
            }
            (ListUnionType(l1), ListUnionType(l2)) => {
                Ok(ListUnionType(l1.union(l2).cloned().collect()))
            }
            (x, y) => {
                if x == y {
                    Ok(x.clone())
                } else {
                    Err(CheckErrors::TypeError(a.clone(), b.clone()))
                }
            }
        }
    }

    pub fn list_of(item_type: TypeSignature, max_len: u32) -> Result<TypeSignature> {
        ListTypeData::new_list(item_type, max_len).map(|x| x.into())
    }

    pub fn empty_list() -> ListTypeData {
        ListTypeData {
            entry_type: Box::new(TypeSignature::NoType),
            max_len: 0,
        }
    }

    pub fn type_of(x: &Value) -> Result<TypeSignature> {
        let out = match x {
            Value::Principal(_) => PrincipalType,
            Value::Int(_v) => IntType,
            Value::UInt(_v) => UIntType,
            Value::Bool(_v) => BoolType,
            Value::Tuple(v) => TupleType(v.type_signature.clone()),
            Value::Sequence(SequenceData::List(list_data)) => list_data.type_signature()?,
            Value::Sequence(SequenceData::Buffer(buff_data)) => buff_data.type_signature()?,
            Value::Sequence(SequenceData::String(CharType::ASCII(ascii_data))) => {
                ascii_data.type_signature()?
            }
            Value::Sequence(SequenceData::String(CharType::UTF8(utf8_data))) => {
                utf8_data.type_signature()?
            }
            Value::Optional(v) => v.type_signature()?,
            Value::Response(v) => v.type_signature()?,
            Value::CallableContract(v) => {
                if let Some(trait_identifier) = &v.trait_identifier {
                    CallableType(CallableSubtype::Trait(trait_identifier.clone()))
                } else {
                    CallableType(CallableSubtype::Principal(v.contract_identifier.clone()))
                }
            }
        };

        Ok(out)
    }

    pub fn literal_type_of(x: &Value) -> Result<TypeSignature> {
        match x {
            Value::Principal(PrincipalData::Contract(contract_id)) => Ok(CallableType(
                CallableSubtype::Principal(contract_id.clone()),
            )),
            _ => Self::type_of(x),
        }
    }

    // Checks if resulting type signature is of valid size.
    pub fn construct_parent_list_type(args: &[Value]) -> Result<ListTypeData> {
        let children_types: Result<Vec<_>> = args.iter().map(TypeSignature::type_of).collect();
        TypeSignature::parent_list_type(&children_types?)
    }

    pub fn parent_list_type(
        children: &[TypeSignature],
    ) -> std::result::Result<ListTypeData, CheckErrors> {
        if let Some((first, rest)) = children.split_first() {
            let mut current_entry_type = first.clone();
            for next_entry in rest.iter() {
                current_entry_type = Self::least_supertype_v2_1(&current_entry_type, next_entry)?;
            }
            let len = u32::try_from(children.len()).map_err(|_| CheckErrors::ValueTooLarge)?;
            ListTypeData::new_list(current_entry_type, len)
        } else {
            Ok(TypeSignature::empty_list())
        }
    }
}

/// Parsing functions.
impl TypeSignature {
    fn parse_atom_type(typename: &str) -> Result<TypeSignature> {
        match typename {
            "int" => Ok(TypeSignature::IntType),
            "uint" => Ok(TypeSignature::UIntType),
            "bool" => Ok(TypeSignature::BoolType),
            "principal" => Ok(TypeSignature::PrincipalType),
            _ => Err(CheckErrors::UnknownTypeName(typename.into())),
        }
    }

    // Parses list type signatures ->
    // (list maximum-length atomic-type)
    fn parse_list_type_repr<A: CostTracker>(
        epoch: StacksEpochId,
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 2 {
            return Err(CheckErrors::InvalidTypeDescription);
        }

        if let SymbolicExpressionType::LiteralValue(Value::Int(max_len)) = &type_args[0].expr {
            let atomic_type_arg = &type_args[type_args.len() - 1];
            let entry_type = TypeSignature::parse_type_repr(epoch, atomic_type_arg, accounting)?;
            let max_len = u32::try_from(*max_len).map_err(|_| CheckErrors::ValueTooLarge)?;
            ListTypeData::new_list(entry_type, max_len).map(|x| x.into())
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the following form:
    // (tuple (key-name-0 value-type-0) (key-name-1 value-type-1))
    fn parse_tuple_type_repr<A: CostTracker>(
        epoch: StacksEpochId,
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        let mapped_key_types = parse_name_type_pairs(epoch, type_args, accounting)?;
        let tuple_type_signature = TupleTypeSignature::try_from(mapped_key_types)?;
        Ok(TypeSignature::from(tuple_type_signature))
    }

    // Parses type signatures of the form:
    // (buff 10)
    fn parse_buff_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(buff_len)) = &type_args[0].expr {
            BufferLength::try_from(*buff_len)
                .map(|buff_len| SequenceType(SequenceSubtype::BufferType(buff_len)))
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the form:
    // (string-utf8 10)
    fn parse_string_utf8_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(utf8_len)) = &type_args[0].expr {
            StringUTF8Length::try_from(*utf8_len).map(|utf8_len| {
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(utf8_len)))
            })
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the form:
    // (string-ascii 10)
    fn parse_string_ascii_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(buff_len)) = &type_args[0].expr {
            BufferLength::try_from(*buff_len).map(|buff_len| {
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(buff_len)))
            })
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    fn parse_optional_type_repr<A: CostTracker>(
        epoch: StacksEpochId,
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        let inner_type = TypeSignature::parse_type_repr(epoch, &type_args[0], accounting)?;

        TypeSignature::new_option(inner_type)
    }

    pub fn parse_response_type_repr<A: CostTracker>(
        epoch: StacksEpochId,
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 2 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        let ok_type = TypeSignature::parse_type_repr(epoch, &type_args[0], accounting)?;
        let err_type = TypeSignature::parse_type_repr(epoch, &type_args[1], accounting)?;
        TypeSignature::new_response(ok_type, err_type)
    }

    pub fn parse_type_repr<A: CostTracker>(
        epoch: StacksEpochId,
        x: &SymbolicExpression,
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        runtime_cost(ClarityCostFunction::TypeParseStep, accounting, 0)?;

        match x.expr {
            SymbolicExpressionType::Atom(ref atom_type_str) => {
                let atomic_type = TypeSignature::parse_atom_type(atom_type_str)?;
                Ok(atomic_type)
            }
            SymbolicExpressionType::List(ref list_contents) => {
                let (compound_type, rest) = list_contents
                    .split_first()
                    .ok_or(CheckErrors::InvalidTypeDescription)?;
                if let SymbolicExpressionType::Atom(ref compound_type) = compound_type.expr {
                    match compound_type.as_ref() {
                        "list" => TypeSignature::parse_list_type_repr(epoch, rest, accounting),
                        "buff" => TypeSignature::parse_buff_type_repr(rest),
                        "string-utf8" => TypeSignature::parse_string_utf8_type_repr(rest),
                        "string-ascii" => TypeSignature::parse_string_ascii_type_repr(rest),
                        "tuple" => TypeSignature::parse_tuple_type_repr(epoch, rest, accounting),
                        "optional" => {
                            TypeSignature::parse_optional_type_repr(epoch, rest, accounting)
                        }
                        "response" => {
                            TypeSignature::parse_response_type_repr(epoch, rest, accounting)
                        }
                        _ => Err(CheckErrors::InvalidTypeDescription),
                    }
                } else {
                    Err(CheckErrors::InvalidTypeDescription)
                }
            }
            SymbolicExpressionType::TraitReference(_, ref trait_definition)
                if epoch < StacksEpochId::Epoch21 =>
            {
                match trait_definition {
                    TraitDefinition::Defined(trait_id) => {
                        Ok(TypeSignature::TraitReferenceType(trait_id.clone()))
                    }
                    TraitDefinition::Imported(trait_id) => {
                        Ok(TypeSignature::TraitReferenceType(trait_id.clone()))
                    }
                }
            }
            SymbolicExpressionType::TraitReference(_, ref trait_definition) => {
                match trait_definition {
                    TraitDefinition::Defined(trait_id) => Ok(TypeSignature::CallableType(
                        CallableSubtype::Trait(trait_id.clone()),
                    )),
                    TraitDefinition::Imported(trait_id) => Ok(TypeSignature::CallableType(
                        CallableSubtype::Trait(trait_id.clone()),
                    )),
                }
            }
            _ => Err(CheckErrors::InvalidTypeDescription),
        }
    }

    pub fn parse_trait_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
        epoch: StacksEpochId,
        clarity_version: ClarityVersion,
    ) -> Result<BTreeMap<ClarityName, FunctionSignature>> {
        let mut trait_signature: BTreeMap<ClarityName, FunctionSignature> = BTreeMap::new();
        let functions_types = type_args
            .first()
            .ok_or_else(|| CheckErrors::InvalidTypeDescription)?
            .match_list()
            .ok_or(CheckErrors::DefineTraitBadSignature)?;

        for function_type in functions_types.iter() {
            let args = function_type
                .match_list()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;
            if args.len() != 3 {
                return Err(CheckErrors::InvalidTypeDescription);
            }

            // Extract function's name
            let fn_name = args[0]
                .match_atom()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;

            // Extract function's arguments
            let fn_args_exprs = args[1]
                .match_list()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;
            let fn_args = fn_args_exprs
                .iter()
                .map(|arg_type| TypeSignature::parse_type_repr(epoch, arg_type, accounting))
                .collect::<Result<_>>()?;

            // Extract function's type return - must be a response
            let fn_return = match TypeSignature::parse_type_repr(epoch, &args[2], accounting) {
                Ok(response) => match response {
                    TypeSignature::ResponseType(_) => Ok(response),
                    _ => Err(CheckErrors::DefineTraitBadSignature),
                },
                _ => Err(CheckErrors::DefineTraitBadSignature),
            }?;

            if trait_signature
                .insert(
                    fn_name.clone(),
                    FunctionSignature {
                        args: fn_args,
                        returns: fn_return,
                    },
                )
                .is_some()
                && clarity_version >= ClarityVersion::Clarity2
            {
                return Err(CheckErrors::DefineTraitDuplicateMethod(fn_name.to_string()));
            }
        }
        Ok(trait_signature)
    }

    #[cfg(test)]
    pub fn from_string(val: &str, version: ClarityVersion, epoch: StacksEpochId) -> Self {
        use crate::vm::ast::parse;
        let expr = &parse(
            &QualifiedContractIdentifier::transient(),
            val,
            version,
            epoch,
        )
        .unwrap()[0];
        TypeSignature::parse_type_repr(epoch, expr, &mut ()).unwrap()
    }
}

/// These implement the size calculations in TypeSignatures
///    in constructors of TypeSignatures, only `.inner_size()` may be called.
///    .inner_size is a failable method to compute the size of the type signature,
///    Failures indicate that a type signature represents _too large_ of a value.
/// TypeSignature constructors will fail instead of constructing such a type.
///   because of this, the public interface to size is infallible.
impl TypeSignature {
    pub fn depth(&self) -> u8 {
        // unlike inner_size, depth will never threaten to overflow,
        //  because a new type can only increase depth by 1.
        match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            CallableType(_)
            | TraitReferenceType(_)
            | ListUnionType(_)
            | NoType
            | IntType
            | UIntType
            | BoolType
            | PrincipalType
            | SequenceType(SequenceSubtype::BufferType(_))
            | SequenceType(SequenceSubtype::StringType(_)) => 1,
            TupleType(tuple_sig) => 1 + tuple_sig.max_depth(),
            SequenceType(SequenceSubtype::ListType(list_type)) => {
                1 + list_type.get_list_item_type().depth()
            }
            OptionalType(t) => 1 + t.depth(),
            ResponseType(v) => 1 + cmp::max(v.0.depth(), v.1.depth()),
        }
    }

    pub fn size(&self) -> Result<u32> {
        self.inner_size()?.ok_or_else(|| {
            CheckErrors::Expects(
                "FAIL: .size() overflowed on too large of a type. construction should have failed!"
                    .into(),
            )
        })
    }

    fn inner_size(&self) -> Result<Option<u32>> {
        let out = match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            NoType => Some(1),
            IntType => Some(16),
            UIntType => Some(16),
            BoolType => Some(1),
            PrincipalType => Some(148), // 20+128
            TupleType(tuple_sig) => tuple_sig.inner_size()?,
            SequenceType(SequenceSubtype::BufferType(len))
            | SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                Some(4 + u32::from(len))
            }
            SequenceType(SequenceSubtype::ListType(list_type)) => list_type.inner_size()?,
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                Some(4 + 4 * u32::from(len))
            }
            OptionalType(t) => t.size()?.checked_add(WRAPPER_VALUE_SIZE),
            ResponseType(v) => {
                // ResponseTypes are 1 byte for the committed bool,
                //   plus max(err_type, ok_type)
                let (t, s) = (&v.0, &v.1);
                let t_size = t.size()?;
                let s_size = s.size()?;
                cmp::max(t_size, s_size).checked_add(WRAPPER_VALUE_SIZE)
            }
            CallableType(CallableSubtype::Principal(_)) | ListUnionType(_) => Some(148), // 20+128
            CallableType(CallableSubtype::Trait(_)) | TraitReferenceType(_) => Some(276), // 20+128+128
        };
        Ok(out)
    }

    pub fn type_size(&self) -> Result<u32> {
        self.inner_type_size()
            .ok_or_else(|| CheckErrors::ValueTooLarge)
    }

    /// Returns the size of the _type signature_
    fn inner_type_size(&self) -> Option<u32> {
        match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            // These types all only use ~1 byte for their type enum
            NoType | IntType | UIntType | BoolType | PrincipalType => Some(1),
            // u32 length + type enum
            TupleType(tuple_sig) => tuple_sig.type_size(),
            SequenceType(SequenceSubtype::BufferType(_)) => Some(1 + 4),
            SequenceType(SequenceSubtype::ListType(list_type)) => list_type.type_size(),
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => Some(1 + 4),
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => Some(1 + 4),
            OptionalType(t) => t.inner_type_size()?.checked_add(1),
            ResponseType(v) => {
                let (t, s) = (&v.0, &v.1);
                t.inner_type_size()?
                    .checked_add(s.inner_type_size()?)?
                    .checked_add(1)
            }
            CallableType(_) | TraitReferenceType(_) | ListUnionType(_) => Some(1),
        }
    }
}

impl ListTypeData {
    /// List Size: type_signature_size + max_len * entry_type.size()
    fn inner_size(&self) -> Result<Option<u32>> {
        let total_size = self
            .entry_type
            .size()?
            .checked_mul(self.max_len)
            .and_then(|x| x.checked_add(self.type_size()?));
        match total_size {
            Some(total_size) => {
                if total_size > MAX_VALUE_SIZE {
                    Ok(None)
                } else {
                    Ok(Some(total_size))
                }
            }
            None => Ok(None),
        }
    }

    fn type_size(&self) -> Option<u32> {
        let total_size = self.entry_type.inner_type_size()?.checked_add(4 + 1)?; // 1 byte for Type enum, 4 for max_len.
        if total_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(total_size)
        }
    }
}

impl TupleTypeSignature {
    /// Tuple Size:
    ///    size( btreemap<name, type> ) = 2*map.len() + sum(names) + sum(values)
    pub fn type_size(&self) -> Option<u32> {
        let mut type_map_size = u32::try_from(self.type_map.len()).ok()?.checked_mul(2)?;

        for (name, type_signature) in self.type_map.iter() {
            // we only accept ascii names, so 1 char = 1 byte.
            type_map_size = type_map_size
                .checked_add(type_signature.inner_type_size()?)?
                // name.len() is bound to MAX_STRING_LEN (128), so `as u32` won't ever truncate
                .checked_add(name.len() as u32)?;
        }

        if type_map_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(type_map_size)
        }
    }

    pub fn size(&self) -> Result<u32> {
        self.inner_size()?
            .ok_or_else(|| CheckErrors::Expects("size() overflowed on a constructed type.".into()))
    }

    fn max_depth(&self) -> u8 {
        let mut max = 0;
        for (_name, type_signature) in self.type_map.iter() {
            max = cmp::max(max, type_signature.depth())
        }
        max
    }

    /// Tuple Size:
    ///    size( btreemap<name, value> ) + type_size
    ///    size( btreemap<name, value> ) = 2*map.len() + sum(names) + sum(values)
    fn inner_size(&self) -> Result<Option<u32>> {
        let Some(mut total_size) = u32::try_from(self.type_map.len())
            .ok()
            .and_then(|x| x.checked_mul(2))
            .and_then(|x| x.checked_add(self.type_size()?))
        else {
            return Ok(None);
        };

        for (name, type_signature) in self.type_map.iter() {
            // we only accept ascii names, so 1 char = 1 byte.
            total_size = if let Some(new_size) = total_size.checked_add(type_signature.size()?) {
                new_size
            } else {
                return Ok(None);
            };
            total_size = if let Some(new_size) = total_size.checked_add(name.len() as u32) {
                new_size
            } else {
                return Ok(None);
            };
        }

        if total_size > MAX_VALUE_SIZE {
            Ok(None)
        } else {
            Ok(Some(total_size))
        }
    }
}

use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::costs::CostTracker;
use crate::vm::ClarityVersion;

pub fn parse_name_type_pairs<A: CostTracker>(
    epoch: StacksEpochId,
    name_type_pairs: &[SymbolicExpression],
    accounting: &mut A,
) -> Result<Vec<(ClarityName, TypeSignature)>> {
    // this is a pretty deep nesting here, but what we're trying to do is pick out the values of
    // the form:
    // ((name1 type1) (name2 type2) (name3 type3) ...)
    // which is a list of 2-length lists of atoms.
    use crate::vm::representations::SymbolicExpressionType::{Atom, List};

    // step 1: parse it into a vec of symbolicexpression pairs.
    let as_pairs: Result<Vec<_>> = name_type_pairs
        .iter()
        .map(|key_type_pair| {
            if let List(ref as_vec) = key_type_pair.expr {
                if as_vec.len() != 2 {
                    Err(CheckErrors::BadSyntaxExpectedListOfPairs)
                } else {
                    Ok((&as_vec[0], &as_vec[1]))
                }
            } else {
                Err(CheckErrors::BadSyntaxExpectedListOfPairs)
            }
        })
        .collect();

    // step 2: turn into a vec of (name, typesignature) pairs.
    let key_types: Result<Vec<_>> = (as_pairs?)
        .iter()
        .map(|(name_symbol, type_symbol)| {
            let name = name_symbol
                .match_atom()
                .ok_or(CheckErrors::BadSyntaxExpectedListOfPairs)?
                .clone();
            let type_info = TypeSignature::parse_type_repr(epoch, type_symbol, accounting)?;
            Ok((name, type_info))
        })
        .collect();

    key_types
}

impl fmt::Display for TupleTypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(tuple")?;
        let mut type_strs: Vec<_> = self.type_map.iter().collect();
        type_strs.sort_unstable_by_key(|x| x.0);
        for (field_name, field_type) in type_strs {
            write!(f, " ({} {})", &**field_name, field_type)?;
        }
        write!(f, ")")
    }
}

impl fmt::Debug for TupleTypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TupleTypeSignature {{")?;
        for (field_name, field_type) in self.type_map.iter() {
            write!(f, " \"{}\": {},", &**field_name, field_type)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for AssetIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}::{}",
            &*self.contract_identifier.to_string(),
            &*self.asset_name
        )
    }
}

impl fmt::Display for TypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NoType => write!(f, "UnknownType"),
            IntType => write!(f, "int"),
            UIntType => write!(f, "uint"),
            BoolType => write!(f, "bool"),
            OptionalType(t) => write!(f, "(optional {})", t),
            ResponseType(v) => write!(f, "(response {} {})", v.0, v.1),
            TupleType(t) => write!(f, "{}", t),
            PrincipalType => write!(f, "principal"),
            SequenceType(SequenceSubtype::BufferType(len)) => write!(f, "(buff {})", len),
            SequenceType(SequenceSubtype::ListType(list_type_data)) => write!(
                f,
                "(list {} {})",
                list_type_data.max_len, list_type_data.entry_type
            ),
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                write!(f, "(string-ascii {})", len)
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                write!(f, "(string-utf8 {})", len)
            }
            CallableType(CallableSubtype::Trait(trait_id)) | TraitReferenceType(trait_id) => {
                write!(f, "<{}>", trait_id)
            }
            CallableType(CallableSubtype::Principal(contract_id)) => {
                write!(f, "(principal {})", contract_id)
            }
            ListUnionType(_) => write!(f, "principal"),
        }
    }
}

impl fmt::Display for BufferLength {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for StringUTF8Length {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for FunctionArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.signature)
    }
}

#[cfg(test)]
mod test {
    #[cfg(test)]
    use rstest::rstest;
    #[cfg(test)]
    use rstest_reuse::{self, *};
    use stacks_common::types::StacksEpochId;

    use super::CheckErrors::*;
    use super::*;
    use crate::vm::tests::test_clarity_versions;
    use crate::vm::{execute, ClarityVersion};

    fn fail_parse(val: &str, version: ClarityVersion, epoch: StacksEpochId) -> CheckErrors {
        use crate::vm::ast::parse;
        let expr = &parse(
            &QualifiedContractIdentifier::transient(),
            val,
            version,
            epoch,
        )
        .unwrap()[0];
        TypeSignature::parse_type_repr(epoch, expr, &mut ()).unwrap_err()
    }

    #[apply(test_clarity_versions)]
    fn type_of_list_of_buffs(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {
        let value = execute("(list \"abc\" \"abcde\")").unwrap().unwrap();
        let type_descr = TypeSignature::from_string("(list 2 (string-ascii 5))", version, epoch);
        assert_eq!(TypeSignature::type_of(&value).unwrap(), type_descr);
    }

    #[apply(test_clarity_versions)]
    fn type_signature_way_too_big(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {
        // first_tuple.type_size ~= 131
        // second_tuple.type_size = k * (130+130)
        // to get a type-size greater than max_value all by itself,
        //   set k = 4033
        let first_tuple = TypeSignature::from_string("(tuple (a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 bool))", version, epoch);

        let len = 4033;
        let mut keys = Vec::with_capacity(len);
        for i in 0..len {
            let key_name = ClarityName::try_from(format!("a{:0127}", i)).unwrap();
            let key_val = first_tuple.clone();
            keys.push((key_name, key_val));
        }

        assert_eq!(
            TupleTypeSignature::try_from(keys).unwrap_err(),
            ValueTooLarge
        );
    }

    #[apply(test_clarity_versions)]
    fn test_construction(#[case] version: ClarityVersion, #[case] epoch: StacksEpochId) {
        let bad_type_descriptions = [
            ("(tuple)", EmptyTuplesNotAllowed),
            ("(list int int)", InvalidTypeDescription),
            ("(list 4294967296 int)", ValueTooLarge),
            ("(list 50 bazel)", UnknownTypeName("bazel".into())),
            ("(buff)", InvalidTypeDescription),
            ("(buff 4294967296)", ValueTooLarge),
            ("(buff int)", InvalidTypeDescription),
            ("(response int)", InvalidTypeDescription),
            ("(optional bazel)", UnknownTypeName("bazel".into())),
            ("(response bazel int)", UnknownTypeName("bazel".into())),
            ("(response int bazel)", UnknownTypeName("bazel".into())),
            ("bazel", UnknownTypeName("bazel".into())),
            ("()", InvalidTypeDescription),
            ("(1234)", InvalidTypeDescription),
            ("(int 3 int)", InvalidTypeDescription),
            ("1234", InvalidTypeDescription),
            ("(list 1 (buff 1048576))", ValueTooLarge),
            ("(list 4294967295 (buff 2))", ValueTooLarge),
            ("(list 2147483647 (buff 2))", ValueTooLarge),
            ("(tuple (l (buff 1048576)))", ValueTooLarge),
        ];

        for (desc, expected) in bad_type_descriptions.iter() {
            assert_eq!(&fail_parse(desc, version, epoch), expected);
        }

        let okay_types = [
            "(list 16 uint)",
            "(list 15 (response int bool))",
            "(list 15 (response bool int))",
            "(buff 1048576)",
            "(list 4400 bool)",
            "(tuple (l (buff 1048550)))",
        ];

        for desc in okay_types.iter() {
            let _ = TypeSignature::from_string(desc, version, epoch); // panics on failed types.
        }
    }

    #[test]
    fn test_least_supertype() {
        let callables = [
            CallableSubtype::Principal(QualifiedContractIdentifier::local("foo").unwrap()),
            CallableSubtype::Trait(TraitIdentifier {
                name: "foo".into(),
                contract_identifier: QualifiedContractIdentifier::transient(),
            }),
        ];
        let list_union = ListUnionType(callables.clone().into());
        let callables2 = [
            CallableSubtype::Principal(QualifiedContractIdentifier::local("bar").unwrap()),
            CallableSubtype::Trait(TraitIdentifier {
                name: "bar".into(),
                contract_identifier: QualifiedContractIdentifier::transient(),
            }),
        ];
        let list_union2 = ListUnionType(callables2.clone().into());
        let list_union_merged = ListUnionType(HashSet::from_iter(
            [callables, callables2].concat().iter().cloned(),
        ));
        let callable_principals = [
            CallableSubtype::Principal(QualifiedContractIdentifier::local("foo").unwrap()),
            CallableSubtype::Principal(QualifiedContractIdentifier::local("bar").unwrap()),
        ];
        let list_union_principals = ListUnionType(callable_principals.into());

        let notype_pairs = [
            // NoType with X should result in X
            (
                (TypeSignature::NoType, TypeSignature::NoType),
                TypeSignature::NoType,
            ),
            (
                (TypeSignature::NoType, TypeSignature::IntType),
                TypeSignature::IntType,
            ),
            (
                (TypeSignature::NoType, TypeSignature::UIntType),
                TypeSignature::UIntType,
            ),
            (
                (TypeSignature::NoType, TypeSignature::BoolType),
                TypeSignature::BoolType,
            ),
            (
                (TypeSignature::NoType, TypeSignature::min_buffer().unwrap()),
                TypeSignature::min_buffer().unwrap(),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
                ),
                TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::bound_string_ascii_type(17).unwrap(),
                ),
                TypeSignature::bound_string_ascii_type(17).unwrap(),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::max_string_utf8().unwrap(),
                ),
                TypeSignature::max_string_utf8().unwrap(),
            ),
            (
                (TypeSignature::NoType, TypeSignature::PrincipalType),
                TypeSignature::PrincipalType,
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::TupleType(
                        TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                            .unwrap(),
                    ),
                ),
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                        .unwrap(),
                ),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::new_option(TypeSignature::IntType).unwrap(),
                ),
                TypeSignature::new_option(TypeSignature::IntType).unwrap(),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                        .unwrap(),
                ),
                TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                    .unwrap(),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::transient(),
                    )),
                ),
                TypeSignature::CallableType(CallableSubtype::Principal(
                    QualifiedContractIdentifier::transient(),
                )),
            ),
            (
                (
                    TypeSignature::NoType,
                    TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                        name: "foo".into(),
                        contract_identifier: QualifiedContractIdentifier::transient(),
                    })),
                ),
                TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                    name: "foo".into(),
                    contract_identifier: QualifiedContractIdentifier::transient(),
                })),
            ),
            (
                (TypeSignature::NoType, list_union.clone()),
                list_union.clone(),
            ),
        ];

        for (pair, expected) in notype_pairs {
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.0, &pair.1).unwrap(),
                expected
            );
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.1, &pair.0).unwrap(),
                expected
            );
        }

        let simple_pairs = [
            ((IntType, IntType), IntType),
            ((UIntType, UIntType), UIntType),
            ((BoolType, BoolType), BoolType),
            (
                (
                    TypeSignature::max_buffer().unwrap(),
                    TypeSignature::max_buffer().unwrap(),
                ),
                TypeSignature::max_buffer().unwrap(),
            ),
            (
                (
                    TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
                    TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
                ),
                TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
            ),
            (
                (
                    TypeSignature::bound_string_ascii_type(17).unwrap(),
                    TypeSignature::bound_string_ascii_type(17).unwrap(),
                ),
                TypeSignature::bound_string_ascii_type(17).unwrap(),
            ),
            (
                (
                    TypeSignature::max_string_utf8().unwrap(),
                    TypeSignature::max_string_utf8().unwrap(),
                ),
                TypeSignature::max_string_utf8().unwrap(),
            ),
            (
                (TypeSignature::PrincipalType, TypeSignature::PrincipalType),
                TypeSignature::PrincipalType,
            ),
            (
                (
                    TypeSignature::TupleType(
                        TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                            .unwrap(),
                    ),
                    TypeSignature::TupleType(
                        TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                            .unwrap(),
                    ),
                ),
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                        .unwrap(),
                ),
            ),
            (
                (
                    TypeSignature::new_option(TypeSignature::IntType).unwrap(),
                    TypeSignature::new_option(TypeSignature::IntType).unwrap(),
                ),
                TypeSignature::new_option(TypeSignature::IntType).unwrap(),
            ),
            (
                (
                    TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                        .unwrap(),
                    TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                        .unwrap(),
                ),
                TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                    .unwrap(),
            ),
            (
                (
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::transient(),
                    )),
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::transient(),
                    )),
                ),
                TypeSignature::CallableType(CallableSubtype::Principal(
                    QualifiedContractIdentifier::transient(),
                )),
            ),
            (
                (
                    TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                        name: "foo".into(),
                        contract_identifier: QualifiedContractIdentifier::transient(),
                    })),
                    TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                        name: "foo".into(),
                        contract_identifier: QualifiedContractIdentifier::transient(),
                    })),
                ),
                TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                    name: "foo".into(),
                    contract_identifier: QualifiedContractIdentifier::transient(),
                })),
            ),
            ((list_union.clone(), list_union.clone()), list_union.clone()),
        ];

        for (pair, expected) in simple_pairs {
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.0, &pair.1).unwrap(),
                expected
            );
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.1, &pair.0).unwrap(),
                expected
            );
        }

        let matched_pairs = [
            (
                (
                    TypeSignature::max_buffer().unwrap(),
                    TypeSignature::min_buffer().unwrap(),
                ),
                TypeSignature::max_buffer().unwrap(),
            ),
            (
                (
                    TypeSignature::list_of(TypeSignature::IntType, 17).unwrap(),
                    TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
                ),
                TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
            ),
            (
                (
                    TypeSignature::min_string_ascii().unwrap(),
                    TypeSignature::bound_string_ascii_type(17).unwrap(),
                ),
                TypeSignature::bound_string_ascii_type(17).unwrap(),
            ),
            (
                (
                    TypeSignature::min_string_utf8().unwrap(),
                    TypeSignature::max_string_utf8().unwrap(),
                ),
                TypeSignature::max_string_utf8().unwrap(),
            ),
            (
                (
                    TypeSignature::PrincipalType,
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::transient(),
                    )),
                ),
                TypeSignature::PrincipalType,
            ),
            (
                (TypeSignature::PrincipalType, list_union_principals.clone()),
                TypeSignature::PrincipalType,
            ),
            (
                (
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::local("foo").unwrap(),
                    )),
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::local("bar").unwrap(),
                    )),
                ),
                list_union_principals.clone(),
            ),
            (
                (list_union.clone(), list_union2.clone()),
                list_union_merged.clone(),
            ),
        ];

        for (pair, expected) in matched_pairs {
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.0, &pair.1).unwrap(),
                expected
            );
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.1, &pair.0).unwrap(),
                expected
            );
        }

        let compound_pairs = [
            (
                (
                    TypeSignature::list_of(
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            16_u32.try_into().unwrap(),
                        )),
                        5,
                    )
                    .unwrap(),
                    TypeSignature::list_of(TypeSignature::min_buffer().unwrap(), 3).unwrap(),
                ),
                TypeSignature::list_of(
                    TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        16_u32.try_into().unwrap(),
                    )),
                    5,
                )
                .unwrap(),
            ),
            (
                (
                    TypeSignature::TupleType(
                        TupleTypeSignature::try_from(vec![(
                            "b".into(),
                            TypeSignature::min_string_ascii().unwrap(),
                        )])
                        .unwrap(),
                    ),
                    TypeSignature::TupleType(
                        TupleTypeSignature::try_from(vec![(
                            "b".into(),
                            TypeSignature::bound_string_ascii_type(17).unwrap(),
                        )])
                        .unwrap(),
                    ),
                ),
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![(
                        "b".into(),
                        TypeSignature::bound_string_ascii_type(17).unwrap(),
                    )])
                    .unwrap(),
                ),
            ),
            (
                (
                    TypeSignature::new_option(TypeSignature::min_string_ascii().unwrap()).unwrap(),
                    TypeSignature::new_option(TypeSignature::bound_string_ascii_type(17).unwrap())
                        .unwrap(),
                ),
                TypeSignature::new_option(TypeSignature::bound_string_ascii_type(17).unwrap())
                    .unwrap(),
            ),
            (
                (
                    TypeSignature::new_response(TypeSignature::PrincipalType, list_union.clone())
                        .unwrap(),
                    TypeSignature::new_response(
                        TypeSignature::CallableType(CallableSubtype::Principal(
                            QualifiedContractIdentifier::transient(),
                        )),
                        list_union2.clone(),
                    )
                    .unwrap(),
                ),
                TypeSignature::new_response(TypeSignature::PrincipalType, list_union_merged)
                    .unwrap(),
            ),
        ];

        for (pair, expected) in compound_pairs {
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.0, &pair.1).unwrap(),
                expected
            );
            assert_eq!(
                TypeSignature::least_supertype_v2_1(&pair.1, &pair.0).unwrap(),
                expected
            );
        }

        let bad_pairs = [
            (IntType, UIntType),
            (BoolType, IntType),
            (
                TypeSignature::max_buffer().unwrap(),
                TypeSignature::max_string_ascii().unwrap(),
            ),
            (
                TypeSignature::list_of(TypeSignature::UIntType, 42).unwrap(),
                TypeSignature::list_of(TypeSignature::IntType, 42).unwrap(),
            ),
            (
                TypeSignature::min_string_utf8().unwrap(),
                TypeSignature::bound_string_ascii_type(17).unwrap(),
            ),
            (
                TypeSignature::min_string_utf8().unwrap(),
                TypeSignature::min_buffer().unwrap(),
            ),
            (
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::IntType)])
                        .unwrap(),
                ),
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![("a".into(), TypeSignature::UIntType)])
                        .unwrap(),
                ),
            ),
            (
                TypeSignature::new_option(TypeSignature::IntType).unwrap(),
                TypeSignature::new_option(TypeSignature::min_string_utf8().unwrap()).unwrap(),
            ),
            (
                TypeSignature::new_response(TypeSignature::IntType, TypeSignature::BoolType)
                    .unwrap(),
                TypeSignature::new_response(TypeSignature::BoolType, TypeSignature::IntType)
                    .unwrap(),
            ),
            (
                TypeSignature::CallableType(CallableSubtype::Principal(
                    QualifiedContractIdentifier::transient(),
                )),
                TypeSignature::IntType,
            ),
            (
                TypeSignature::CallableType(CallableSubtype::Trait(TraitIdentifier {
                    name: "foo".into(),
                    contract_identifier: QualifiedContractIdentifier::transient(),
                })),
                TypeSignature::PrincipalType,
            ),
            (list_union.clone(), TypeSignature::PrincipalType),
            (
                TypeSignature::min_string_ascii().unwrap(),
                list_union_principals,
            ),
            (
                TypeSignature::list_of(
                    TypeSignature::SequenceType(SequenceSubtype::BufferType(
                        16_u32.try_into().unwrap(),
                    )),
                    5,
                )
                .unwrap(),
                TypeSignature::list_of(TypeSignature::min_string_ascii().unwrap(), 3).unwrap(),
            ),
            (
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![(
                        "b".into(),
                        TypeSignature::min_string_ascii().unwrap(),
                    )])
                    .unwrap(),
                ),
                TypeSignature::TupleType(
                    TupleTypeSignature::try_from(vec![("b".into(), TypeSignature::UIntType)])
                        .unwrap(),
                ),
            ),
            (
                TypeSignature::new_option(TypeSignature::min_string_ascii().unwrap()).unwrap(),
                TypeSignature::new_option(TypeSignature::min_string_utf8().unwrap()).unwrap(),
            ),
            (
                TypeSignature::new_response(TypeSignature::PrincipalType, list_union).unwrap(),
                TypeSignature::new_response(
                    list_union2,
                    TypeSignature::CallableType(CallableSubtype::Principal(
                        QualifiedContractIdentifier::transient(),
                    )),
                )
                .unwrap(),
            ),
        ];

        for pair in bad_pairs {
            matches!(
                TypeSignature::least_supertype_v2_1(&pair.0, &pair.1).unwrap_err(),
                CheckErrors::TypeError(..)
            );
            matches!(
                TypeSignature::least_supertype_v2_1(&pair.1, &pair.0).unwrap_err(),
                CheckErrors::TypeError(..)
            );
        }
    }
}
