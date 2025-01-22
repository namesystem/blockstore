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

pub mod serialization;
pub mod signatures;

use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::{char, cmp, fmt, str};

use hashbrown::hash_map::OccupiedEntry;
use regex::Regex;
use stacks_common::address::c32;
use stacks_common::types::chainstate::StacksAddress;
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash;

use crate::vm::errors::{
    CheckErrors, IncomparableError, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};
use crate::vm::representations::{
    ClarityName, ContractName, SymbolicExpression, SymbolicExpressionType,
};
pub use crate::vm::types::signatures::{
    parse_name_type_pairs, AssetIdentifier, BufferLength, FixedFunction, FunctionArg,
    FunctionSignature, FunctionType, ListTypeData, SequenceSubtype, StringSubtype,
    StringUTF8Length, TupleTypeSignature, TypeSignature, BUFF_1, BUFF_20, BUFF_21, BUFF_32,
    BUFF_33, BUFF_64, BUFF_65,
};
use crate::vm::ClarityVersion;

pub const MAX_VALUE_SIZE: u32 = 1024 * 1024; // 1MB
pub const BOUND_VALUE_SERIALIZATION_BYTES: u32 = MAX_VALUE_SIZE * 2;
pub const BOUND_VALUE_SERIALIZATION_HEX: u32 = BOUND_VALUE_SERIALIZATION_BYTES * 2;

pub const MAX_TYPE_DEPTH: u8 = 32;
// this is the charged size for wrapped values, i.e., response or optionals
pub const WRAPPER_VALUE_SIZE: u32 = 1;

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct TupleData {
    // todo: remove type_signature
    pub type_signature: TupleTypeSignature,
    pub data_map: BTreeMap<ClarityName, Value>,
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuffData {
    pub data: Vec<u8>,
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct ListData {
    pub data: Vec<Value>,
    // todo: remove type_signature
    pub type_signature: ListTypeData,
}

#[derive(Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct StandardPrincipalData(pub u8, pub [u8; 20]);

impl StandardPrincipalData {
    pub fn transient() -> StandardPrincipalData {
        Self(
            1,
            [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        )
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct QualifiedContractIdentifier {
    pub issuer: StandardPrincipalData,
    pub name: ContractName,
}

impl QualifiedContractIdentifier {
    pub fn new(issuer: StandardPrincipalData, name: ContractName) -> QualifiedContractIdentifier {
        Self { issuer, name }
    }

    pub fn local(name: &str) -> Result<QualifiedContractIdentifier> {
        let name = name.to_string().try_into()?;
        Ok(Self::new(StandardPrincipalData::transient(), name))
    }

    #[allow(clippy::unwrap_used)]
    pub fn transient() -> QualifiedContractIdentifier {
        let name = String::from("__transient").try_into().unwrap();
        Self {
            issuer: StandardPrincipalData::transient(),
            name,
        }
    }

    /// Was this contract issued by the null issuer address? (i.e., is it a "boot contract")
    pub fn is_boot(&self) -> bool {
        self.issuer.1 == [0; 20]
    }

    pub fn parse(literal: &str) -> Result<QualifiedContractIdentifier> {
        let split: Vec<_> = literal.splitn(2, '.').collect();
        if split.len() != 2 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: expected a `.` in a qualified contract name"
                    .to_string(),
            )
            .into());
        }
        let sender = PrincipalData::parse_standard_principal(split[0])?;
        let name = split[1].to_string().try_into()?;
        Ok(QualifiedContractIdentifier::new(sender, name))
    }
}

impl fmt::Display for QualifiedContractIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.issuer, self.name)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum PrincipalData {
    Standard(StandardPrincipalData),
    Contract(QualifiedContractIdentifier),
}

pub enum ContractIdentifier {
    Relative(ContractName),
    Qualified(QualifiedContractIdentifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptionalData {
    pub data: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResponseData {
    pub committed: bool,
    pub data: Box<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallableData {
    pub contract_identifier: QualifiedContractIdentifier,
    pub trait_identifier: Option<TraitIdentifier>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct TraitIdentifier {
    pub name: ClarityName,
    pub contract_identifier: QualifiedContractIdentifier,
}

pub trait StacksAddressExtensions {
    fn to_account_principal(&self) -> PrincipalData;
}

impl StacksAddressExtensions for StacksAddress {
    fn to_account_principal(&self) -> PrincipalData {
        PrincipalData::Standard(StandardPrincipalData(self.version, *self.bytes.as_bytes()))
    }
}

impl TraitIdentifier {
    pub fn new(
        issuer: StandardPrincipalData,
        contract_name: ContractName,
        name: ClarityName,
    ) -> TraitIdentifier {
        Self {
            name,
            contract_identifier: QualifiedContractIdentifier {
                issuer,
                name: contract_name,
            },
        }
    }

    pub fn parse_fully_qualified(literal: &str) -> Result<TraitIdentifier> {
        let (issuer, contract_name, name) = Self::parse(literal)?;
        let issuer = issuer.ok_or(RuntimeErrorType::BadTypeConstruction)?;
        Ok(TraitIdentifier::new(issuer, contract_name, name))
    }

    pub fn parse_sugared_syntax(literal: &str) -> Result<(ContractName, ClarityName)> {
        let (_, contract_name, name) = Self::parse(literal)?;
        Ok((contract_name, name))
    }

    pub fn parse(
        literal: &str,
    ) -> Result<(Option<StandardPrincipalData>, ContractName, ClarityName)> {
        let split: Vec<_> = literal.splitn(3, '.').collect();
        if split.len() != 3 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: expected a `.` in a qualified contract name"
                    .to_string(),
            )
            .into());
        }

        let issuer = match split[0].len() {
            0 => None,
            _ => Some(PrincipalData::parse_standard_principal(split[0])?),
        };
        let contract_name = split[1].to_string().try_into()?;
        let name = split[2].to_string().try_into()?;

        Ok((issuer, contract_name, name))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Int(i128),
    UInt(u128),
    Bool(bool),
    Sequence(SequenceData),
    Principal(PrincipalData),
    Tuple(TupleData),
    Optional(OptionalData),
    Response(ResponseData),
    CallableContract(CallableData),
    // NOTE: any new value variants which may contain _other values_ (i.e.,
    //  compound values like `Optional`, `Tuple`, `Response`, or `Sequence(List)`)
    //  must be handled in the value sanitization routine!
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum SequenceData {
    Buffer(BuffData),
    List(ListData),
    String(CharType),
}

impl SequenceData {
    pub fn atom_values(&mut self) -> Result<Vec<SymbolicExpression>> {
        match self {
            SequenceData::Buffer(ref mut data) => data.atom_values(),
            SequenceData::List(ref mut data) => data.atom_values(),
            SequenceData::String(CharType::ASCII(ref mut data)) => data.atom_values(),
            SequenceData::String(CharType::UTF8(ref mut data)) => data.atom_values(),
        }
    }

    pub fn element_size(&self) -> Result<u32> {
        let out = match self {
            SequenceData::Buffer(..) => TypeSignature::min_buffer()?.size(),
            SequenceData::List(ref data) => data.type_signature.get_list_item_type().size(),
            SequenceData::String(CharType::ASCII(..)) => TypeSignature::min_string_ascii()?.size(),
            SequenceData::String(CharType::UTF8(..)) => TypeSignature::min_string_utf8()?.size(),
        }?;
        Ok(out)
    }

    pub fn len(&self) -> usize {
        match &self {
            SequenceData::Buffer(data) => data.items().len(),
            SequenceData::List(data) => data.items().len(),
            SequenceData::String(CharType::ASCII(data)) => data.items().len(),
            SequenceData::String(CharType::UTF8(data)) => data.items().len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn element_at(self, index: usize) -> Result<Option<Value>> {
        if self.len() <= index {
            return Ok(None);
        }
        let result = match self {
            SequenceData::Buffer(data) => Value::buff_from_byte(data.data[index]),
            SequenceData::List(mut data) => data.data.remove(index),
            SequenceData::String(CharType::ASCII(data)) => {
                Value::string_ascii_from_bytes(vec![data.data[index]]).map_err(|_| {
                    InterpreterError::Expect(
                        "BUG: failed to initialize single-byte ASCII buffer".into(),
                    )
                })?
            }
            SequenceData::String(CharType::UTF8(mut data)) => {
                Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data {
                    data: vec![data.data.remove(index)],
                })))
            }
        };

        Ok(Some(result))
    }

    pub fn replace_at(self, epoch: &StacksEpochId, index: usize, element: Value) -> Result<Value> {
        let seq_length = self.len();

        // Check that the length of the provided element is 1. In the case that SequenceData
        // is a list, we check that the provided element is the right type below.
        if !self.is_list() {
            if let Value::Sequence(data) = &element {
                let elem_length = data.len();
                if elem_length != 1 {
                    return Err(RuntimeErrorType::BadTypeConstruction.into());
                }
            } else {
                return Err(RuntimeErrorType::BadTypeConstruction.into());
            }
        }
        if index >= seq_length {
            return Err(CheckErrors::ValueOutOfBounds.into());
        }

        let new_seq_data = match (self, element) {
            (SequenceData::Buffer(mut data), Value::Sequence(SequenceData::Buffer(elem))) => {
                data.data[index] = elem.data[0];
                SequenceData::Buffer(data)
            }
            (SequenceData::List(mut data), elem) => {
                let entry_type = data.type_signature.get_list_item_type();
                if !entry_type.admits(epoch, &elem)? {
                    return Err(CheckErrors::ListTypesMustMatch.into());
                }
                data.data[index] = elem;
                SequenceData::List(data)
            }
            (
                SequenceData::String(CharType::ASCII(mut data)),
                Value::Sequence(SequenceData::String(CharType::ASCII(elem))),
            ) => {
                data.data[index] = elem.data[0];
                SequenceData::String(CharType::ASCII(data))
            }
            (
                SequenceData::String(CharType::UTF8(mut data)),
                Value::Sequence(SequenceData::String(CharType::UTF8(mut elem))),
            ) => {
                data.data[index] = elem.data.swap_remove(0);
                SequenceData::String(CharType::UTF8(data))
            }
            _ => return Err(CheckErrors::ListTypesMustMatch.into()),
        };

        Value::some(Value::Sequence(new_seq_data))
    }

    pub fn contains(&self, to_find: Value) -> Result<Option<usize>> {
        match self {
            SequenceData::Buffer(ref data) => {
                if let Value::Sequence(SequenceData::Buffer(to_find_vec)) = to_find {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(CheckErrors::TypeValueError(TypeSignature::min_buffer()?, to_find).into())
                }
            }
            SequenceData::List(ref data) => {
                for (index, entry) in data.data.iter().enumerate() {
                    if entry == &to_find {
                        return Ok(Some(index));
                    }
                }
                Ok(None)
            }
            SequenceData::String(CharType::ASCII(ref data)) => {
                if let Value::Sequence(SequenceData::String(CharType::ASCII(to_find_vec))) = to_find
                {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(
                        CheckErrors::TypeValueError(TypeSignature::min_string_ascii()?, to_find)
                            .into(),
                    )
                }
            }
            SequenceData::String(CharType::UTF8(ref data)) => {
                if let Value::Sequence(SequenceData::String(CharType::UTF8(to_find_vec))) = to_find
                {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(
                        CheckErrors::TypeValueError(TypeSignature::min_string_utf8()?, to_find)
                            .into(),
                    )
                }
            }
        }
    }

    pub fn filter<F>(&mut self, filter: &mut F) -> Result<()>
    where
        F: FnMut(SymbolicExpression) -> Result<bool>,
    {
        // Note: this macro can probably get removed once
        // ```Vec::drain_filter<F>(&mut self, filter: F) -> DrainFilter<T, F>```
        // is available in rust stable channel (experimental at this point).
        macro_rules! drain_filter {
            ($data:expr, $seq_type:ident) => {
                let mut i = 0;
                while i != $data.data.len() {
                    let atom_value =
                        SymbolicExpression::atom_value($seq_type::to_value(&$data.data[i])?);
                    match filter(atom_value) {
                        Ok(res) if res == false => {
                            $data.data.remove(i);
                        }
                        Ok(_) => {
                            i += 1;
                        }
                        Err(err) => return Err(err),
                    }
                }
            };
        }

        match self {
            SequenceData::Buffer(ref mut data) => {
                drain_filter!(data, BuffData);
            }
            SequenceData::List(ref mut data) => {
                drain_filter!(data, ListData);
            }
            SequenceData::String(CharType::ASCII(ref mut data)) => {
                drain_filter!(data, ASCIIData);
            }
            SequenceData::String(CharType::UTF8(ref mut data)) => {
                drain_filter!(data, UTF8Data);
            }
        }
        Ok(())
    }

    pub fn concat(&mut self, epoch: &StacksEpochId, other_seq: SequenceData) -> Result<()> {
        match (self, other_seq) {
            (SequenceData::List(ref mut inner_data), SequenceData::List(other_inner_data)) => {
                inner_data.append(epoch, other_inner_data)
            }
            (
                SequenceData::Buffer(ref mut inner_data),
                SequenceData::Buffer(ref mut other_inner_data),
            ) => inner_data.append(other_inner_data),
            (
                SequenceData::String(CharType::ASCII(ref mut inner_data)),
                SequenceData::String(CharType::ASCII(ref mut other_inner_data)),
            ) => inner_data.append(other_inner_data),
            (
                SequenceData::String(CharType::UTF8(ref mut inner_data)),
                SequenceData::String(CharType::UTF8(ref mut other_inner_data)),
            ) => inner_data.append(other_inner_data),
            _ => Err(RuntimeErrorType::BadTypeConstruction.into()),
        }?;
        Ok(())
    }

    pub fn slice(
        self,
        epoch: &StacksEpochId,
        left_position: usize,
        right_position: usize,
    ) -> Result<Value> {
        let empty_seq = left_position == right_position;

        let result = match self {
            SequenceData::Buffer(data) => {
                let data = if empty_seq {
                    vec![]
                } else {
                    data.data[left_position..right_position].to_vec()
                };
                Value::buff_from(data)
            }
            SequenceData::List(data) => {
                let data = if empty_seq {
                    vec![]
                } else {
                    data.data[left_position..right_position].to_vec()
                };
                Value::cons_list(data, epoch)
            }
            SequenceData::String(CharType::ASCII(data)) => {
                let data = if empty_seq {
                    vec![]
                } else {
                    data.data[left_position..right_position].to_vec()
                };
                Value::string_ascii_from_bytes(data)
            }
            SequenceData::String(CharType::UTF8(data)) => {
                let data = if empty_seq {
                    vec![]
                } else {
                    data.data[left_position..right_position].to_vec()
                };
                Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
                    UTF8Data { data },
                ))))
            }
        }?;

        Ok(result)
    }

    pub fn is_list(&self) -> bool {
        matches!(self, SequenceData::List(..))
    }
}

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum CharType {
    UTF8(UTF8Data),
    ASCII(ASCIIData),
}

impl fmt::Display for CharType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CharType::ASCII(string) => write!(f, "{}", string),
            CharType::UTF8(string) => write!(f, "{}", string),
        }
    }
}

impl fmt::Debug for CharType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ASCIIData {
    pub data: Vec<u8>,
}

impl fmt::Display for ASCIIData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut escaped_str = String::new();
        for c in self.data.iter() {
            let escaped_char = format!("{}", std::ascii::escape_default(*c));
            escaped_str.push_str(&escaped_char);
        }
        write!(f, "\"{}\"", escaped_str)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UTF8Data {
    pub data: Vec<Vec<u8>>,
}

impl fmt::Display for UTF8Data {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();
        for c in self.data.iter() {
            if c.len() > 1 {
                // We escape extended charset
                result.push_str(&format!("\\u{{{}}}", hash::to_hex(&c[..])));
            } else {
                // We render an ASCII char, escaped
                let escaped_char = format!("{}", std::ascii::escape_default(c[0]));
                result.push_str(&escaped_char);
            }
        }
        write!(f, "u\"{}\"", result)
    }
}

pub trait SequencedValue<T> {
    fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors>;

    fn items(&self) -> &Vec<T>;

    fn drained_items(&mut self) -> Vec<T>;

    fn to_value(v: &T) -> Result<Value>;

    fn atom_values(&mut self) -> Result<Vec<SymbolicExpression>> {
        self.drained_items()
            .iter()
            .map(|item| Ok(SymbolicExpression::atom_value(Self::to_value(item)?)))
            .collect()
    }
}

impl SequencedValue<Value> for ListData {
    fn items(&self) -> &Vec<Value> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<Value> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        Ok(TypeSignature::SequenceType(SequenceSubtype::ListType(
            self.type_signature.clone(),
        )))
    }

    fn to_value(v: &Value) -> Result<Value> {
        Ok(v.clone())
    }
}

impl SequencedValue<u8> for BuffData {
    fn items(&self) -> &Vec<u8> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<u8> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        let buff_length = BufferLength::try_from(self.data.len()).map_err(|_| {
            CheckErrors::Expects("ERROR: Too large of a buffer successfully constructed.".into())
        })?;
        Ok(TypeSignature::SequenceType(SequenceSubtype::BufferType(
            buff_length,
        )))
    }

    fn to_value(v: &u8) -> Result<Value> {
        Ok(Value::buff_from_byte(*v))
    }
}

impl SequencedValue<u8> for ASCIIData {
    fn items(&self) -> &Vec<u8> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<u8> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        let buff_length = BufferLength::try_from(self.data.len()).map_err(|_| {
            CheckErrors::Expects("ERROR: Too large of a buffer successfully constructed.".into())
        })?;
        Ok(TypeSignature::SequenceType(SequenceSubtype::StringType(
            StringSubtype::ASCII(buff_length),
        )))
    }

    fn to_value(v: &u8) -> Result<Value> {
        Value::string_ascii_from_bytes(vec![*v]).map_err(|_| {
            InterpreterError::Expect("ERROR: Invalid ASCII string successfully constructed".into())
                .into()
        })
    }
}

impl SequencedValue<Vec<u8>> for UTF8Data {
    fn items(&self) -> &Vec<Vec<u8>> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<Vec<u8>> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        let str_len = StringUTF8Length::try_from(self.data.len()).map_err(|_| {
            CheckErrors::Expects("ERROR: Too large of a buffer successfully constructed.".into())
        })?;
        Ok(TypeSignature::SequenceType(SequenceSubtype::StringType(
            StringSubtype::UTF8(str_len),
        )))
    }

    fn to_value(v: &Vec<u8>) -> Result<Value> {
        Value::string_utf8_from_bytes(v.clone()).map_err(|_| {
            InterpreterError::Expect("ERROR: Invalid UTF8 string successfully constructed".into())
                .into()
        })
    }
}

// Properties for "get-block-info".
define_versioned_named_enum!(BlockInfoProperty(ClarityVersion) {
    Time("time", ClarityVersion::Clarity1),
    VrfSeed("vrf-seed", ClarityVersion::Clarity1),
    HeaderHash("header-hash", ClarityVersion::Clarity1),
    IdentityHeaderHash("id-header-hash", ClarityVersion::Clarity1),
    BurnchainHeaderHash("burnchain-header-hash", ClarityVersion::Clarity1),
    MinerAddress("miner-address", ClarityVersion::Clarity1),
    MinerSpendWinner("miner-spend-winner", ClarityVersion::Clarity2),
    MinerSpendTotal("miner-spend-total", ClarityVersion::Clarity2),
    BlockReward("block-reward", ClarityVersion::Clarity2),
});

// Properties for "get-burn-block-info".
define_named_enum!(BurnBlockInfoProperty {
    HeaderHash("header-hash"),
    PoxAddrs("pox-addrs"),
});

define_named_enum!(StacksBlockInfoProperty {
    IndexHeaderHash("id-header-hash"),
    HeaderHash("header-hash"),
    Time("time"),
});

define_named_enum!(TenureInfoProperty {
    Time("time"),
    VrfSeed("vrf-seed"),
    BurnchainHeaderHash("burnchain-header-hash"),
    MinerAddress("miner-address"),
    MinerSpendWinner("miner-spend-winner"),
    MinerSpendTotal("miner-spend-total"),
    BlockReward("block-reward"),
});

impl OptionalData {
    pub fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        let type_result = match self.data {
            Some(ref v) => TypeSignature::new_option(TypeSignature::type_of(v)?),
            None => TypeSignature::new_option(TypeSignature::NoType),
        };
        type_result.map_err(|_| {
            CheckErrors::Expects("Should not have constructed too large of a type.".into())
        })
    }
}

impl ResponseData {
    pub fn type_signature(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        let type_result = match self.committed {
            true => TypeSignature::new_response(
                TypeSignature::type_of(&self.data)?,
                TypeSignature::NoType,
            ),
            false => TypeSignature::new_response(
                TypeSignature::NoType,
                TypeSignature::type_of(&self.data)?,
            ),
        };
        type_result.map_err(|_| {
            CheckErrors::Expects("Should not have constructed too large of a type.".into())
        })
    }
}

impl BlockInfoProperty {
    pub fn type_result(&self) -> TypeSignature {
        use self::BlockInfoProperty::*;
        match self {
            Time | MinerSpendWinner | MinerSpendTotal | BlockReward => TypeSignature::UIntType,
            IdentityHeaderHash | VrfSeed | HeaderHash | BurnchainHeaderHash => BUFF_32.clone(),
            MinerAddress => TypeSignature::PrincipalType,
        }
    }
}

impl BurnBlockInfoProperty {
    pub fn type_result(&self) -> std::result::Result<TypeSignature, CheckErrors> {
        use self::BurnBlockInfoProperty::*;
        let result = match self {
            HeaderHash => BUFF_32.clone(),
            PoxAddrs => TupleTypeSignature::try_from(vec![
                (
                    "addrs".into(),
                    TypeSignature::list_of(
                        TypeSignature::TupleType(
                            TupleTypeSignature::try_from(vec![
                                ("version".into(), BUFF_1.clone()),
                                ("hashbytes".into(), BUFF_32.clone()),
                            ])
                            .map_err(|_| {
                                CheckErrors::Expects(
                                    "FATAL: bad type signature for pox addr".into(),
                                )
                            })?,
                        ),
                        2,
                    )
                    .map_err(|_| CheckErrors::Expects("FATAL: bad list type signature".into()))?,
                ),
                ("payout".into(), TypeSignature::UIntType),
            ])
            .map_err(|_| CheckErrors::Expects("FATAL: bad type signature for pox addr".into()))?
            .into(),
        };
        Ok(result)
    }
}

impl StacksBlockInfoProperty {
    pub fn type_result(&self) -> TypeSignature {
        use self::StacksBlockInfoProperty::*;
        match self {
            Time => TypeSignature::UIntType,
            IndexHeaderHash | HeaderHash => BUFF_32.clone(),
        }
    }
}

impl TenureInfoProperty {
    pub fn type_result(&self) -> TypeSignature {
        use self::TenureInfoProperty::*;
        match self {
            Time | MinerSpendWinner | MinerSpendTotal | BlockReward => TypeSignature::UIntType,
            VrfSeed | BurnchainHeaderHash => BUFF_32.clone(),
            MinerAddress => TypeSignature::PrincipalType,
        }
    }
}

impl PartialEq for ListData {
    fn eq(&self, other: &ListData) -> bool {
        self.data == other.data
    }
}

impl PartialEq for TupleData {
    fn eq(&self, other: &TupleData) -> bool {
        self.data_map == other.data_map
    }
}

pub const NONE: Value = Value::Optional(OptionalData { data: None });

impl Value {
    pub fn some(data: Value) -> Result<Value> {
        if data.size()? + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth()? + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Optional(OptionalData {
                data: Some(Box::new(data)),
            }))
        }
    }

    pub fn none() -> Value {
        NONE.clone()
    }

    pub fn okay_true() -> Value {
        Value::Response(ResponseData {
            committed: true,
            data: Box::new(Value::Bool(true)),
        })
    }

    pub fn err_uint(ecode: u128) -> Value {
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(Value::UInt(ecode)),
        })
    }

    pub fn err_none() -> Value {
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(NONE.clone()),
        })
    }

    pub fn okay(data: Value) -> Result<Value> {
        if data.size()? + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth()? + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Response(ResponseData {
                committed: true,
                data: Box::new(data),
            }))
        }
    }

    pub fn error(data: Value) -> Result<Value> {
        if data.size()? + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth()? + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Response(ResponseData {
                committed: false,
                data: Box::new(data),
            }))
        }
    }

    pub fn size(&self) -> Result<u32> {
        Ok(TypeSignature::type_of(self)?.size()?)
    }

    pub fn depth(&self) -> Result<u8> {
        Ok(TypeSignature::type_of(self)?.depth())
    }

    /// Invariant: the supplied Values have already been "checked", i.e., it's a valid Value object
    ///  this invariant is enforced through the Value constructors, each of which checks to ensure
    ///  that any typing data is correct.
    pub fn list_with_type(
        epoch: &StacksEpochId,
        list_data: Vec<Value>,
        expected_type: ListTypeData,
    ) -> Result<Value> {
        // Constructors for TypeSignature ensure that the size of the Value cannot
        //   be greater than MAX_VALUE_SIZE (they error on such constructions)
        //   so we do not need to perform that check here.
        if (expected_type.get_max_len() as usize) < list_data.len() {
            return Err(InterpreterError::FailureConstructingListWithType.into());
        }

        {
            let expected_item_type = expected_type.get_list_item_type();

            for item in &list_data {
                if !expected_item_type.admits(epoch, item)? {
                    return Err(InterpreterError::FailureConstructingListWithType.into());
                }
            }
        }

        Ok(Value::Sequence(SequenceData::List(ListData {
            data: list_data,
            type_signature: expected_type,
        })))
    }

    pub fn cons_list_unsanitized(list_data: Vec<Value>) -> Result<Value> {
        let type_sig = TypeSignature::construct_parent_list_type(&list_data)?;
        Ok(Value::Sequence(SequenceData::List(ListData {
            data: list_data,
            type_signature: type_sig,
        })))
    }

    pub fn cons_list(list_data: Vec<Value>, epoch: &StacksEpochId) -> Result<Value> {
        // Constructors for TypeSignature ensure that the size of the Value cannot
        //   be greater than MAX_VALUE_SIZE (they error on such constructions)
        // Aaron: at this point, we've _already_ allocated memory for this type.
        //     (e.g., from a (map...) call, or a (list...) call.
        //     this is a problem _if_ the static analyzer cannot already prevent
        //     this case. This applies to all the constructor size checks.
        let type_sig = TypeSignature::construct_parent_list_type(&list_data)?;
        let list_data_opt: Option<_> = list_data
            .into_iter()
            .map(|item| {
                Value::sanitize_value(epoch, type_sig.get_list_item_type(), item)
                    .map(|(value, _did_sanitize)| value)
            })
            .collect();
        let list_data = list_data_opt.ok_or_else(|| CheckErrors::ListTypesMustMatch)?;
        Ok(Value::Sequence(SequenceData::List(ListData {
            data: list_data,
            type_signature: type_sig,
        })))
    }

    /// # Errors
    /// - CheckErrors::ValueTooLarge if `buff_data` is too large.
    pub fn buff_from(buff_data: Vec<u8>) -> Result<Value> {
        // check the buffer size
        BufferLength::try_from(buff_data.len())?;
        // construct the buffer
        Ok(Value::Sequence(SequenceData::Buffer(BuffData {
            data: buff_data,
        })))
    }

    pub fn buff_from_byte(byte: u8) -> Value {
        Value::Sequence(SequenceData::Buffer(BuffData { data: vec![byte] }))
    }

    pub fn string_ascii_from_bytes(bytes: Vec<u8>) -> Result<Value> {
        // check the string size
        BufferLength::try_from(bytes.len())?;

        for b in bytes.iter() {
            if !b.is_ascii_alphanumeric() && !b.is_ascii_punctuation() && !b.is_ascii_whitespace() {
                return Err(CheckErrors::InvalidCharactersDetected.into());
            }
        }
        // construct the string
        Ok(Value::Sequence(SequenceData::String(CharType::ASCII(
            ASCIIData { data: bytes },
        ))))
    }

    pub fn string_utf8_from_string_utf8_literal(tokenized_str: String) -> Result<Value> {
        let wrapped_codepoints_matcher = Regex::new("^\\\\u\\{(?P<value>[[:xdigit:]]+)\\}")
            .map_err(|_| InterpreterError::Expect("Bad regex".into()))?;
        let mut window = tokenized_str.as_str();
        let mut cursor = 0;
        let mut data: Vec<Vec<u8>> = vec![];
        while !window.is_empty() {
            if let Some(captures) = wrapped_codepoints_matcher.captures(window) {
                let matched = captures
                    .name("value")
                    .ok_or_else(|| InterpreterError::Expect("Expected capture".into()))?;
                let scalar_value = window[matched.start()..matched.end()].to_string();
                let unicode_char = {
                    let u = u32::from_str_radix(&scalar_value, 16)
                        .map_err(|_| CheckErrors::InvalidUTF8Encoding)?;
                    let c = char::from_u32(u).ok_or_else(|| CheckErrors::InvalidUTF8Encoding)?;
                    let mut encoded_char: Vec<u8> = vec![0; c.len_utf8()];
                    c.encode_utf8(&mut encoded_char[..]);
                    encoded_char
                };

                data.push(unicode_char);
                cursor += scalar_value.len() + 4;
            } else {
                let ascii_char = window[0..1].to_string().into_bytes();
                data.push(ascii_char);
                cursor += 1;
            }
            // check the string size
            StringUTF8Length::try_from(data.len())?;

            window = &tokenized_str[cursor..];
        }
        // construct the string
        Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
            UTF8Data { data },
        ))))
    }

    pub fn string_utf8_from_bytes(bytes: Vec<u8>) -> Result<Value> {
        let validated_utf8_str = match str::from_utf8(&bytes) {
            Ok(string) => string,
            _ => return Err(CheckErrors::InvalidCharactersDetected.into()),
        };
        let data = validated_utf8_str
            .chars()
            .map(|char| {
                let mut encoded_char = vec![0u8; char.len_utf8()];
                char.encode_utf8(&mut encoded_char);
                encoded_char
            })
            .collect::<Vec<_>>();
        // check the string size
        StringUTF8Length::try_from(data.len())?;

        Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
            UTF8Data { data },
        ))))
    }

    pub fn string_utf8_from_unicode_scalars(scalars: Vec<u8>) -> Result<Value> {
        let chars_result: Result<Vec<char>> = scalars
            .chunks(4)
            .map(|chunk| {
                if chunk.len() == 4 {
                    let value = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
                    std::char::from_u32(value).ok_or(CheckErrors::InvalidCharactersDetected.into())
                } else {
                    Err(CheckErrors::InvalidCharactersDetected.into())
                }
            })
            .collect();

        let validated_utf8_str: String = chars_result?.into_iter().collect();

        let mut data = vec![];
        for char in validated_utf8_str.chars() {
            let mut encoded_char: Vec<u8> = vec![0; char.len_utf8()];
            char.encode_utf8(&mut encoded_char[..]);
            data.push(encoded_char);
        }
        // check the string size
        StringUTF8Length::try_from(data.len())?;

        Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
            UTF8Data { data },
        ))))
    }

    pub fn expect_ascii(self) -> Result<String> {
        if let Value::Sequence(SequenceData::String(CharType::ASCII(ASCIIData { data }))) = self {
            Ok(String::from_utf8(data)
                .map_err(|_| InterpreterError::Expect("Non UTF-8 data in string".into()))?)
        } else {
            error!("Value '{:?}' is not an ASCII string", &self);
            Err(InterpreterError::Expect("Expected ASCII string".into()).into())
        }
    }

    pub fn expect_u128(self) -> Result<u128> {
        if let Value::UInt(inner) = self {
            Ok(inner)
        } else {
            error!("Value '{:?}' is not a u128", &self);
            Err(InterpreterError::Expect("Expected u128".into()).into())
        }
    }

    pub fn expect_i128(self) -> Result<i128> {
        if let Value::Int(inner) = self {
            Ok(inner)
        } else {
            error!("Value '{:?}' is not an i128", &self);
            Err(InterpreterError::Expect("Expected i128".into()).into())
        }
    }

    pub fn expect_buff(self, sz: usize) -> Result<Vec<u8>> {
        if let Value::Sequence(SequenceData::Buffer(buffdata)) = self {
            if buffdata.data.len() <= sz {
                Ok(buffdata.data)
            } else {
                error!(
                    "Value buffer has len {}, expected {}",
                    buffdata.data.len(),
                    sz
                );
                Err(InterpreterError::Expect("Unexpected buff length".into()).into())
            }
        } else {
            error!("Value '{:?}' is not a buff", &self);
            Err(InterpreterError::Expect("Expected buff".into()).into())
        }
    }

    pub fn expect_list(self) -> Result<Vec<Value>> {
        if let Value::Sequence(SequenceData::List(listdata)) = self {
            Ok(listdata.data)
        } else {
            error!("Value '{:?}' is not a list", &self);
            Err(InterpreterError::Expect("Expected list".into()).into())
        }
    }

    pub fn expect_buff_padded(self, sz: usize, pad: u8) -> Result<Vec<u8>> {
        let mut data = self.expect_buff(sz)?;
        if sz > data.len() {
            for _ in data.len()..sz {
                data.push(pad)
            }
        }
        Ok(data)
    }

    pub fn expect_bool(self) -> Result<bool> {
        if let Value::Bool(b) = self {
            Ok(b)
        } else {
            error!("Value '{:?}' is not a bool", &self);
            Err(InterpreterError::Expect("Expected bool".into()).into())
        }
    }

    pub fn expect_tuple(self) -> Result<TupleData> {
        if let Value::Tuple(data) = self {
            Ok(data)
        } else {
            error!("Value '{:?}' is not a tuple", &self);
            Err(InterpreterError::Expect("Expected tuple".into()).into())
        }
    }

    pub fn expect_optional(self) -> Result<Option<Value>> {
        if let Value::Optional(opt) = self {
            match opt.data {
                Some(boxed_value) => Ok(Some(*boxed_value)),
                None => Ok(None),
            }
        } else {
            error!("Value '{:?}' is not an optional", &self);
            Err(InterpreterError::Expect("Expected optional".into()).into())
        }
    }

    pub fn expect_principal(self) -> Result<PrincipalData> {
        if let Value::Principal(p) = self {
            Ok(p)
        } else {
            error!("Value '{:?}' is not a principal", &self);
            Err(InterpreterError::Expect("Expected principal".into()).into())
        }
    }

    pub fn expect_callable(self) -> Result<CallableData> {
        if let Value::CallableContract(t) = self {
            Ok(t)
        } else {
            error!("Value '{:?}' is not a callable contract", &self);
            Err(InterpreterError::Expect("Expected callable".into()).into())
        }
    }

    pub fn expect_result(self) -> Result<std::result::Result<Value, Value>> {
        if let Value::Response(res_data) = self {
            if res_data.committed {
                Ok(Ok(*res_data.data))
            } else {
                Ok(Err(*res_data.data))
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            Err(InterpreterError::Expect("Expected response".into()).into())
        }
    }

    pub fn expect_result_ok(self) -> Result<Value> {
        if let Value::Response(res_data) = self {
            if res_data.committed {
                Ok(*res_data.data)
            } else {
                error!("Value is not a (ok ..)");
                Err(InterpreterError::Expect("Expected ok response".into()).into())
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            Err(InterpreterError::Expect("Expected response".into()).into())
        }
    }

    pub fn expect_result_err(self) -> Result<Value> {
        if let Value::Response(res_data) = self {
            if !res_data.committed {
                Ok(*res_data.data)
            } else {
                error!("Value is not a (err ..)");
                Err(InterpreterError::Expect("Expected err response".into()).into())
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            Err(InterpreterError::Expect("Expected response".into()).into())
        }
    }
}

impl BuffData {
    pub fn len(&self) -> Result<BufferLength> {
        self.data
            .len()
            .try_into()
            .map_err(|_| InterpreterError::Expect("Data length should be valid".into()).into())
    }

    pub fn as_slice(&self) -> &[u8] {
        self.data.as_slice()
    }

    fn append(&mut self, other_seq: &mut BuffData) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn empty() -> Self {
        Self { data: Vec::new() }
    }
}

impl ListData {
    pub fn len(&self) -> Result<u32> {
        self.data
            .len()
            .try_into()
            .map_err(|_| InterpreterError::Expect("Data length should be valid".into()).into())
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn append(&mut self, epoch: &StacksEpochId, other_seq: ListData) -> Result<()> {
        let entry_type_a = self.type_signature.get_list_item_type();
        let entry_type_b = other_seq.type_signature.get_list_item_type();
        let entry_type = TypeSignature::factor_out_no_type(epoch, entry_type_a, entry_type_b)?;
        let max_len = self.type_signature.get_max_len() + other_seq.type_signature.get_max_len();
        for item in other_seq.data.into_iter() {
            let (item, _) = Value::sanitize_value(epoch, &entry_type, item)
                .ok_or_else(|| CheckErrors::ListTypesMustMatch)?;
            self.data.push(item);
        }

        self.type_signature = ListTypeData::new_list(entry_type, max_len)?;
        Ok(())
    }
}

impl ASCIIData {
    fn append(&mut self, other_seq: &mut ASCIIData) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn len(&self) -> Result<BufferLength> {
        self.data
            .len()
            .try_into()
            .map_err(|_| InterpreterError::Expect("Data length should be valid".into()).into())
    }
}

impl UTF8Data {
    fn append(&mut self, other_seq: &mut UTF8Data) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn len(&self) -> Result<BufferLength> {
        self.data
            .len()
            .try_into()
            .map_err(|_| InterpreterError::Expect("Data length should be valid".into()).into())
    }
}

impl fmt::Display for OptionalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.data {
            Some(ref x) => write!(f, "(some {})", x),
            None => write!(f, "none"),
        }
    }
}

impl fmt::Display for ResponseData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.committed {
            true => write!(f, "(ok {})", self.data),
            false => write!(f, "(err {})", self.data),
        }
    }
}

impl fmt::Display for BuffData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", hash::to_hex(&self.data))
    }
}

impl fmt::Debug for BuffData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(int) => write!(f, "{}", int),
            Value::UInt(int) => write!(f, "u{}", int),
            Value::Bool(boolean) => write!(f, "{}", boolean),
            Value::Tuple(data) => write!(f, "{}", data),
            Value::Principal(principal_data) => write!(f, "{}", principal_data),
            Value::Optional(opt_data) => write!(f, "{}", opt_data),
            Value::Response(res_data) => write!(f, "{}", res_data),
            Value::Sequence(SequenceData::Buffer(vec_bytes)) => write!(f, "0x{}", &vec_bytes),
            Value::Sequence(SequenceData::String(string)) => write!(f, "{}", string),
            Value::Sequence(SequenceData::List(list_data)) => {
                write!(f, "(")?;
                for (ix, v) in list_data.data.iter().enumerate() {
                    if ix > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
            Value::CallableContract(callable_data) => write!(f, "{}", callable_data),
        }
    }
}

impl PrincipalData {
    pub fn version(&self) -> u8 {
        match self {
            PrincipalData::Standard(StandardPrincipalData(version, _)) => *version,
            PrincipalData::Contract(QualifiedContractIdentifier { issuer, name: _ }) => issuer.0,
        }
    }

    pub fn parse(literal: &str) -> Result<PrincipalData> {
        // be permissive about leading single-quote
        let literal = literal.strip_prefix('\'').unwrap_or(literal);

        if literal.contains('.') {
            PrincipalData::parse_qualified_contract_principal(literal)
        } else {
            PrincipalData::parse_standard_principal(literal).map(PrincipalData::from)
        }
    }

    pub fn parse_qualified_contract_principal(literal: &str) -> Result<PrincipalData> {
        let contract_id = QualifiedContractIdentifier::parse(literal)?;
        Ok(PrincipalData::Contract(contract_id))
    }

    pub fn parse_standard_principal(literal: &str) -> Result<StandardPrincipalData> {
        let (version, data) = c32::c32_address_decode(literal).map_err(|x| {
            RuntimeErrorType::ParseError(format!("Invalid principal literal: {}", x))
        })?;
        if data.len() != 20 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: Expected 20 data bytes.".to_string(),
            )
            .into());
        }
        let mut fixed_data = [0; 20];
        fixed_data.copy_from_slice(&data[..20]);
        Ok(StandardPrincipalData(version, fixed_data))
    }
}

impl StandardPrincipalData {
    pub fn to_address(&self) -> String {
        c32::c32_address(self.0, &self.1[..]).unwrap_or_else(|_| "INVALID_C32_ADD".to_string())
    }
}

impl fmt::Display for StandardPrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let c32_str = self.to_address();
        write!(f, "{}", c32_str)
    }
}

impl fmt::Debug for StandardPrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let c32_str = self.to_address();
        write!(f, "StandardPrincipalData({})", c32_str)
    }
}

impl fmt::Display for PrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PrincipalData::Standard(sender) => write!(f, "{}", sender),
            PrincipalData::Contract(contract_identifier) => write!(
                f,
                "{}.{}",
                contract_identifier.issuer, contract_identifier.name
            ),
        }
    }
}

impl fmt::Display for CallableData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(trait_identifier) = &self.trait_identifier {
            write!(
                f,
                "({} as <{}>)",
                self.contract_identifier, trait_identifier,
            )
        } else {
            write!(f, "{}", self.contract_identifier,)
        }
    }
}

impl fmt::Display for TraitIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.contract_identifier, self.name)
    }
}

impl From<StacksAddress> for StandardPrincipalData {
    fn from(addr: StacksAddress) -> StandardPrincipalData {
        StandardPrincipalData(addr.version, addr.bytes.0)
    }
}

impl From<StacksAddress> for PrincipalData {
    fn from(addr: StacksAddress) -> PrincipalData {
        PrincipalData::from(StandardPrincipalData::from(addr))
    }
}

impl From<StandardPrincipalData> for StacksAddress {
    fn from(o: StandardPrincipalData) -> StacksAddress {
        StacksAddress {
            version: o.0,
            bytes: hash::Hash160(o.1),
        }
    }
}

impl From<StandardPrincipalData> for Value {
    fn from(principal: StandardPrincipalData) -> Self {
        Value::Principal(PrincipalData::from(principal))
    }
}

impl From<QualifiedContractIdentifier> for Value {
    fn from(principal: QualifiedContractIdentifier) -> Self {
        Value::Principal(PrincipalData::Contract(principal))
    }
}

impl From<PrincipalData> for Value {
    fn from(p: PrincipalData) -> Self {
        Value::Principal(p)
    }
}

impl From<StandardPrincipalData> for PrincipalData {
    fn from(p: StandardPrincipalData) -> Self {
        PrincipalData::Standard(p)
    }
}

impl From<QualifiedContractIdentifier> for PrincipalData {
    fn from(principal: QualifiedContractIdentifier) -> Self {
        PrincipalData::Contract(principal)
    }
}

impl From<TupleData> for Value {
    fn from(t: TupleData) -> Self {
        Value::Tuple(t)
    }
}

impl From<ASCIIData> for Value {
    fn from(ascii: ASCIIData) -> Self {
        Value::Sequence(SequenceData::String(CharType::ASCII(ascii)))
    }
}
impl From<ContractName> for ASCIIData {
    fn from(name: ContractName) -> Self {
        // ContractName is guaranteed to be between 5 and 40 bytes and contains only printable
        // ASCII already, so this conversion should not fail.
        ASCIIData {
            data: name.as_str().as_bytes().to_vec(),
        }
    }
}

impl TupleData {
    fn new(
        type_signature: TupleTypeSignature,
        data_map: BTreeMap<ClarityName, Value>,
    ) -> Result<TupleData> {
        let t = TupleData {
            type_signature,
            data_map,
        };
        Ok(t)
    }

    /// Return the number of fields in this tuple value
    pub fn len(&self) -> u64 {
        self.data_map.len() as u64
    }

    /// Checks whether the tuple value is empty
    pub fn is_empty(&self) -> bool {
        self.data_map.is_empty()
    }

    // TODO: add tests from mutation testing results #4833
    #[cfg_attr(test, mutants::skip)]
    pub fn from_data(data: Vec<(ClarityName, Value)>) -> Result<TupleData> {
        let mut type_map = BTreeMap::new();
        let mut data_map = BTreeMap::new();
        for (name, value) in data.into_iter() {
            let type_info = TypeSignature::type_of(&value)?;
            let entry = type_map.entry(name.clone());
            match entry {
                Entry::Vacant(e) => e.insert(type_info),
                Entry::Occupied(_) => return Err(CheckErrors::NameAlreadyUsed(name.into()).into()),
            };
            data_map.insert(name, value);
        }

        Self::new(TupleTypeSignature::try_from(type_map)?, data_map)
    }

    // TODO: add tests from mutation testing results #4834
    #[cfg_attr(test, mutants::skip)]
    pub fn from_data_typed(
        epoch: &StacksEpochId,
        data: Vec<(ClarityName, Value)>,
        expected: &TupleTypeSignature,
    ) -> Result<TupleData> {
        let mut data_map = BTreeMap::new();
        for (name, value) in data.into_iter() {
            let expected_type = expected
                .field_type(&name)
                .ok_or(InterpreterError::FailureConstructingTupleWithType)?;
            if !expected_type.admits(epoch, &value)? {
                return Err(InterpreterError::FailureConstructingTupleWithType.into());
            }
            data_map.insert(name, value);
        }
        Self::new(expected.clone(), data_map)
    }

    pub fn get(&self, name: &str) -> Result<&Value> {
        self.data_map.get(name).ok_or_else(|| {
            CheckErrors::NoSuchTupleField(name.to_string(), self.type_signature.clone()).into()
        })
    }

    pub fn get_owned(mut self, name: &str) -> Result<Value> {
        self.data_map.remove(name).ok_or_else(|| {
            CheckErrors::NoSuchTupleField(name.to_string(), self.type_signature.clone()).into()
        })
    }

    pub fn shallow_merge(mut base: TupleData, updates: TupleData) -> Result<TupleData> {
        let TupleData {
            data_map,
            mut type_signature,
        } = updates;
        for (name, value) in data_map.into_iter() {
            base.data_map.insert(name, value);
        }
        base.type_signature.shallow_merge(&mut type_signature);
        Ok(base)
    }
}

impl fmt::Display for TupleData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(tuple")?;
        for (name, value) in self.data_map.iter() {
            write!(f, " ")?;
            write!(f, "({} {})", &**name, value)?;
        }
        write!(f, ")")
    }
}

/// Given the serialized string representation of a Clarity value,
///  return the size of the same byte representation.
pub fn byte_len_of_serialization(serialized: &str) -> u64 {
    serialized.len() as u64 / 2
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_constructors() {
        assert_eq!(
            Value::list_with_type(
                &StacksEpochId::latest(),
                vec![Value::Int(5), Value::Int(2)],
                ListTypeData::new_list(TypeSignature::BoolType, 3).unwrap()
            ),
            Err(InterpreterError::FailureConstructingListWithType.into())
        );
        assert_eq!(
            ListTypeData::new_list(TypeSignature::IntType, MAX_VALUE_SIZE),
            Err(CheckErrors::ValueTooLarge)
        );

        assert_eq!(
            Value::buff_from(vec![0; (MAX_VALUE_SIZE + 1) as usize]),
            Err(CheckErrors::ValueTooLarge.into())
        );

        // Test that wrappers (okay, error, some)
        //   correctly error when _they_ cause the value size
        //   to exceed the max value size (note, the buffer constructor
        //   isn't causing the error).
        assert_eq!(
            Value::okay(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        assert_eq!(
            Value::error(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        assert_eq!(
            Value::some(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        // Test that the depth limit is correctly enforced:
        //   for tuples, lists, somes, okays, errors.

        let cons = || {
            Value::some(Value::some(Value::some(Value::some(Value::some(
                Value::some(Value::some(Value::some(Value::some(Value::some(
                    Value::some(Value::some(Value::some(Value::some(Value::some(
                        Value::some(Value::some(Value::some(Value::some(Value::some(
                            Value::some(Value::some(Value::some(Value::some(Value::some(
                                Value::some(Value::some(Value::some(Value::some(
                                    Value::some(Value::some(Value::Int(1))?)?,
                                )?)?)?)?,
                            )?)?)?)?)?,
                        )?)?)?)?)?,
                    )?)?)?)?)?,
                )?)?)?)?)?,
            )?)?)?)?)
        };
        let inner_value = cons().unwrap();
        assert_eq!(
            TupleData::from_data(vec![("a".into(), inner_value.clone())]),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );

        assert_eq!(
            Value::list_from(vec![inner_value.clone()]),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::okay(inner_value.clone()),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::error(inner_value.clone()),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::some(inner_value),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );

        if std::env::var("CIRCLE_TESTING") == Ok("1".to_string()) {
            println!("Skipping allocation test on Circle");
            return;
        }

        // on 32-bit archs, this error cannot even happen, so don't test (and cause an overflow panic)
        if (u32::MAX as usize) < usize::MAX {
            assert_eq!(
                Value::buff_from(vec![0; (u32::MAX as usize) + 10]),
                Err(CheckErrors::ValueTooLarge.into())
            );
        }
    }

    #[test]
    fn simple_size_test() {
        assert_eq!(Value::Int(10).size().unwrap(), 16);
    }

    #[test]
    fn simple_tuple_get_test() {
        let t = TupleData::from_data(vec![("abc".into(), Value::Int(0))]).unwrap();
        assert_eq!(t.get("abc"), Ok(&Value::Int(0)));
        // should error!
        t.get("abcd").unwrap_err();
    }

    #[test]
    fn test_some_displays() {
        assert_eq!(
            &format!(
                "{}",
                Value::list_from(vec![Value::Int(10), Value::Int(5)]).unwrap()
            ),
            "(10 5)"
        );
        assert_eq!(
            &format!("{}", Value::some(Value::Int(10)).unwrap()),
            "(some 10)"
        );
        assert_eq!(
            &format!("{}", Value::okay(Value::Int(10)).unwrap()),
            "(ok 10)"
        );
        assert_eq!(
            &format!("{}", Value::error(Value::Int(10)).unwrap()),
            "(err 10)"
        );
        assert_eq!(&format!("{}", Value::none()), "none");
        assert_eq!(
            &format!(
                "{}",
                Value::from(
                    PrincipalData::parse_standard_principal(
                        "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G"
                    )
                    .unwrap()
                )
            ),
            "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G"
        );

        assert_eq!(
            &format!(
                "{}",
                Value::from(TupleData::from_data(vec![("a".into(), Value::Int(2))]).unwrap())
            ),
            "(tuple (a 2))"
        );
    }

    #[test]
    fn expect_buff() {
        let buff = Value::Sequence(SequenceData::Buffer(BuffData {
            data: vec![1, 2, 3, 4, 5],
        }));
        assert_eq!(buff.clone().expect_buff(5).unwrap(), vec![1, 2, 3, 4, 5]);
        assert_eq!(buff.clone().expect_buff(6).unwrap(), vec![1, 2, 3, 4, 5]);
        assert_eq!(
            buff.clone().expect_buff_padded(6, 0).unwrap(),
            vec![1, 2, 3, 4, 5, 0]
        );
        assert_eq!(buff.clone().expect_buff(10).unwrap(), vec![1, 2, 3, 4, 5]);
        assert_eq!(
            buff.expect_buff_padded(10, 1).unwrap(),
            vec![1, 2, 3, 4, 5, 1, 1, 1, 1, 1]
        );
    }

    #[test]
    #[should_panic]
    fn expect_buff_too_small() {
        let buff = Value::Sequence(SequenceData::Buffer(BuffData {
            data: vec![1, 2, 3, 4, 5],
        }));
        let _ = buff.expect_buff(4).unwrap();
    }
}
