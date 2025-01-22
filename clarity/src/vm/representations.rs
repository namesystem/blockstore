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

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::io::{Read, Write};
use std::ops::Deref;

use lazy_static::lazy_static;
use regex::Regex;
use stacks_common::codec::{
    read_next, read_next_at_most, write_next, Error as codec_error, StacksMessageCodec,
};

use crate::vm::errors::RuntimeErrorType;
use crate::vm::types::{QualifiedContractIdentifier, TraitIdentifier, Value};

pub const CONTRACT_MIN_NAME_LENGTH: usize = 1;
pub const CONTRACT_MAX_NAME_LENGTH: usize = 40;
pub const MAX_STRING_LEN: u8 = 128;

lazy_static! {
    pub static ref STANDARD_PRINCIPAL_REGEX_STRING: String =
        "[0123456789ABCDEFGHJKMNPQRSTVWXYZ]{28,41}".into();
    pub static ref CONTRACT_NAME_REGEX_STRING: String = format!(
        r#"([a-zA-Z](([a-zA-Z0-9]|[-_])){{{},{}}})"#,
        CONTRACT_MIN_NAME_LENGTH - 1,
        // NOTE: this is deliberate.  Earlier versions of the node will accept contract principals whose names are up to
        // 128 bytes.  This behavior must be preserved for backwards-compatibility.
        MAX_STRING_LEN - 1
    );
    pub static ref CONTRACT_PRINCIPAL_REGEX_STRING: String = format!(
        r#"{}(\.){}"#,
        *STANDARD_PRINCIPAL_REGEX_STRING, *CONTRACT_NAME_REGEX_STRING
    );
    pub static ref PRINCIPAL_DATA_REGEX_STRING: String = format!(
        "({})|({})",
        *STANDARD_PRINCIPAL_REGEX_STRING, *CONTRACT_PRINCIPAL_REGEX_STRING
    );
    pub static ref CLARITY_NAME_REGEX_STRING: String =
        "^[a-zA-Z]([a-zA-Z0-9]|[-_!?+<>=/*])*$|^[-+=/*]$|^[<>]=?$".into();
    pub static ref CLARITY_NAME_REGEX: Regex =
    {
        #[allow(clippy::unwrap_used)]
        Regex::new(CLARITY_NAME_REGEX_STRING.as_str()).unwrap()
    };
    pub static ref CONTRACT_NAME_REGEX: Regex =
    {
        #[allow(clippy::unwrap_used)]
        Regex::new(format!("^{}$|^__transient$", CONTRACT_NAME_REGEX_STRING.as_str()).as_str())
            .unwrap()
    };
}

guarded_string!(
    ClarityName,
    "ClarityName",
    CLARITY_NAME_REGEX,
    MAX_STRING_LEN,
    RuntimeErrorType,
    RuntimeErrorType::BadNameValue
);
guarded_string!(
    ContractName,
    "ContractName",
    CONTRACT_NAME_REGEX,
    MAX_STRING_LEN,
    RuntimeErrorType,
    RuntimeErrorType::BadNameValue
);

impl StacksMessageCodec for ClarityName {
    #[allow(clippy::needless_as_bytes)] // as_bytes isn't necessary, but verbosity is preferable in the codec impls
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        // ClarityName can't be longer than vm::representations::MAX_STRING_LEN, which itself is
        // a u8, so we should be good here.
        if self.as_bytes().len() > MAX_STRING_LEN as usize {
            return Err(codec_error::SerializeError(
                "Failed to serialize clarity name: too long".to_string(),
            ));
        }
        write_next(fd, &(self.as_bytes().len() as u8))?;
        fd.write_all(self.as_bytes())
            .map_err(codec_error::WriteError)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<ClarityName, codec_error> {
        let len_byte: u8 = read_next(fd)?;
        if len_byte > MAX_STRING_LEN {
            return Err(codec_error::DeserializeError(
                "Failed to deserialize clarity name: too long".to_string(),
            ));
        }
        let mut bytes = vec![0u8; len_byte as usize];
        fd.read_exact(&mut bytes).map_err(codec_error::ReadError)?;

        // must encode a valid string
        let s = String::from_utf8(bytes).map_err(|_e| {
            codec_error::DeserializeError(
                "Failed to parse Clarity name: could not contruct from utf8".to_string(),
            )
        })?;

        // must decode to a clarity name
        let name = ClarityName::try_from(s).map_err(|e| {
            codec_error::DeserializeError(format!("Failed to parse Clarity name: {:?}", e))
        })?;
        Ok(name)
    }
}

impl StacksMessageCodec for ContractName {
    #[allow(clippy::needless_as_bytes)] // as_bytes isn't necessary, but verbosity is preferable in the codec impls
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        if self.as_bytes().len() < CONTRACT_MIN_NAME_LENGTH
            || self.as_bytes().len() > CONTRACT_MAX_NAME_LENGTH
        {
            return Err(codec_error::SerializeError(format!(
                "Failed to serialize contract name: too short or too long: {}",
                self.as_bytes().len()
            )));
        }
        write_next(fd, &(self.as_bytes().len() as u8))?;
        fd.write_all(self.as_bytes())
            .map_err(codec_error::WriteError)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<ContractName, codec_error> {
        let len_byte: u8 = read_next(fd)?;
        if (len_byte as usize) < CONTRACT_MIN_NAME_LENGTH
            || (len_byte as usize) > CONTRACT_MAX_NAME_LENGTH
        {
            return Err(codec_error::DeserializeError(format!(
                "Failed to deserialize contract name: too short or too long: {}",
                len_byte
            )));
        }
        let mut bytes = vec![0u8; len_byte as usize];
        fd.read_exact(&mut bytes).map_err(codec_error::ReadError)?;

        // must encode a valid string
        let s = String::from_utf8(bytes).map_err(|_e| {
            codec_error::DeserializeError(
                "Failed to parse Contract name: could not construct from utf8".to_string(),
            )
        })?;

        let name = ContractName::try_from(s).map_err(|e| {
            codec_error::DeserializeError(format!("Failed to parse Contract name: {:?}", e))
        })?;
        Ok(name)
    }
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub enum PreSymbolicExpressionType {
    AtomValue(Value),
    Atom(ClarityName),
    List(Vec<PreSymbolicExpression>),
    Tuple(Vec<PreSymbolicExpression>),
    SugaredContractIdentifier(ContractName),
    SugaredFieldIdentifier(ContractName, ClarityName),
    FieldIdentifier(TraitIdentifier),
    TraitReference(ClarityName),
    Comment(String),
    Placeholder(String),
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct PreSymbolicExpression {
    pub pre_expr: PreSymbolicExpressionType,
    pub id: u64,

    #[cfg(feature = "developer-mode")]
    pub span: Span,
}

pub trait SymbolicExpressionCommon {
    type S: SymbolicExpressionCommon;
    fn set_id(&mut self, id: u64);
    fn match_list_mut(&mut self) -> Option<&mut [Self::S]>;
}

impl SymbolicExpressionCommon for PreSymbolicExpression {
    type S = PreSymbolicExpression;
    fn set_id(&mut self, id: u64) {
        self.id = id;
    }
    fn match_list_mut(&mut self) -> Option<&mut [PreSymbolicExpression]> {
        if let PreSymbolicExpressionType::List(ref mut list) = self.pre_expr {
            Some(list)
        } else {
            None
        }
    }
}

impl SymbolicExpressionCommon for SymbolicExpression {
    type S = SymbolicExpression;
    fn set_id(&mut self, id: u64) {
        self.id = id;
    }
    fn match_list_mut(&mut self) -> Option<&mut [SymbolicExpression]> {
        if let SymbolicExpressionType::List(ref mut list) = self.expr {
            Some(list)
        } else {
            None
        }
    }
}

impl PreSymbolicExpression {
    #[cfg(feature = "developer-mode")]
    fn cons() -> PreSymbolicExpression {
        PreSymbolicExpression {
            id: 0,
            span: Span::zero(),
            pre_expr: PreSymbolicExpressionType::AtomValue(Value::Bool(false)),
        }
    }
    #[cfg(not(feature = "developer-mode"))]
    fn cons() -> PreSymbolicExpression {
        PreSymbolicExpression {
            id: 0,
            pre_expr: PreSymbolicExpressionType::AtomValue(Value::Bool(false)),
        }
    }

    #[cfg(feature = "developer-mode")]
    pub fn set_span(&mut self, start_line: u32, start_column: u32, end_line: u32, end_column: u32) {
        self.span = Span {
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn set_span(
        &mut self,
        _start_line: u32,
        _start_column: u32,
        _end_line: u32,
        _end_column: u32,
    ) {
    }

    #[cfg(feature = "developer-mode")]
    pub fn copy_span(&mut self, src: &Span) {
        self.span = src.clone();
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn copy_span(&mut self, _src: &Span) {}

    #[cfg(feature = "developer-mode")]
    pub fn span(&self) -> &Span {
        &self.span
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn span(&self) -> &Span {
        &Span::ZERO
    }

    pub fn sugared_contract_identifier(val: ContractName) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::SugaredContractIdentifier(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn sugared_field_identifier(
        contract_name: ContractName,
        name: ClarityName,
    ) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::SugaredFieldIdentifier(contract_name, name),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn atom_value(val: Value) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::AtomValue(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn atom(val: ClarityName) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::Atom(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn trait_reference(val: ClarityName) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::TraitReference(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn field_identifier(val: TraitIdentifier) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::FieldIdentifier(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn list(val: Vec<PreSymbolicExpression>) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::List(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn tuple(val: Vec<PreSymbolicExpression>) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::Tuple(val),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn placeholder(s: String) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::Placeholder(s),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn comment(comment: String) -> PreSymbolicExpression {
        PreSymbolicExpression {
            pre_expr: PreSymbolicExpressionType::Comment(comment),
            ..PreSymbolicExpression::cons()
        }
    }

    pub fn match_trait_reference(&self) -> Option<&ClarityName> {
        if let PreSymbolicExpressionType::TraitReference(ref value) = self.pre_expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_atom_value(&self) -> Option<&Value> {
        if let PreSymbolicExpressionType::AtomValue(ref value) = self.pre_expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_atom(&self) -> Option<&ClarityName> {
        if let PreSymbolicExpressionType::Atom(ref value) = self.pre_expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_list(&self) -> Option<&[PreSymbolicExpression]> {
        if let PreSymbolicExpressionType::List(ref list) = self.pre_expr {
            Some(list)
        } else {
            None
        }
    }

    pub fn match_field_identifier(&self) -> Option<&TraitIdentifier> {
        if let PreSymbolicExpressionType::FieldIdentifier(ref value) = self.pre_expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_placeholder(&self) -> Option<&str> {
        if let PreSymbolicExpressionType::Placeholder(ref s) = self.pre_expr {
            Some(s.as_str())
        } else {
            None
        }
    }

    pub fn match_comment(&self) -> Option<&str> {
        if let PreSymbolicExpressionType::Comment(ref s) = self.pre_expr {
            Some(s.as_str())
        } else {
            None
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub enum SymbolicExpressionType {
    AtomValue(Value),
    Atom(ClarityName),
    List(Vec<SymbolicExpression>),
    LiteralValue(Value),
    Field(TraitIdentifier),
    TraitReference(ClarityName, TraitDefinition),
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub enum TraitDefinition {
    Defined(TraitIdentifier),
    Imported(TraitIdentifier),
}

pub fn depth_traverse<F, T, E>(expr: &SymbolicExpression, mut visit: F) -> Result<Option<T>, E>
where
    F: FnMut(&SymbolicExpression) -> Result<T, E>,
{
    let mut stack = vec![];
    let mut last = None;
    stack.push(expr);
    while let Some(current) = stack.pop() {
        last = Some(visit(current)?);
        if let Some(list) = current.match_list() {
            for item in list.iter() {
                stack.push(item);
            }
        }
    }

    Ok(last)
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct SymbolicExpression {
    pub expr: SymbolicExpressionType,
    // this id field is used by compiler passes to store information in
    //  maps.
    // first pass       -> fill out unique ids
    // ...typing passes -> store information in hashmap according to id.
    //
    // this is a fairly standard technique in compiler passes
    pub id: u64,

    #[cfg(feature = "developer-mode")]
    #[serde(default)]
    pub span: Span,

    #[cfg(feature = "developer-mode")]
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub pre_comments: Vec<(String, Span)>,
    #[cfg(feature = "developer-mode")]
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_line_comment: Option<String>,
    #[cfg(feature = "developer-mode")]
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub post_comments: Vec<(String, Span)>,
}

impl SymbolicExpression {
    #[cfg(feature = "developer-mode")]
    fn cons() -> SymbolicExpression {
        SymbolicExpression {
            id: 0,
            expr: SymbolicExpressionType::AtomValue(Value::Bool(false)),
            span: Span::zero(),
            pre_comments: vec![],
            end_line_comment: None,
            post_comments: vec![],
        }
    }
    #[cfg(not(feature = "developer-mode"))]
    fn cons() -> SymbolicExpression {
        SymbolicExpression {
            id: 0,
            expr: SymbolicExpressionType::AtomValue(Value::Bool(false)),
        }
    }

    #[cfg(feature = "developer-mode")]
    pub fn set_span(&mut self, start_line: u32, start_column: u32, end_line: u32, end_column: u32) {
        self.span = Span {
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn set_span(
        &mut self,
        _start_line: u32,
        _start_column: u32,
        _end_line: u32,
        _end_column: u32,
    ) {
    }

    #[cfg(feature = "developer-mode")]
    pub fn copy_span(&mut self, src: &Span) {
        self.span = src.clone();
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn copy_span(&mut self, _src: &Span) {}

    #[cfg(feature = "developer-mode")]
    pub fn span(&self) -> &Span {
        &self.span
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn span(&self) -> &Span {
        &Span::ZERO
    }

    pub fn atom_value(val: Value) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::AtomValue(val),
            ..SymbolicExpression::cons()
        }
    }

    pub fn atom(val: ClarityName) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::Atom(val),
            ..SymbolicExpression::cons()
        }
    }

    pub fn literal_value(val: Value) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::LiteralValue(val),
            ..SymbolicExpression::cons()
        }
    }

    pub fn list(val: Vec<SymbolicExpression>) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::List(val),
            ..SymbolicExpression::cons()
        }
    }

    pub fn trait_reference(
        val: ClarityName,
        trait_definition: TraitDefinition,
    ) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::TraitReference(val, trait_definition),
            ..SymbolicExpression::cons()
        }
    }

    pub fn field(val: TraitIdentifier) -> SymbolicExpression {
        SymbolicExpression {
            expr: SymbolicExpressionType::Field(val),
            ..SymbolicExpression::cons()
        }
    }

    // These match functions are used to simplify calling code
    //   areas a lot. There is a frequent code pattern where
    //   a block _expects_ specific symbolic expressions, leading
    //   to a lot of very verbose `if let x = {` expressions.

    pub fn match_list(&self) -> Option<&[SymbolicExpression]> {
        if let SymbolicExpressionType::List(ref list) = self.expr {
            Some(list)
        } else {
            None
        }
    }

    pub fn match_atom(&self) -> Option<&ClarityName> {
        if let SymbolicExpressionType::Atom(ref value) = self.expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_atom_value(&self) -> Option<&Value> {
        if let SymbolicExpressionType::AtomValue(ref value) = self.expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_literal_value(&self) -> Option<&Value> {
        if let SymbolicExpressionType::LiteralValue(ref value) = self.expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_trait_reference(&self) -> Option<&ClarityName> {
        if let SymbolicExpressionType::TraitReference(ref value, _) = self.expr {
            Some(value)
        } else {
            None
        }
    }

    pub fn match_field(&self) -> Option<&TraitIdentifier> {
        if let SymbolicExpressionType::Field(ref value) = self.expr {
            Some(value)
        } else {
            None
        }
    }
}

impl fmt::Display for SymbolicExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr {
            SymbolicExpressionType::List(ref list) => {
                write!(f, "(")?;
                for item in list.iter() {
                    write!(f, " {}", item)?;
                }
                write!(f, " )")?;
            }
            SymbolicExpressionType::Atom(ref value) => {
                write!(f, "{}", &**value)?;
            }
            SymbolicExpressionType::AtomValue(ref value)
            | SymbolicExpressionType::LiteralValue(ref value) => {
                write!(f, "{}", value)?;
            }
            SymbolicExpressionType::TraitReference(ref value, _) => {
                write!(f, "<{}>", &**value)?;
            }
            SymbolicExpressionType::Field(ref value) => {
                write!(f, "<{}>", value)?;
            }
        };

        Ok(())
    }
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Span {
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
}

impl Span {
    pub const ZERO: Span = Span {
        start_line: 0,
        start_column: 0,
        end_line: 0,
        end_column: 0,
    };

    pub fn zero() -> Span {
        Span {
            start_line: 0,
            start_column: 0,
            end_line: 0,
            end_column: 0,
        }
    }
}
