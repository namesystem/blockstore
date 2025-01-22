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

use std::error::Error as ErrorTrait;
use std::string::FromUtf8Error;
use std::{error, fmt};

#[cfg(feature = "canonical")]
use rusqlite::Error as SqliteError;
use serde_json::Error as SerdeJSONErr;
use stacks_common::types::chainstate::BlockHeaderHash;

use super::ast::errors::ParseErrors;
pub use crate::vm::analysis::errors::{
    check_argument_count, check_arguments_at_least, check_arguments_at_most, CheckErrors,
};
use crate::vm::ast::errors::ParseError;
use crate::vm::contexts::StackTrace;
use crate::vm::costs::CostErrors;
use crate::vm::types::Value;

#[derive(Debug)]
pub struct IncomparableError<T> {
    pub err: T,
}

#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
pub enum Error {
    /// UncheckedErrors are errors that *should* be caught by the
    ///   TypeChecker and other check passes. Test executions may
    ///   trigger these errors.
    Unchecked(CheckErrors),
    Interpreter(InterpreterError),
    Runtime(RuntimeErrorType, Option<StackTrace>),
    ShortReturn(ShortReturnType),
    #[cfg(feature = "clarity-wasm")]
    Wasm(WasmError),
}

/// InterpreterErrors are errors that *should never* occur.
/// Test executions may trigger these errors.
#[derive(Debug, PartialEq)]
pub enum InterpreterError {
    BadSender(Value),
    BadSymbolicRepresentation(String),
    InterpreterError(String),
    UninitializedPersistedVariable,
    FailedToConstructAssetTable,
    FailedToConstructEventBatch,
    #[cfg(feature = "canonical")]
    SqliteError(IncomparableError<SqliteError>),
    BadFileName,
    FailedToCreateDataDirectory,
    MarfFailure(String),
    FailureConstructingTupleWithType,
    FailureConstructingListWithType,
    InsufficientBalance,
    CostContractLoadFailure,
    DBError(String),
    Expect(String),
}

/// RuntimeErrors are errors that smart contracts are expected
///   to be able to trigger during execution (e.g., arithmetic errors)
#[derive(Debug, PartialEq)]
pub enum RuntimeErrorType {
    Arithmetic(String),
    ArithmeticOverflow,
    ArithmeticUnderflow,
    SupplyOverflow(u128, u128),
    SupplyUnderflow(u128, u128),
    DivisionByZero,
    // error in parsing types
    ParseError(String),
    // error in parsing the AST
    ASTError(ParseError),
    MaxStackDepthReached,
    MaxContextDepthReached,
    ListDimensionTooHigh,
    BadTypeConstruction,
    ValueTooLarge,
    BadBlockHeight(String),
    TransferNonPositiveAmount,
    NoSuchToken,
    NotImplemented,
    NoCallerInContext,
    NoSenderInContext,
    NonPositiveTokenSupply,
    JSONParseError(IncomparableError<SerdeJSONErr>),
    AttemptToFetchInTransientContext,
    BadNameValue(&'static str, String),
    UnknownBlockHeaderHash(BlockHeaderHash),
    BadBlockHash(Vec<u8>),
    UnwrapFailure,
    DefunctPoxContract,
    PoxAlreadyLocked,
    MetadataAlreadySet,
}

#[derive(Debug, PartialEq)]
pub enum ShortReturnType {
    ExpectedValue(Value),
    AssertionFailed(Value),
}

/// WasmErrors are errors that *should never* occur.
/// Test executions may trigger these errors, but if they show up in normal
/// execution, it indicates a bug in the Wasm compiler or runtime.
#[cfg(feature = "clarity-wasm")]
#[derive(Debug)]
pub enum WasmError {
    WasmGeneratorError(String),
    ModuleNotFound,
    DefinesNotFound,
    TopLevelNotFound,
    MemoryNotFound,
    GlobalNotFound(String),
    WasmCompileFailed(wasmtime::Error),
    UnableToLoadModule(wasmtime::Error),
    UnableToLinkHostFunction(String, wasmtime::Error),
    UnableToReadIdentifier(FromUtf8Error),
    UnableToRetrieveIdentifier(i32),
    InvalidClarityName(String),
    UnableToWriteStackPointer(wasmtime::Error),
    UnableToReadMemory(wasmtime::Error),
    UnableToWriteMemory(wasmtime::Error),
    ValueTypeMismatch,
    InvalidNoTypeInValue,
    InvalidListUnionTypeInValue,
    InvalidFunctionKind(i32),
    DefineFunctionCalledInRunMode,
    ExpectedReturnValue,
    InvalidIndicator(i32),
    Runtime(wasmtime::Error),
}

#[cfg(feature = "clarity-wasm")]
impl fmt::Display for WasmError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WasmError::WasmGeneratorError(e) => write!(f, "Wasm generator error: {e}"),
            WasmError::ModuleNotFound => write!(f, "Module not found"),
            WasmError::DefinesNotFound => write!(f, "Defines function not found"),
            WasmError::TopLevelNotFound => write!(f, "Top level function not found"),
            WasmError::MemoryNotFound => write!(f, "Memory not found"),
            WasmError::GlobalNotFound(e) => write!(f, "Global variable not found: {e}"),
            WasmError::WasmCompileFailed(e) => write!(f, "Wasm compile failed: {e}"),
            WasmError::UnableToLoadModule(e) => write!(f, "Unable to load module: {e}"),
            WasmError::UnableToLinkHostFunction(name, e) => {
                write!(f, "Unable to link host function {name}: {e}")
            }
            WasmError::UnableToReadIdentifier(e) => write!(f, "Unable to read identifier: {e}"),
            WasmError::UnableToRetrieveIdentifier(id) => {
                write!(f, "Unable to retrieve identifier: {id}")
            }
            WasmError::InvalidClarityName(name) => write!(f, "Invalid Clarity name: {name}"),
            WasmError::UnableToWriteStackPointer(e) => {
                write!(f, "Unable to write stack pointer: {e}")
            }
            WasmError::UnableToReadMemory(e) => write!(f, "Unable to read memory: {e}"),
            WasmError::UnableToWriteMemory(e) => write!(f, "Unable to write memory: {e}"),
            WasmError::ValueTypeMismatch => write!(f, "Value type mismatch"),
            WasmError::InvalidNoTypeInValue => write!(f, "Invalid no type in value"),
            WasmError::InvalidListUnionTypeInValue => write!(f, "Invalid list union type in value"),
            WasmError::InvalidFunctionKind(kind) => write!(f, "Invalid function kind: {kind}"),
            WasmError::DefineFunctionCalledInRunMode => {
                write!(f, "Define function called in run mode")
            }
            WasmError::ExpectedReturnValue => write!(f, "Expected return value"),
            WasmError::InvalidIndicator(indicator) => {
                write!(f, "Invalid response/optional indicator: {indicator}")
            }
            WasmError::Runtime(e) => write!(f, "Runtime error: {e}"),
        }
    }
}

#[cfg(feature = "clarity-wasm")]
impl std::error::Error for WasmError {}

pub type InterpreterResult<R> = Result<R, Error>;

impl<T> PartialEq<IncomparableError<T>> for IncomparableError<T> {
    fn eq(&self, _other: &IncomparableError<T>) -> bool {
        false
    }
}

impl PartialEq<Error> for Error {
    fn eq(&self, other: &Error) -> bool {
        match (self, other) {
            (Error::Runtime(x, _), Error::Runtime(y, _)) => x == y,
            (Error::Unchecked(x), Error::Unchecked(y)) => x == y,
            (Error::ShortReturn(x), Error::ShortReturn(y)) => x == y,
            (Error::Interpreter(x), Error::Interpreter(y)) => x == y,
            _ => false,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Runtime(ref err, ref stack) => {
                write!(f, "{err}")?;
                if let Some(ref stack_trace) = stack {
                    writeln!(f, "\n Stack Trace: ")?;
                    for item in stack_trace.iter() {
                        writeln!(f, "{item}")?;
                    }
                }
                Ok(())
            }
            _ => write!(f, "{self:?}"),
        }
    }
}

impl fmt::Display for RuntimeErrorType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl error::Error for RuntimeErrorType {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Self {
        match &err.err {
            ParseErrors::InterpreterFailure => Error::from(InterpreterError::Expect(
                "Unexpected interpreter failure during parsing".into(),
            )),
            _ => Error::from(RuntimeErrorType::ASTError(err)),
        }
    }
}

impl From<CostErrors> for Error {
    fn from(err: CostErrors) -> Self {
        match err {
            CostErrors::InterpreterFailure => Error::from(InterpreterError::Expect(
                "Interpreter failure during cost calculation".into(),
            )),
            CostErrors::Expect(s) => Error::from(InterpreterError::Expect(format!(
                "Interpreter failure during cost calculation: {s}"
            ))),
            other_err => Error::from(CheckErrors::from(other_err)),
        }
    }
}

impl From<RuntimeErrorType> for Error {
    fn from(err: RuntimeErrorType) -> Self {
        Error::Runtime(err, None)
    }
}

impl From<CheckErrors> for Error {
    fn from(err: CheckErrors) -> Self {
        Error::Unchecked(err)
    }
}

impl From<ShortReturnType> for Error {
    fn from(err: ShortReturnType) -> Self {
        Error::ShortReturn(err)
    }
}

impl From<InterpreterError> for Error {
    fn from(err: InterpreterError) -> Self {
        Error::Interpreter(err)
    }
}

#[cfg(test)]
impl From<Error> for () {
    fn from(err: Error) -> Self {}
}

impl From<ShortReturnType> for Value {
    fn from(val: ShortReturnType) -> Self {
        match val {
            ShortReturnType::ExpectedValue(v) => v,
            ShortReturnType::AssertionFailed(v) => v,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::vm::execute;

    #[test]
    #[cfg(feature = "developer-mode")]
    fn error_formats() {
        let t = "(/ 10 0)";
        let expected = "DivisionByZero
 Stack Trace:
_native_:native_div
";

        assert_eq!(format!("{}", execute(t).unwrap_err()), expected);
    }

    #[test]
    fn equality() {
        assert_eq!(
            Error::ShortReturn(ShortReturnType::ExpectedValue(Value::Bool(true))),
            Error::ShortReturn(ShortReturnType::ExpectedValue(Value::Bool(true)))
        );
        assert_eq!(
            Error::Interpreter(InterpreterError::InterpreterError("".to_string())),
            Error::Interpreter(InterpreterError::InterpreterError("".to_string()))
        );
        assert!(
            Error::ShortReturn(ShortReturnType::ExpectedValue(Value::Bool(true)))
                != Error::Interpreter(InterpreterError::InterpreterError("".to_string()))
        );
    }
}
