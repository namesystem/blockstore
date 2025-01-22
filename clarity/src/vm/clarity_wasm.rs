use std::borrow::BorrowMut;
use std::collections::{BTreeMap, HashMap};
use std::f32::EPSILON;
use std::fs::File;
use std::io::Write;

use stacks_common::types::chainstate::StacksBlockId;
use stacks_common::types::StacksEpochId;
use stacks_common::util::hash::{Keccak256Hash, Sha512Sum, Sha512Trunc256Sum};
use stacks_common::util::secp256k1::{secp256k1_recover, secp256k1_verify, Secp256k1PublicKey};
use wasmtime::{AsContextMut, Caller, Engine, Linker, Memory, Module, Store, Trap, Val, ValType};

use super::analysis::{CheckError, CheckErrors};
use super::ast::{build_ast_with_rules, ASTRules};
use super::callables::{DefineType, DefinedFunction};
use super::contracts::Contract;
use super::costs::{constants as cost_constants, CostTracker, LimitedCostTracker};
use super::database::clarity_db::ValueResult;
use super::database::{ClarityDatabase, DataVariableMetadata, STXBalance};
use super::errors::RuntimeErrorType;
use super::events::*;
use super::functions::crypto::{pubkey_to_address_v1, pubkey_to_address_v2};
use super::types::signatures::CallableSubtype;
use super::types::{
    ASCIIData, AssetIdentifier, BlockInfoProperty, BuffData, BurnBlockInfoProperty, CallableData,
    CharType, FixedFunction, FunctionType, ListData, ListTypeData, OptionalData, PrincipalData,
    QualifiedContractIdentifier, ResponseData, SequenceData, StacksAddressExtensions,
    StandardPrincipalData, TraitIdentifier, TupleData, TupleTypeSignature, UTF8Data, BUFF_1,
    BUFF_32, BUFF_33,
};
use super::{CallStack, ClarityVersion, ContractName, Environment, SymbolicExpression};
use crate::vm::analysis::ContractAnalysis;
use crate::vm::ast::ContractAST;
use crate::vm::contexts::GlobalContext;
use crate::vm::errors::{Error, WasmError};
use crate::vm::functions::principals;
use crate::vm::types::{
    BufferLength, SequenceSubtype, SequencedValue, StringSubtype, TypeSignature,
};
use crate::vm::{ClarityName, ContractContext, Value};

enum MintAssetErrorCodes {
    ALREADY_EXIST = 1,
}
enum MintTokenErrorCodes {
    NON_POSITIVE_AMOUNT = 1,
}
enum TransferAssetErrorCodes {
    NOT_OWNED_BY = 1,
    SENDER_IS_RECIPIENT = 2,
    DOES_NOT_EXIST = 3,
}
enum TransferTokenErrorCodes {
    NOT_ENOUGH_BALANCE = 1,
    SENDER_IS_RECIPIENT = 2,
    NON_POSITIVE_AMOUNT = 3,
}

enum BurnAssetErrorCodes {
    NOT_OWNED_BY = 1,
    DOES_NOT_EXIST = 3,
}
enum BurnTokenErrorCodes {
    NOT_ENOUGH_BALANCE_OR_NON_POSITIVE = 1,
}

enum StxErrorCodes {
    NOT_ENOUGH_BALANCE = 1,
    SENDER_IS_RECIPIENT = 2,
    NON_POSITIVE_AMOUNT = 3,
    SENDER_IS_NOT_TX_SENDER = 4,
}

/// The context used when making calls into the Wasm module.
pub struct ClarityWasmContext<'a, 'b> {
    pub global_context: &'a mut GlobalContext<'b>,
    contract_context: Option<&'a ContractContext>,
    contract_context_mut: Option<&'a mut ContractContext>,
    pub call_stack: &'a mut CallStack,
    pub sender: Option<PrincipalData>,
    pub caller: Option<PrincipalData>,
    pub sponsor: Option<PrincipalData>,
    // Stack of senders, used for `as-contract` expressions.
    sender_stack: Vec<PrincipalData>,
    /// Stack of callers, used for `contract-call?` and `as-contract` expressions.
    caller_stack: Vec<PrincipalData>,
    /// Stack of block hashes, used for `at-block` expressions.
    bhh_stack: Vec<StacksBlockId>,

    /// Contract analysis data, used for typing information, and only available
    /// when initializing a contract. Should always be `Some` when initializing
    /// a contract, and `None` otherwise.
    pub contract_analysis: Option<&'a ContractAnalysis>,
}

impl<'a, 'b> ClarityWasmContext<'a, 'b> {
    pub fn new_init(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a mut ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
        sponsor: Option<PrincipalData>,
        contract_analysis: Option<&'a ContractAnalysis>,
    ) -> Self {
        ClarityWasmContext {
            global_context,
            contract_context: None,
            contract_context_mut: Some(contract_context),
            call_stack,
            sender,
            caller,
            sponsor,
            sender_stack: vec![],
            caller_stack: vec![],
            bhh_stack: vec![],
            contract_analysis,
        }
    }

    pub fn new_run(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
        sponsor: Option<PrincipalData>,
        contract_analysis: Option<&'a ContractAnalysis>,
    ) -> Self {
        ClarityWasmContext {
            global_context,
            contract_context: Some(contract_context),
            contract_context_mut: None,
            call_stack,
            sender,
            caller,
            sponsor,
            sender_stack: vec![],
            caller_stack: vec![],
            bhh_stack: vec![],
            contract_analysis,
        }
    }

    fn push_sender(&mut self, sender: PrincipalData) {
        if let Some(current) = self.sender.take() {
            self.sender_stack.push(current);
        }
        self.sender = Some(sender);
    }

    fn pop_sender(&mut self) -> Result<PrincipalData, Error> {
        self.sender
            .take()
            .ok_or(RuntimeErrorType::NoSenderInContext.into())
            .inspect(|_| {
                self.sender = self.sender_stack.pop();
            })
    }

    fn push_caller(&mut self, caller: PrincipalData) {
        if let Some(current) = self.caller.take() {
            self.caller_stack.push(current);
        }
        self.caller = Some(caller);
    }

    fn pop_caller(&mut self) -> Result<PrincipalData, Error> {
        self.caller
            .take()
            .ok_or(RuntimeErrorType::NoCallerInContext.into())
            .inspect(|_| {
                self.caller = self.caller_stack.pop();
            })
    }

    fn push_at_block(&mut self, bhh: StacksBlockId) {
        self.bhh_stack.push(bhh);
    }

    fn pop_at_block(&mut self) -> Result<StacksBlockId, Error> {
        self.bhh_stack
            .pop()
            .ok_or(Error::Wasm(WasmError::WasmGeneratorError(
                "Could not pop at_block".to_string(),
            )))
    }

    /// Return an immutable reference to the contract_context
    pub fn contract_context(&self) -> &ContractContext {
        if let Some(contract_context) = &self.contract_context {
            contract_context
        } else if let Some(contract_context) = &self.contract_context_mut {
            contract_context
        } else {
            unreachable!("contract_context and contract_context_mut are both None")
        }
    }

    /// Return a mutable reference to the contract_context if we are currently
    /// initializing a contract, else, return an error.
    pub fn contract_context_mut(&mut self) -> Result<&mut ContractContext, Error> {
        match &mut self.contract_context_mut {
            Some(contract_context) => Ok(contract_context),
            None => Err(Error::Wasm(WasmError::DefineFunctionCalledInRunMode)),
        }
    }

    pub fn push_to_event_batch(&mut self, event: StacksTransactionEvent) {
        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(event);
        }
    }

    pub fn construct_print_transaction_event(
        contract_id: &QualifiedContractIdentifier,
        value: &Value,
    ) -> StacksTransactionEvent {
        let print_event = SmartContractEventData {
            key: (contract_id.clone(), "print".to_string()),
            value: value.clone(),
        };

        StacksTransactionEvent::SmartContractEvent(print_event)
    }

    pub fn register_print_event(&mut self, value: Value) -> Result<(), Error> {
        let event = Self::construct_print_transaction_event(
            &self.contract_context().contract_identifier,
            &value,
        );

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_stx_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
        memo: BuffData,
    ) -> Result<(), Error> {
        let event_data = STXTransferEventData {
            sender,
            recipient,
            amount,
            memo,
        };
        let event = StacksTransactionEvent::STXEvent(STXEventType::STXTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_stx_burn_event(
        &mut self,
        sender: PrincipalData,
        amount: u128,
    ) -> Result<(), Error> {
        let event_data = STXBurnEventData { sender, amount };
        let event = StacksTransactionEvent::STXEvent(STXEventType::STXBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = NFTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_mint_event(
        &mut self,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = NFTMintEventData {
            recipient,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTMintEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_nft_burn_event(
        &mut self,
        sender: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = NFTBurnEventData {
            sender,
            asset_identifier,
            value,
        };
        let event = StacksTransactionEvent::NFTEvent(NFTEventType::NFTBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = FTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTTransferEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_mint_event(
        &mut self,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = FTMintEventData {
            recipient,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTMintEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }

    pub fn register_ft_burn_event(
        &mut self,
        sender: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<(), Error> {
        let event_data = FTBurnEventData {
            sender,
            asset_identifier,
            amount,
        };
        let event = StacksTransactionEvent::FTEvent(FTEventType::FTBurnEvent(event_data));

        self.push_to_event_batch(event);
        Ok(())
    }
}

/// Push a placeholder value for Wasm type `ty` onto the data stack.
fn placeholder_for_type(ty: ValType) -> Val {
    match ty {
        ValType::I32 => Val::I32(0),
        ValType::I64 => Val::I64(0),
        ValType::F32 => Val::F32(0),
        ValType::F64 => Val::F64(0),
        ValType::V128 => Val::V128(0.into()),
        ValType::ExternRef => Val::ExternRef(None),
        ValType::FuncRef => Val::FuncRef(None),
    }
}

/// Initialize a contract, executing all of the top-level expressions and
/// registering all of the definitions in the context. Returns the value
/// returned from the last top-level expression.
pub fn initialize_contract(
    global_context: &mut GlobalContext,
    contract_context: &mut ContractContext,
    sponsor: Option<PrincipalData>,
    contract_analysis: &ContractAnalysis,
) -> Result<Option<Value>, Error> {
    let publisher: PrincipalData = contract_context.contract_identifier.issuer.clone().into();

    let mut call_stack = CallStack::new();
    let epoch = global_context.epoch_id;
    let clarity_version = *contract_context.get_clarity_version();
    let engine = global_context.engine.clone();
    let init_context = ClarityWasmContext::new_init(
        global_context,
        contract_context,
        &mut call_stack,
        Some(publisher.clone()),
        Some(publisher),
        sponsor.clone(),
        Some(contract_analysis),
    );
    let module = init_context
        .contract_context()
        .with_wasm_module(|wasm_module| {
            Module::from_binary(&engine, wasm_module)
                .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, init_context);
    let mut linker = Linker::new(&engine);

    // Link in the host interface functions.
    link_host_functions(&mut linker)?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Call the `.top-level` function, which contains all top-level expressions
    // from the contract.
    let top_level = instance
        .get_func(&mut store, ".top-level")
        .ok_or(Error::Wasm(WasmError::DefinesNotFound))?;

    // Get the return type of the top-level expressions function
    let ty = top_level.ty(&mut store);
    let results_iter = ty.results();
    let mut results = vec![];
    for result_ty in results_iter {
        results.push(placeholder_for_type(result_ty));
    }

    top_level
        .call(&mut store, &[], results.as_mut_slice())
        .map_err(|e| {
            error_mapping::resolve_error(e, instance, &mut store, &epoch, &clarity_version)
        })?;

    // Save the compiled Wasm module into the contract context
    store.data_mut().contract_context_mut()?.set_wasm_module(
        module
            .serialize()
            .map_err(|e| Error::Wasm(WasmError::WasmCompileFailed(e)))?,
    );

    // Get the type of the last top-level expression with a return value
    // or default to `None`.
    let return_type = contract_analysis.expressions.iter().rev().find_map(|expr| {
        contract_analysis
            .type_map
            .as_ref()
            .and_then(|type_map| type_map.get_type_expected(expr))
    });

    if let Some(return_type) = return_type {
        let memory = instance
            .get_memory(&mut store, "memory")
            .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
        wasm_to_clarity_value(return_type, 0, &results, memory, &mut &mut store, epoch)
            .map(|(val, _offset)| val)
    } else {
        Ok(None)
    }
}

/// Call a function in the contract.
pub fn call_function<'a>(
    function_name: &str,
    args: &[Value],
    global_context: &'a mut GlobalContext,
    contract_context: &'a ContractContext,
    call_stack: &'a mut CallStack,
    sender: Option<PrincipalData>,
    caller: Option<PrincipalData>,
    sponsor: Option<PrincipalData>,
) -> Result<Value, Error> {
    let epoch = global_context.epoch_id;
    let clarity_version = *contract_context.get_clarity_version();
    let engine = global_context.engine.clone();
    let context = ClarityWasmContext::new_run(
        global_context,
        contract_context,
        call_stack,
        sender,
        caller,
        sponsor,
        None,
    );

    let func_types = context
        .contract_context()
        .lookup_function(function_name)
        .ok_or(CheckErrors::UndefinedFunction(function_name.to_string()))?;
    let module = context
        .contract_context()
        .with_wasm_module(|wasm_module| unsafe {
            Module::deserialize(&engine, wasm_module)
                .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))
        })?;
    let mut store = Store::new(&engine, context);
    let mut linker = Linker::new(&engine);

    // Link in the host interface functions.
    link_host_functions(&mut linker)?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| Error::Wasm(WasmError::UnableToLoadModule(e)))?;

    // Call the specified function
    let func = instance
        .get_func(&mut store, function_name)
        .ok_or(CheckErrors::UndefinedFunction(function_name.to_string()))?;

    // Access the global stack pointer from the instance
    let stack_pointer = instance
        .get_global(&mut store, "stack-pointer")
        .ok_or(Error::Wasm(WasmError::GlobalNotFound(
            "stack-pointer".to_string(),
        )))?;
    let mut offset = stack_pointer
        .get(&mut store)
        .i32()
        .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;

    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

    // Determine how much space is needed for arguments
    let mut arg_size = 0;
    for arg in func_types.get_arg_types() {
        arg_size += get_type_in_memory_size(arg, false);
    }
    let mut in_mem_offset = offset + arg_size;

    // Convert the args into wasmtime values
    let mut wasm_args = vec![];
    for (arg, ty) in args.iter().zip(func_types.get_arg_types()) {
        let (arg_vec, new_offset, new_in_mem_offset) =
            pass_argument_to_wasm(memory, &mut store, ty, arg, offset, in_mem_offset)?;
        wasm_args.extend(arg_vec);
        offset = new_offset;
        in_mem_offset = new_in_mem_offset;
    }

    // Reserve stack space for the return value, if necessary.
    let return_type = func_types
        .get_return_type()
        .as_ref()
        .ok_or(Error::Wasm(WasmError::ExpectedReturnValue))?
        .clone();
    let (mut results, offset) = reserve_space_for_return(offset, &return_type)?;

    // Update the stack pointer after space is reserved for the arguments and
    // return values.
    stack_pointer
        .set(&mut store, Val::I32(offset))
        .map_err(|e| Error::Wasm(WasmError::Runtime(e)))?;

    // Call the function
    func.call(&mut store, &wasm_args, &mut results)
        .map_err(|e| {
            error_mapping::resolve_error(e, instance, &mut store, &epoch, &clarity_version)
        })?;

    // If the function returns a value, translate it into a Clarity `Value`
    wasm_to_clarity_value(&return_type, 0, &results, memory, &mut &mut store, epoch)
        .map(|(val, _offset)| val)
        .and_then(|option_value| {
            option_value.ok_or_else(|| Error::Wasm(WasmError::ExpectedReturnValue))
        })
}

// Bytes for principal version
pub const PRINCIPAL_VERSION_BYTES: usize = 1;
// Number of bytes in principal hash
pub const PRINCIPAL_HASH_BYTES: usize = 20;
// Standard principal version + hash
pub const PRINCIPAL_BYTES: usize = PRINCIPAL_VERSION_BYTES + PRINCIPAL_HASH_BYTES;
// Number of bytes used to store the length of the contract name
pub const CONTRACT_NAME_LENGTH_BYTES: usize = 1;
// 1 byte for version, 20 bytes for hash, 4 bytes for contract name length (0)
pub const STANDARD_PRINCIPAL_BYTES: usize = PRINCIPAL_BYTES + CONTRACT_NAME_LENGTH_BYTES;
// Max length of a contract name
pub const CONTRACT_NAME_MAX_LENGTH: usize = 128;
// Standard principal, but at most 128 character function name
pub const PRINCIPAL_BYTES_MAX: usize = STANDARD_PRINCIPAL_BYTES + CONTRACT_NAME_MAX_LENGTH;

/// Return the number of bytes required to representation of a value of the
/// type `ty`. For in-memory types, this is just the size of the offset and
/// length. For non-in-memory types, this is the size of the value itself.
pub fn get_type_size(ty: &TypeSignature) -> i32 {
    match ty {
        TypeSignature::IntType | TypeSignature::UIntType => 16, // low: i64, high: i64
        TypeSignature::BoolType => 4,                           // i32
        TypeSignature::PrincipalType
        | TypeSignature::SequenceType(_)
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => 8, // offset: i32, length: i32
        TypeSignature::OptionalType(inner) => 4 + get_type_size(inner), // indicator: i32, value: inner
        TypeSignature::TupleType(tuple_ty) => {
            let mut size = 0;
            for inner_type in tuple_ty.get_type_map().values() {
                size += get_type_size(inner_type);
            }
            size
        }
        TypeSignature::ResponseType(inner_types) => {
            // indicator: i32, ok_val: inner_types.0, err_val: inner_types.1
            4 + get_type_size(&inner_types.0) + get_type_size(&inner_types.1)
        }
        TypeSignature::NoType => 4, // i32
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a value type")
        }
    }
}

/// Return the number of bytes required to store a value of the type `ty`.
pub fn get_type_in_memory_size(ty: &TypeSignature, include_repr: bool) -> i32 {
    match ty {
        TypeSignature::IntType | TypeSignature::UIntType => 16, // i64_low + i64_high
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(length))) => {
            let mut size = u32::from(length) as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            // Standard principal is a 1 byte version and a 20 byte Hash160.
            // Then there is an int32 for the contract name length, followed by
            // the contract name, which has a max length of 128.
            let mut size = PRINCIPAL_BYTES_MAX as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::OptionalType(inner) => 4 + get_type_in_memory_size(inner, include_repr),
        TypeSignature::SequenceType(SequenceSubtype::ListType(list_data)) => {
            if include_repr {
                8 // offset + length
                 + list_data.get_max_len() as i32
                    * get_type_in_memory_size(list_data.get_list_item_type(), true)
            } else {
                list_data.get_max_len() as i32 * get_type_size(list_data.get_list_item_type())
            }
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(length)) => {
            let mut size = u32::from(length) as i32;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(length))) => {
            let mut size = u32::from(length) as i32 * 4;
            if include_repr {
                size += 8; // offset + length
            }
            size
        }
        TypeSignature::NoType => 4,   // i32
        TypeSignature::BoolType => 4, // i32
        TypeSignature::TupleType(tuple_ty) => {
            let mut size = 0;
            for inner_type in tuple_ty.get_type_map().values() {
                size += get_type_in_memory_size(inner_type, include_repr);
            }
            size
        }
        TypeSignature::ResponseType(res_types) => {
            // indicator: i32, ok_val: inner_types.0, err_val: inner_types.1
            4 + get_type_in_memory_size(&res_types.0, include_repr)
                + get_type_in_memory_size(&res_types.1, include_repr)
        }
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

/// Return true if the value of the given type stays in memory, and false if
/// it is stored on the data stack.
pub fn is_in_memory_type(ty: &TypeSignature) -> bool {
    match ty {
        TypeSignature::NoType
        | TypeSignature::IntType
        | TypeSignature::UIntType
        | TypeSignature::BoolType
        | TypeSignature::TupleType(_)
        | TypeSignature::OptionalType(_)
        | TypeSignature::ResponseType(_) => false,
        TypeSignature::SequenceType(_)
        | TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => true,
        TypeSignature::ListUnionType(_) => unreachable!("not a value type"),
    }
}

fn clar2wasm_ty(ty: &TypeSignature) -> Vec<ValType> {
    match ty {
        TypeSignature::NoType => vec![ValType::I32], // TODO: clarity-wasm issue #445. Can this just be empty?
        TypeSignature::IntType => vec![ValType::I64, ValType::I64],
        TypeSignature::UIntType => vec![ValType::I64, ValType::I64],
        TypeSignature::ResponseType(inner_types) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(&inner_types.0));
            types.extend(clar2wasm_ty(&inner_types.1));
            types
        }
        TypeSignature::SequenceType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::BoolType => vec![ValType::I32],
        TypeSignature::PrincipalType | TypeSignature::CallableType(_) => vec![
            ValType::I32, // offset
            ValType::I32, // length
        ],
        TypeSignature::OptionalType(inner_ty) => {
            let mut types = vec![ValType::I32];
            types.extend(clar2wasm_ty(inner_ty));
            types
        }
        TypeSignature::TupleType(inner_types) => {
            let mut types = vec![];
            for inner_type in inner_types.get_type_map().values() {
                types.extend(clar2wasm_ty(inner_type));
            }
            types
        }
        _ => unimplemented!("{:?}", ty),
    }
}

/// Read bytes from the WASM memory at `offset` with `length`
fn read_bytes_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
    length: i32,
) -> Result<Vec<u8>, Error> {
    let mut buffer: Vec<u8> = vec![0; length as usize];
    memory
        .read(store, offset as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    Ok(buffer)
}

/// Read an identifier (string) from the WASM memory at `offset` with `length`.
fn read_identifier_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
    length: i32,
) -> Result<String, Error> {
    let buffer = read_bytes_from_wasm(memory, store, offset, length)?;
    String::from_utf8(buffer).map_err(|e| Error::Wasm(WasmError::UnableToReadIdentifier(e)))
}

fn read_indirect_offset_and_length(
    memory: Memory,
    store: &mut impl AsContextMut,
    offset: i32,
) -> Result<(i32, i32), Error> {
    let mut buffer: [u8; 4] = [0; 4];
    memory
        .read(store.as_context_mut(), offset as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    let indirect_offset = i32::from_le_bytes(buffer);
    memory
        .read(store.as_context_mut(), (offset + 4) as usize, &mut buffer)
        .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
    let length = i32::from_le_bytes(buffer);
    Ok((indirect_offset, length))
}

/// Read a value from the Wasm memory at `offset` with `length` given the
/// provided Clarity `TypeSignature`. In-memory values require one extra level
/// of indirection, so this function will read the offset and length from the
/// memory, then read the actual value.
fn read_from_wasm_indirect(
    memory: Memory,
    store: &mut impl AsContextMut,
    ty: &TypeSignature,
    mut offset: i32,
    epoch: StacksEpochId,
) -> Result<Value, Error> {
    let mut length = get_type_size(ty);

    // For in-memory types, first read the offset and length from the memory,
    // then read the actual value.
    if is_in_memory_type(ty) {
        (offset, length) = read_indirect_offset_and_length(memory, store, offset)?;
    };

    read_from_wasm(memory, store, ty, offset, length, epoch)
}

/// Read a value from the Wasm memory at `offset` with `length`, given the
/// provided Clarity `TypeSignature`.
fn read_from_wasm(
    memory: Memory,
    store: &mut impl AsContextMut,
    ty: &TypeSignature,
    offset: i32,
    length: i32,
    epoch: StacksEpochId,
) -> Result<Value, Error> {
    match ty {
        TypeSignature::UIntType => {
            debug_assert!(
                length == 16,
                "expected uint length to be 16 bytes, found {length}"
            );
            let mut buffer: [u8; 8] = [0; 8];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let low = u64::from_le_bytes(buffer) as u128;
            memory
                .read(store, (offset + 8) as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let high = u64::from_le_bytes(buffer) as u128;
            Ok(Value::UInt((high << 64) | low))
        }
        TypeSignature::IntType => {
            debug_assert!(
                length == 16,
                "expected int length to be 16 bytes, found {length}"
            );
            let mut buffer: [u8; 8] = [0; 8];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let low = u64::from_le_bytes(buffer) as u128;
            memory
                .read(store, (offset + 8) as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let high = u64::from_le_bytes(buffer) as u128;
            Ok(Value::Int(((high << 64) | low) as i128))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
            type_length,
        ))) => {
            debug_assert!(
                type_length >= &BufferLength::try_from(length as u32)?,
                "expected string length to be less than the type length"
            );
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::string_ascii_from_bytes(buffer)
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_s))) => {
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::string_utf8_from_unicode_scalars(buffer)
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            debug_assert!(
                length >= STANDARD_PRINCIPAL_BYTES as i32 && length <= PRINCIPAL_BYTES_MAX as i32
            );
            let mut current_offset = offset as usize;
            let mut version: [u8; PRINCIPAL_VERSION_BYTES] = [0; PRINCIPAL_VERSION_BYTES];
            let mut hash: [u8; PRINCIPAL_HASH_BYTES] = [0; PRINCIPAL_HASH_BYTES];
            memory
                .read(store.as_context_mut(), current_offset, &mut version)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += PRINCIPAL_VERSION_BYTES;
            memory
                .read(store.as_context_mut(), current_offset, &mut hash)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += PRINCIPAL_HASH_BYTES;
            let principal = StandardPrincipalData(version[0], hash);
            let mut contract_length_buf: [u8; CONTRACT_NAME_LENGTH_BYTES] =
                [0; CONTRACT_NAME_LENGTH_BYTES];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset,
                    &mut contract_length_buf,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += CONTRACT_NAME_LENGTH_BYTES;
            let contract_length = contract_length_buf[0];
            if contract_length == 0 {
                Ok(Value::Principal(principal.into()))
            } else {
                let mut contract_name: Vec<u8> = vec![0; contract_length as usize];
                memory
                    .read(store, current_offset, &mut contract_name)
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
                let contract_name = String::from_utf8(contract_name)
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
                let qualified_id = QualifiedContractIdentifier {
                    issuer: principal,
                    name: ContractName::try_from(contract_name)?,
                };
                Ok(
                    if let TypeSignature::CallableType(CallableSubtype::Trait(trait_identifier)) =
                        ty
                    {
                        Value::CallableContract(CallableData {
                            contract_identifier: qualified_id,
                            trait_identifier: Some(trait_identifier.clone()),
                        })
                    } else {
                        Value::Principal(PrincipalData::Contract(qualified_id))
                    },
                )
            }
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_b)) => {
            let mut buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            Value::buff_from(buffer)
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
            let elem_ty = list.get_list_item_type();
            let elem_length = get_type_size(elem_ty);
            let end = offset + length;
            let mut buffer: Vec<Value> = Vec::new();
            let mut current_offset = offset;
            while current_offset < end {
                let elem = read_from_wasm_indirect(memory, store, elem_ty, current_offset, epoch)?;
                buffer.push(elem);
                current_offset += elem_length;
            }
            Value::cons_list_unsanitized(buffer)
        }
        TypeSignature::BoolType => {
            debug_assert!(
                length == 4,
                "expected bool length to be 4 bytes, found {length}"
            );
            let mut buffer: [u8; 4] = [0; 4];
            memory
                .read(store.as_context_mut(), offset as usize, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            let bool_val = u32::from_le_bytes(buffer);
            Ok(Value::Bool(bool_val != 0))
        }
        TypeSignature::TupleType(type_sig) => {
            let mut data = Vec::new();
            let mut current_offset = offset;
            for (field_key, field_ty) in type_sig.get_type_map() {
                let field_length = get_type_size(field_ty);
                let field_value =
                    read_from_wasm_indirect(memory, store, field_ty, current_offset, epoch)?;
                data.push((field_key.clone(), field_value));
                current_offset += field_length;
            }
            Ok(Value::Tuple(TupleData::from_data(data)?))
        }
        TypeSignature::ResponseType(response_type) => {
            let mut current_offset = offset;

            // Read the indicator
            let mut indicator_bytes = [0u8; 4];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset as usize,
                    &mut indicator_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += 4;
            let indicator = i32::from_le_bytes(indicator_bytes);

            // Read the ok or err value, depending on the indicator
            match indicator {
                0 => {
                    current_offset += get_type_size(&response_type.0);
                    let err_value = read_from_wasm_indirect(
                        memory,
                        store,
                        &response_type.1,
                        current_offset,
                        epoch,
                    )?;
                    Value::error(err_value).map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))
                }
                1 => {
                    let ok_value = read_from_wasm_indirect(
                        memory,
                        store,
                        &response_type.0,
                        current_offset,
                        epoch,
                    )?;
                    Value::okay(ok_value).map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))
                }
                _ => Err(Error::Wasm(WasmError::InvalidIndicator(indicator))),
            }
        }
        TypeSignature::OptionalType(type_sig) => {
            let mut current_offset = offset;

            // Read the indicator
            let mut indicator_bytes = [0u8; 4];
            memory
                .read(
                    store.as_context_mut(),
                    current_offset as usize,
                    &mut indicator_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;
            current_offset += 4;
            let indicator = i32::from_le_bytes(indicator_bytes);

            match indicator {
                0 => Ok(Value::none()),
                1 => {
                    let value =
                        read_from_wasm_indirect(memory, store, type_sig, current_offset, epoch)?;
                    Ok(
                        Value::some(value)
                            .map_err(|_| Error::Wasm(WasmError::ValueTypeMismatch))?,
                    )
                }
                _ => Err(Error::Wasm(WasmError::InvalidIndicator(indicator))),
            }
        }
        TypeSignature::NoType => Err(Error::Wasm(WasmError::InvalidNoTypeInValue)),
        TypeSignature::ListUnionType(_subtypes) => {
            Err(Error::Wasm(WasmError::InvalidListUnionTypeInValue))
        }
    }
}

fn value_as_bool(value: &Value) -> Result<bool, Error> {
    match value {
        Value::Bool(b) => Ok(*b),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_i128(value: &Value) -> Result<i128, Error> {
    match value {
        Value::Int(n) => Ok(*n),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_u128(value: &Value) -> Result<u128, Error> {
    match value {
        Value::UInt(n) => Ok(*n),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_principal(value: &Value) -> Result<&PrincipalData, Error> {
    match value {
        Value::Principal(p) => Ok(p),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_buffer(value: Value) -> Result<BuffData, Error> {
    match value {
        Value::Sequence(SequenceData::Buffer(buffdata)) => Ok(buffdata),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_optional(value: &Value) -> Result<&OptionalData, Error> {
    match value {
        Value::Optional(opt_data) => Ok(opt_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_response(value: &Value) -> Result<&ResponseData, Error> {
    match value {
        Value::Response(res_data) => Ok(res_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_string_ascii(value: Value) -> Result<ASCIIData, Error> {
    match value {
        Value::Sequence(SequenceData::String(CharType::ASCII(string_data))) => Ok(string_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_tuple(value: &Value) -> Result<&TupleData, Error> {
    match value {
        Value::Tuple(d) => Ok(d),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

fn value_as_list(value: &Value) -> Result<&ListData, Error> {
    match value {
        Value::Sequence(SequenceData::List(list_data)) => Ok(list_data),
        _ => Err(Error::Wasm(WasmError::ValueTypeMismatch)),
    }
}

/// Write a value to the Wasm memory at `offset` given the provided Clarity
/// `TypeSignature`.
///
/// If the value is an in-memory type, then it will be written
/// to the memory at `in_mem_offset`, and if `include_repr` is true, the offset
/// and length of the value will be written to the memory at `offset`.
/// Returns the number of bytes written at `offset` and at `in_mem_offset`.
fn write_to_wasm(
    mut store: impl AsContextMut,
    memory: Memory,
    ty: &TypeSignature,
    offset: i32,
    in_mem_offset: i32,
    value: &Value,
    include_repr: bool,
) -> Result<(i32, i32), Error> {
    match ty {
        TypeSignature::IntType => {
            let mut buffer: [u8; 8] = [0; 8];
            let i = value_as_i128(value)?;
            let high = (i >> 64) as u64;
            let low = (i & 0xffff_ffff_ffff_ffff) as u64;
            buffer.copy_from_slice(&low.to_le_bytes());
            memory
                .write(&mut store, offset as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            buffer.copy_from_slice(&high.to_le_bytes());
            memory
                .write(&mut store, (offset + 8) as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((16, 0))
        }
        TypeSignature::UIntType => {
            let mut buffer: [u8; 8] = [0; 8];
            let i = value_as_u128(value)?;
            let high = (i >> 64) as u64;
            let low = (i & 0xffff_ffff_ffff_ffff) as u64;
            buffer.copy_from_slice(&low.to_le_bytes());
            memory
                .write(&mut store, offset as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            buffer.copy_from_slice(&high.to_le_bytes());
            memory
                .write(&mut store, (offset + 8) as usize, &buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((16, 0))
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_length)) => {
            let buffdata = value_as_buffer(value.clone())?;
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to `in_mem_offset`
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &buffdata.data,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += buffdata.data.len() as i32;

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(string_subtype)) => {
            let string = match string_subtype {
                StringSubtype::ASCII(_length) => value_as_string_ascii(value.clone())?.data,
                StringSubtype::UTF8(_length) => {
                    let Value::Sequence(SequenceData::String(CharType::UTF8(utf8_data))) = value
                    else {
                        unreachable!("A string-utf8 type should contain a string-utf8 value")
                    };
                    String::from_utf8(utf8_data.items().iter().flatten().copied().collect())
                        .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?
                        .chars()
                        .flat_map(|c| (c as u32).to_be_bytes())
                        .collect()
                }
            };
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to `in_mem_offset`
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &string,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += string.len() as i32;

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(list)) => {
            let mut written = 0;
            let list_data = value_as_list(value)?;
            let elem_ty = list.get_list_item_type();
            // For a list, the values are written to the memory at
            // `in_mem_offset`, and the representation (offset and length) is
            // written to the memory at `offset`. The `in_mem_offset` for the
            // list elements should be after their representations.
            let val_offset = in_mem_offset;
            let val_in_mem_offset =
                in_mem_offset + list_data.data.len() as i32 * get_type_size(elem_ty);
            let mut val_written = 0;
            let mut val_in_mem_written = 0;
            for elem in &list_data.data {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store.as_context_mut(),
                    memory,
                    elem_ty,
                    val_offset + val_written,
                    val_in_mem_offset + val_in_mem_written,
                    elem,
                    true,
                )?;
                val_written += new_written;
                val_in_mem_written += new_in_mem_written;
            }

            if include_repr {
                // Write the representation (offset and length) of the value to
                // `offset`.
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = val_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + 4) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, val_written + val_in_mem_written))
        }
        TypeSignature::ResponseType(inner_types) => {
            let mut written = 0;
            let mut in_mem_written = 0;
            let res = value_as_response(value)?;
            let indicator = if res.committed { 1i32 } else { 0i32 };
            let indicator_bytes = indicator.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &indicator_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            written += 4;

            if res.committed {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    &inner_types.0,
                    offset + written,
                    in_mem_offset,
                    &res.data,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;

                // Skip space for the err value
                written += get_type_size(&inner_types.1);
            } else {
                // Skip space for the ok value
                written += get_type_size(&inner_types.0);

                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    &inner_types.1,
                    offset + written,
                    in_mem_offset,
                    &res.data,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            }
            Ok((written, in_mem_written))
        }
        TypeSignature::BoolType => {
            let bool_val = value_as_bool(value)?;
            let val = if bool_val { 1u32 } else { 0u32 };
            let val_bytes = val.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &val_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((4, 0))
        }
        TypeSignature::NoType => {
            let val_bytes = [0u8; 4];
            memory
                .write(&mut store, (offset) as usize, &val_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            Ok((4, 0))
        }
        TypeSignature::OptionalType(inner_ty) => {
            let mut written = 0;
            let mut in_mem_written = 0;
            let opt_data = value_as_optional(value)?;
            let indicator = if opt_data.data.is_some() { 1i32 } else { 0i32 };
            let indicator_bytes = indicator.to_le_bytes();
            memory
                .write(&mut store, (offset) as usize, &indicator_bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            written += 4;
            if let Some(inner) = opt_data.data.as_ref() {
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store,
                    memory,
                    inner_ty,
                    offset + written,
                    in_mem_offset,
                    inner,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            } else {
                written += get_type_size(inner_ty);
            }
            Ok((written, in_mem_written))
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            let principal = value_as_principal(value)?;
            let (standard, contract_name) = match principal {
                PrincipalData::Standard(s) => (s, ""),
                PrincipalData::Contract(contract_identifier) => (
                    &contract_identifier.issuer,
                    contract_identifier.name.as_str(),
                ),
            };
            let mut written = 0;
            let mut in_mem_written = 0;

            // Write the value to in_mem_offset
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &[standard.0],
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += 1;
            memory
                .write(
                    &mut store,
                    (in_mem_offset + in_mem_written) as usize,
                    &standard.1,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            in_mem_written += standard.1.len() as i32;
            if !contract_name.is_empty() {
                let len_buffer = [contract_name.len() as u8];
                memory
                    .write(
                        &mut store,
                        (in_mem_offset + in_mem_written) as usize,
                        &len_buffer,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += 1;
                let bytes = contract_name.as_bytes();
                memory
                    .write(&mut store, (in_mem_offset + in_mem_written) as usize, bytes)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += bytes.len() as i32;
            } else {
                let len_buffer = [0u8];
                memory
                    .write(
                        &mut store,
                        (in_mem_offset + in_mem_written) as usize,
                        &len_buffer,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                in_mem_written += 1;
            }

            if include_repr {
                // Write the representation (offset and length of the value) to the
                // offset
                let offset_buffer = in_mem_offset.to_le_bytes();
                memory
                    .write(&mut store, (offset) as usize, &offset_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
                let len_buffer = in_mem_written.to_le_bytes();
                memory
                    .write(&mut store, (offset + written) as usize, &len_buffer)
                    .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
                written += 4;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::TupleType(type_sig) => {
            let tuple_data = value_as_tuple(value)?;
            let mut written = 0;
            let mut in_mem_written = 0;

            for (key, val_type) in type_sig.get_type_map() {
                let val = tuple_data
                    .data_map
                    .get(key)
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
                let (new_written, new_in_mem_written) = write_to_wasm(
                    store.as_context_mut(),
                    memory,
                    val_type,
                    offset + written,
                    in_mem_offset + in_mem_written,
                    val,
                    true,
                )?;
                written += new_written;
                in_mem_written += new_in_mem_written;
            }

            Ok((written, in_mem_written))
        }
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a value type")
        }
    }
}

/// Convert a Clarity `Value` into one or more Wasm `Val`. If this value
/// requires writing into the Wasm memory, write it to the provided `offset`.
/// Return a vector of `Val`s that can be passed to a Wasm function, and the
/// two offsets, adjusted to the next available memory location.
fn pass_argument_to_wasm(
    memory: Memory,
    mut store: impl AsContextMut,
    ty: &TypeSignature,
    value: &Value,
    offset: i32,
    in_mem_offset: i32,
) -> Result<(Vec<Val>, i32, i32), Error> {
    match value {
        Value::UInt(n) => {
            let high = (n >> 64) as u64;
            let low = (n & 0xffff_ffff_ffff_ffff) as u64;
            let buffer = vec![Val::I64(low as i64), Val::I64(high as i64)];
            Ok((buffer, offset, in_mem_offset))
        }
        Value::Int(n) => {
            let high = (n >> 64) as u64;
            let low = (n & 0xffff_ffff_ffff_ffff) as u64;
            let buffer = vec![Val::I64(low as i64), Val::I64(high as i64)];
            Ok((buffer, offset, in_mem_offset))
        }
        Value::Bool(b) => Ok((
            vec![Val::I32(if *b { 1 } else { 0 })],
            offset,
            in_mem_offset,
        )),
        Value::Optional(o) => {
            let TypeSignature::OptionalType(inner_ty) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            if let Some(inner_value) = o.data.as_ref() {
                let mut buffer = vec![Val::I32(1)];
                let (inner_buffer, new_offset, new_in_mem_offset) = pass_argument_to_wasm(
                    memory,
                    store,
                    inner_ty,
                    inner_value,
                    offset,
                    in_mem_offset,
                )?;
                buffer.extend(inner_buffer);
                Ok((buffer, new_offset, new_in_mem_offset))
            } else {
                let buffer = clar2wasm_ty(ty)
                    .into_iter()
                    .map(|vt| match vt {
                        ValType::I32 => Val::I32(0),
                        ValType::I64 => Val::I64(0),
                        _ => unreachable!("No other types used in Clarity-Wasm"),
                    })
                    .collect();
                Ok((buffer, offset, in_mem_offset))
            }
        }
        Value::Response(r) => {
            let TypeSignature::ResponseType(inner_tys) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };
            let mut buffer = vec![Val::I32(r.committed as i32)];
            let (value_buffer, new_offset, new_in_mem_offset) = pass_argument_to_wasm(
                memory,
                store,
                if r.committed {
                    &inner_tys.0
                } else {
                    &inner_tys.1
                },
                &r.data,
                offset,
                in_mem_offset,
            )?;
            let empty_buffer = clar2wasm_ty(if r.committed {
                &inner_tys.1
            } else {
                &inner_tys.0
            })
            .into_iter()
            .map(|vt| match vt {
                ValType::I32 => Val::I32(0),
                ValType::I64 => Val::I64(0),
                _ => unreachable!("No other types used in Clarity-Wasm"),
            });

            if r.committed {
                buffer.extend(value_buffer);
                buffer.extend(empty_buffer);
            } else {
                buffer.extend(empty_buffer);
                buffer.extend(value_buffer);
            }

            Ok((buffer, new_offset, new_in_mem_offset))
        }
        Value::Sequence(SequenceData::String(CharType::ASCII(s))) => {
            // For a string, write the bytes into the memory, then pass the
            // offset and length to the Wasm function.
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(s.data.len() as i32)];
            memory
                .write(
                    store.as_context_mut(),
                    in_mem_offset as usize,
                    s.data.as_slice(),
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + s.data.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::String(CharType::UTF8(s))) => {
            // For a utf8 string, convert the chars to big-endian i32, convert this into a list of
            // bytes, then pass the offset and length to the wasm function
            let bytes: Vec<u8> = String::from_utf8(s.items().iter().flatten().copied().collect())
                .map_err(|e| Error::Wasm(WasmError::WasmGeneratorError(e.to_string())))?
                .chars()
                .flat_map(|c| (c as u32).to_be_bytes())
                .collect();
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::Buffer(b)) => {
            // For a buffer, write the bytes into the memory, then pass the
            // offset and length to the Wasm function.
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(b.data.len() as i32)];
            memory
                .write(
                    store.as_context_mut(),
                    in_mem_offset as usize,
                    b.data.as_slice(),
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + b.data.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Sequence(SequenceData::List(l)) => {
            let TypeSignature::SequenceType(SequenceSubtype::ListType(ltd)) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            let mut buffer = vec![Val::I32(offset)];
            let mut written = 0;
            let mut in_mem_written = 0;
            for item in &l.data {
                let (len, in_mem_len) = write_to_wasm(
                    &mut store,
                    memory,
                    ltd.get_list_item_type(),
                    offset + written,
                    in_mem_offset + in_mem_written,
                    item,
                    true,
                )?;
                written += len;
                in_mem_written += in_mem_len;
            }
            buffer.push(Val::I32(written));
            Ok((buffer, offset + written, in_mem_offset + in_mem_written))
        }
        Value::Principal(PrincipalData::Standard(StandardPrincipalData(v, h))) => {
            let mut bytes: Vec<u8> = Vec::with_capacity(22);
            bytes.push(*v);
            bytes.extend(h);
            bytes.push(0);
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Principal(PrincipalData::Contract(p))
        | Value::CallableContract(CallableData {
            contract_identifier: p,
            ..
        }) => {
            // Callable types can just ignore the optional trait identifier, and
            // is handled like a qualified contract
            let QualifiedContractIdentifier {
                issuer: StandardPrincipalData(v, h),
                name,
            } = p;
            let bytes: Vec<u8> = std::iter::once(v)
                .chain(h.iter())
                .chain(std::iter::once(&name.len()))
                .chain(name.as_bytes())
                .copied()
                .collect();
            let buffer = vec![Val::I32(in_mem_offset), Val::I32(bytes.len() as i32)];
            memory
                .write(&mut store, in_mem_offset as usize, &bytes)
                .map_err(|e| Error::Wasm(WasmError::UnableToWriteMemory(e.into())))?;
            let adjusted_in_mem_offset = in_mem_offset + bytes.len() as i32;
            Ok((buffer, offset, adjusted_in_mem_offset))
        }
        Value::Tuple(TupleData { data_map, .. }) => {
            let TypeSignature::TupleType(tuple_ty) = ty else {
                return Err(Error::Wasm(WasmError::ValueTypeMismatch));
            };

            let mut buffer = vec![];
            let mut offset = offset;
            let mut in_mem_offset = in_mem_offset;
            for (name, ty) in tuple_ty.get_type_map() {
                let b;
                (b, offset, in_mem_offset) = pass_argument_to_wasm(
                    memory,
                    store.as_context_mut(),
                    ty,
                    &data_map[name],
                    offset,
                    in_mem_offset,
                )?;
                buffer.extend(b);
            }
            Ok((buffer, offset, in_mem_offset))
        }
    }
}

pub fn signature_from_string(
    val: &str,
    version: ClarityVersion,
    epoch: StacksEpochId,
) -> Result<TypeSignature, Error> {
    let expr = build_ast_with_rules(
        &QualifiedContractIdentifier::transient(),
        val,
        &mut (),
        version,
        epoch,
        ASTRules::Typical,
    )?
    .expressions;
    let expr = expr.first().ok_or(CheckErrors::InvalidTypeDescription)?;
    Ok(TypeSignature::parse_type_repr(
        StacksEpochId::latest(),
        expr,
        &mut (),
    )?)
}

/// Reserve space on the Wasm stack for the return value of a function, if
/// needed, and return a vector of `Val`s that can be passed to `call`, as a
/// place to store the return value, along with the new offset, which is the
/// next available memory location.
fn reserve_space_for_return(
    offset: i32,
    return_type: &TypeSignature,
) -> Result<(Vec<Val>, i32), Error> {
    match return_type {
        TypeSignature::UIntType | TypeSignature::IntType => {
            Ok((vec![Val::I64(0), Val::I64(0)], offset))
        }
        TypeSignature::BoolType => Ok((vec![Val::I32(0)], offset)),
        TypeSignature::OptionalType(optional) => {
            let mut vals = vec![Val::I32(0)];
            let (opt_vals, adjusted) = reserve_space_for_return(offset, optional)?;
            vals.extend(opt_vals);
            Ok((vals, adjusted))
        }
        TypeSignature::ResponseType(response) => {
            let mut vals = vec![Val::I32(0)];
            let (mut subexpr_values, mut adjusted) = reserve_space_for_return(offset, &response.0)?;
            vals.extend(subexpr_values);
            (subexpr_values, adjusted) = reserve_space_for_return(adjusted, &response.1)?;
            vals.extend(subexpr_values);
            Ok((vals, adjusted))
        }
        TypeSignature::NoType => Ok((vec![Val::I32(0)], offset)),
        TypeSignature::SequenceType(_)
        | TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            // All in-memory types return an offset and length.˝
            let length = get_type_in_memory_size(return_type, false);

            // Return values will be offset and length
            Ok((vec![Val::I32(0), Val::I32(0)], offset + length))
        }
        TypeSignature::TupleType(type_sig) => {
            let mut vals = vec![];
            let mut adjusted = offset;
            for ty in type_sig.get_type_map().values() {
                let (subexpr_values, new_offset) = reserve_space_for_return(adjusted, ty)?;
                vals.extend(subexpr_values);
                adjusted = new_offset;
            }
            Ok((vals, adjusted))
        }
        TypeSignature::ListUnionType(_) => {
            unreachable!("not a valid return type");
        }
    }
}

/// Convert a Wasm value into a Clarity `Value`. Depending on the type, the
/// values may be directly passed in the Wasm `Val`s or may be read from the
/// Wasm memory, via an offset and size.
/// - `type_sig` is the Clarity type of the value.
/// - `value_index` is the index of the value in the array of Wasm `Val`s.
/// - `buffer` is the array of Wasm `Val`s.
/// - `memory` is the Wasm memory.
/// - `store` is the Wasm store.
/// Returns the Clarity `Value` and the number of Wasm `Val`s that were used.
fn wasm_to_clarity_value(
    type_sig: &TypeSignature,
    value_index: usize,
    buffer: &[Val],
    memory: Memory,
    store: &mut impl AsContextMut,
    epoch: StacksEpochId,
) -> Result<(Option<Value>, usize), Error> {
    match type_sig {
        TypeSignature::IntType => {
            let lower = buffer[value_index]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let upper = buffer[value_index + 1]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            Ok((
                Some(Value::Int(((upper as i128) << 64) | (lower as u64) as i128)),
                2,
            ))
        }
        TypeSignature::UIntType => {
            let lower = buffer[value_index]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let upper = buffer[value_index + 1]
                .i64()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            Ok((
                Some(Value::UInt(
                    ((upper as u128) << 64) | (lower as u64) as u128,
                )),
                2,
            ))
        }
        TypeSignature::BoolType => Ok((
            Some(Value::Bool(
                buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    != 0,
            )),
            1,
        )),
        TypeSignature::OptionalType(optional) => {
            let value_types = clar2wasm_ty(optional);
            Ok((
                if buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    == 1
                {
                    let (value, _) = wasm_to_clarity_value(
                        optional,
                        value_index + 1,
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::some(value.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineType,
                    ))?)?)
                } else {
                    Some(Value::none())
                },
                1 + value_types.len(),
            ))
        }
        TypeSignature::ResponseType(response) => {
            let ok_types = clar2wasm_ty(&response.0);
            let err_types = clar2wasm_ty(&response.1);

            Ok((
                if buffer[value_index]
                    .i32()
                    .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?
                    == 1
                {
                    let (ok, _) = wasm_to_clarity_value(
                        &response.0,
                        value_index + 1,
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::okay(ok.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineResponseOkType,
                    ))?)?)
                } else {
                    let (err, _) = wasm_to_clarity_value(
                        &response.1,
                        value_index + 1 + ok_types.len(),
                        buffer,
                        memory,
                        store,
                        epoch,
                    )?;
                    Some(Value::error(err.ok_or(Error::Unchecked(
                        CheckErrors::CouldNotDetermineResponseErrType,
                    ))?)?)
                },
                1 + ok_types.len() + err_types.len(),
            ))
        }
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut string_buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut string_buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((Some(Value::string_ascii_from_bytes(string_buffer)?), 2))
        }
        // A `NoType` will be a dummy value that should not be used.
        TypeSignature::NoType => Ok((None, 1)),
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut string_buffer: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut string_buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((
                Some(Value::string_utf8_from_unicode_scalars(string_buffer)?),
                2,
            ))
        }
        TypeSignature::SequenceType(SequenceSubtype::BufferType(_buffer_length)) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut buff: Vec<u8> = vec![0; length as usize];
            memory
                .read(store, offset as usize, &mut buff)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            Ok((Some(Value::buff_from(buff)?), 2))
        }
        TypeSignature::SequenceType(SequenceSubtype::ListType(_)) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let length = buffer[value_index + 1]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;

            let value = read_from_wasm(memory, store, type_sig, offset, length, epoch)?;
            Ok((Some(value), 2))
        }
        TypeSignature::PrincipalType
        | TypeSignature::CallableType(_)
        | TypeSignature::TraitReferenceType(_) => {
            let offset = buffer[value_index]
                .i32()
                .ok_or(Error::Wasm(WasmError::ValueTypeMismatch))?;
            let mut principal_bytes: [u8; 1 + PRINCIPAL_HASH_BYTES] = [0; 1 + PRINCIPAL_HASH_BYTES];
            memory
                .read(
                    store.as_context_mut(),
                    offset as usize,
                    &mut principal_bytes,
                )
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            let mut buffer: [u8; CONTRACT_NAME_LENGTH_BYTES] = [0; CONTRACT_NAME_LENGTH_BYTES];
            memory
                .read(store.as_context_mut(), offset as usize + 21, &mut buffer)
                .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
            let standard = StandardPrincipalData(
                principal_bytes[0],
                principal_bytes[1..].try_into().map_err(|_| {
                    Error::Wasm(WasmError::WasmGeneratorError(
                        "Could not decode principal".into(),
                    ))
                })?,
            );
            let contract_name_length = buffer[0] as usize;
            if contract_name_length == 0 {
                Ok((Some(Value::Principal(PrincipalData::Standard(standard))), 2))
            } else {
                let mut contract_name: Vec<u8> = vec![0; contract_name_length];
                memory
                    .read(
                        store,
                        (offset + STANDARD_PRINCIPAL_BYTES as i32) as usize,
                        &mut contract_name,
                    )
                    .map_err(|e| Error::Wasm(WasmError::UnableToReadMemory(e.into())))?;
                let qualified_id = QualifiedContractIdentifier {
                    issuer: standard,
                    name: ContractName::try_from(
                        String::from_utf8(contract_name)
                            .map_err(|e| Error::Wasm(WasmError::UnableToReadIdentifier(e)))?,
                    )?,
                };
                Ok((
                    Some(
                        if let TypeSignature::CallableType(CallableSubtype::Trait(
                            trait_identifier,
                        )) = type_sig
                        {
                            Value::CallableContract(CallableData {
                                contract_identifier: qualified_id,
                                trait_identifier: Some(trait_identifier.clone()),
                            })
                        } else {
                            Value::Principal(PrincipalData::Contract(qualified_id))
                        },
                    ),
                    2,
                ))
            }
        }
        TypeSignature::TupleType(t) => {
            let mut index = value_index;
            let mut data_map = Vec::new();
            for (name, ty) in t.get_type_map() {
                let (value, increment) =
                    wasm_to_clarity_value(ty, index, buffer, memory, store, epoch)?;
                data_map.push((
                    name.clone(),
                    value.ok_or(Error::Unchecked(CheckErrors::BadTupleConstruction))?,
                ));
                index += increment;
            }
            let tuple = TupleData::from_data(data_map)?;
            Ok((Some(tuple.into()), index - value_index))
        }
        TypeSignature::ListUnionType(_subtypes) => {
            Err(Error::Wasm(WasmError::InvalidListUnionTypeInValue))
        }
    }
}

/// Link the host interface functions for into the Wasm module.
fn link_host_functions(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    link_define_function_fn(linker)?;
    link_define_variable_fn(linker)?;
    link_define_ft_fn(linker)?;
    link_define_nft_fn(linker)?;
    link_define_map_fn(linker)?;
    link_define_trait_fn(linker)?;
    link_impl_trait_fn(linker)?;

    link_get_variable_fn(linker)?;
    link_set_variable_fn(linker)?;
    link_tx_sender_fn(linker)?;
    link_contract_caller_fn(linker)?;
    link_tx_sponsor_fn(linker)?;
    link_block_height_fn(linker)?;
    link_stacks_block_height_fn(linker)?;
    link_tenure_height_fn(linker)?;
    link_burn_block_height_fn(linker)?;
    link_stx_liquid_supply_fn(linker)?;
    link_is_in_regtest_fn(linker)?;
    link_is_in_mainnet_fn(linker)?;
    link_chain_id_fn(linker)?;
    link_enter_as_contract_fn(linker)?;
    link_exit_as_contract_fn(linker)?;
    link_stx_get_balance_fn(linker)?;
    link_stx_account_fn(linker)?;
    link_stx_burn_fn(linker)?;
    link_stx_transfer_fn(linker)?;
    link_ft_get_supply_fn(linker)?;
    link_ft_get_balance_fn(linker)?;
    link_ft_burn_fn(linker)?;
    link_ft_mint_fn(linker)?;
    link_ft_transfer_fn(linker)?;
    link_nft_get_owner_fn(linker)?;
    link_nft_burn_fn(linker)?;
    link_nft_mint_fn(linker)?;
    link_nft_transfer_fn(linker)?;
    link_map_get_fn(linker)?;
    link_map_set_fn(linker)?;
    link_map_insert_fn(linker)?;
    link_map_delete_fn(linker)?;
    link_get_stacks_block_info_header_hash_property_fn(linker)?;
    link_get_stacks_block_info_time_property_fn(linker)?;
    link_get_stacks_block_info_identity_header_hash_property_fn(linker)?;
    link_get_tenure_info_burnchain_header_hash_property_fn(linker)?;
    link_get_tenure_info_miner_address_property_fn(linker)?;
    link_get_tenure_info_vrf_seed_property_fn(linker)?;
    link_get_tenure_info_time_property_fn(linker)?;
    link_get_tenure_info_block_reward_property_fn(linker)?;
    link_get_tenure_info_miner_spend_total_property_fn(linker)?;
    link_get_tenure_info_miner_spend_winner_property_fn(linker)?;
    link_get_block_info_time_property_fn(linker)?;
    link_get_block_info_vrf_seed_property_fn(linker)?;
    link_get_block_info_header_hash_property_fn(linker)?;
    link_get_block_info_burnchain_header_hash_property_fn(linker)?;
    link_get_block_info_identity_header_hash_property_fn(linker)?;
    link_get_block_info_miner_address_property_fn(linker)?;
    link_get_block_info_miner_spend_winner_property_fn(linker)?;
    link_get_block_info_miner_spend_total_property_fn(linker)?;
    link_get_block_info_block_reward_property_fn(linker)?;
    link_get_burn_block_info_header_hash_property_fn(linker)?;
    link_get_burn_block_info_pox_addrs_property_fn(linker)?;
    link_contract_call_fn(linker)?;
    link_begin_public_call_fn(linker)?;
    link_begin_read_only_call_fn(linker)?;
    link_commit_call_fn(linker)?;
    link_roll_back_call_fn(linker)?;
    link_print_fn(linker)?;
    link_enter_at_block_fn(linker)?;
    link_exit_at_block_fn(linker)?;
    link_keccak256_fn(linker)?;
    link_sha512_fn(linker)?;
    link_sha512_256_fn(linker)?;
    link_secp256k1_recover_fn(linker)?;
    link_secp256k1_verify_fn(linker)?;
    link_principal_of_fn(linker)?;
    link_save_constant_fn(linker)?;
    link_load_constant_fn(linker)?;
    link_skip_list(linker)?;

    link_log(linker)?;
    link_debug_msg(linker)
}

/// Link host interface function, `define_variable`, into the Wasm module.
/// This function is called for all variable definitions (`define-data-var`).
fn link_define_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                // TODO: clarity-wasm issue #344 Include this cost
                // runtime_cost(ClarityCostFunction::CreateVar, global_context, value_type.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the variable name string from the memory
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                // Retrieve the type of this variable
                let value_type = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_persisted_variable_type(name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::DefineVariableBadSignature))?
                    .clone();

                let contract = caller.data().contract_context().contract_identifier.clone();

                // Read the initial value from the memory
                if is_in_memory_type(&value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(ClarityName::try_from(name.clone())?);

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(value_type.type_size()? as u64)
                    .map_err(|e| Error::from(e))?;

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(value.size()? as u64)
                    .map_err(|e| Error::from(e))?;

                // Create the variable in the global context
                let data_types = caller.data_mut().global_context.database.create_variable(
                    &contract,
                    name.as_str(),
                    value_type,
                )?;

                // Store the variable in the global context
                caller.data_mut().global_context.database.set_variable(
                    &contract,
                    name.as_str(),
                    value,
                    &data_types,
                    &epoch,
                )?;

                // Save the metadata for this variable in the contract context
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_data_var
                    .insert(ClarityName::from(name.as_str()), data_types);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_variable".to_string(),
                e,
            ))
        })
}

fn link_define_ft_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_ft",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             supply_indicator: i32,
             supply_lo: i64,
             supply_hi: i64| {
                // runtime_cost(ClarityCostFunction::CreateFt, global_context, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let total_supply = if supply_indicator == 1 {
                    Some(((supply_hi as u128) << 64) | supply_lo as u128)
                } else {
                    None
                };

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(
                        TypeSignature::UIntType
                            .type_size()
                            .expect("type size should be realizable")
                            as u64,
                    )
                    .map_err(|e| Error::from(e))?;
                let data_type = caller
                    .data_mut()
                    .global_context
                    .database
                    .create_fungible_token(&contract_identifier, &name, &total_supply)?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_ft
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_ft".to_string(),
                e,
            ))
        })
}

fn link_define_nft_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_nft",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // runtime_cost(ClarityCostFunction::CreateNft, global_context, asset_type.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                // Get the type of this NFT from the contract analysis
                let asset_type = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .non_fungible_tokens
                    .get(&cname)
                    .ok_or(Error::Unchecked(CheckErrors::DefineNFTBadSignature))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(
                        asset_type
                            .type_size()
                            .expect("type size should be realizable")
                            as u64,
                    )
                    .map_err(|e| Error::from(e))?;

                let data_type = caller
                    .data_mut()
                    .global_context
                    .database
                    .create_non_fungible_token(&contract_identifier, &name, &asset_type)?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_nft
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_nft".to_string(),
                e,
            ))
        })
}

fn link_define_map_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_map",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // runtime_cost(
                //     ClarityCostFunction::CreateMap,
                //     global_context,
                //     u64::from(key_type.size()).cost_overflow_add(u64::from(value_type.size()))?,
                // )?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier = caller
                    .data_mut()
                    .contract_context()
                    .contract_identifier
                    .clone();

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let (key_type, value_type) = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_map_type(&name)
                    .ok_or(Error::Unchecked(CheckErrors::BadMapTypeDefinition))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .persisted_names
                    .insert(cname.clone());

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(
                        key_type
                            .type_size()
                            .expect("type size should be realizable")
                            as u64,
                    )
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(
                        value_type
                            .type_size()
                            .expect("type size should be realizable")
                            as u64,
                    )
                    .map_err(|e| Error::from(e))?;

                let data_type = caller.data_mut().global_context.database.create_map(
                    &contract_identifier,
                    &name,
                    key_type.clone(),
                    value_type.clone(),
                )?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .meta_data_map
                    .insert(cname, data_type);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `define_function`, into the Wasm module.
/// This function is called for all function definitions.
fn link_define_function_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_function",
            |mut caller: Caller<'_, ClarityWasmContext>,
             kind: i32,
             name_offset: i32,
             name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the variable name string from the memory
                let function_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let function_cname = ClarityName::try_from(function_name.clone())?;

                // Retrieve the kind of function
                let (define_type, function_type) = match kind {
                    0 => (
                        DefineType::ReadOnly,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_read_only_function_type(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    1 => (
                        DefineType::Public,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_public_function_type(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    2 => (
                        DefineType::Private,
                        caller
                            .data()
                            .contract_analysis
                            .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                            .get_private_function(&function_name)
                            .ok_or(Error::Unchecked(CheckErrors::UnknownFunction(
                                function_name.clone(),
                            )))?,
                    ),
                    _ => Err(Error::Wasm(WasmError::InvalidFunctionKind(kind)))?,
                };

                let fixed_type = match function_type {
                    FunctionType::Fixed(fixed_type) => fixed_type,
                    _ => Err(Error::Unchecked(CheckErrors::DefineFunctionBadSignature))?,
                };

                let function = DefinedFunction::new(
                    fixed_type
                        .args
                        .iter()
                        .map(|arg| (arg.name.clone(), arg.signature.clone()))
                        .collect(),
                    // TODO: We don't actually need the body here, so we
                    // should be able to remove it. For now, this is a
                    // placeholder.
                    SymbolicExpression::literal_value(Value::Int(0)),
                    define_type,
                    &function_cname,
                    &caller
                        .data()
                        .contract_context()
                        .contract_identifier
                        .to_string(),
                    Some(fixed_type.returns.clone()),
                );

                // Insert this function into the context
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .functions
                    .insert(function_cname, function);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_function".to_string(),
                e,
            ))
        })
}

fn link_define_trait_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "define_trait",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::try_from(name.clone())?;

                let trait_def = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefineFunctionCalledInRunMode))?
                    .get_defined_trait(name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::DefineTraitBadSignature))?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .defined_traits
                    .insert(cname, trait_def.clone());

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

fn link_impl_trait_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "impl_trait",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let trait_id_string =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let trait_id = TraitIdentifier::parse_fully_qualified(trait_id_string.as_str())?;

                caller
                    .data_mut()
                    .contract_context_mut()?
                    .implemented_traits
                    .insert(trait_id);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "define_map".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_variable`, into the Wasm module.
/// This function is called for all variable lookups (`var-get`).
fn link_get_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the variable name for this identifier
                let var_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the metadata for this variable
                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_var
                    .get(var_name.as_str())
                    .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?
                    .clone();

                let result = caller
                    .data_mut()
                    .global_context
                    .database
                    .lookup_variable_with_size(&contract, var_name.as_str(), &data_types, &epoch);

                let _result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => data_types.value_type.size()? as u64,
                };

                // TODO: clarity-wasm issue #344 Include this cost
                // runtime_cost(ClarityCostFunction::FetchVar, env, result_size)?;

                let value = result.map(|data| data.value)?;
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                write_to_wasm(
                    &mut caller,
                    memory,
                    &data_types.value_type,
                    return_offset,
                    return_offset + get_type_size(&data_types.value_type),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_variable".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `set_variable`, into the Wasm module.
/// This function is called for all variable assignments (`var-set`).
fn link_set_variable_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "set_variable",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the variable name for this identifier
                let var_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_var
                    .get(var_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchDataVariable(
                        var_name.to_string(),
                    )))?
                    .clone();

                // TODO: clarity-wasm issue #344 Include this cost
                // runtime_cost(
                //     ClarityCostFunction::SetVar,
                //     env,
                //     data_types.value_type.size(),
                // )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // TODO: clarity-wasm issue #344 Include this cost
                // env.add_memory(value.get_memory_use())?;

                // Store the variable in the global context
                caller
                    .data_mut()
                    .global_context
                    .database
                    .set_variable(&contract, var_name.as_str(), value, &data_types, &epoch)
                    .map_err(|e| Error::from(e))?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "set_variable".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tx_sender`, into the Wasm module.
/// This function is called for use of the builtin variable, `tx-sender`.
fn link_tx_sender_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tx_sender",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let sender = caller.data().sender.clone().ok_or(Error::Runtime(
                    RuntimeErrorType::NoSenderInContext.into(),
                    None,
                ))?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let (_, bytes_written) = write_to_wasm(
                    &mut caller,
                    memory,
                    &TypeSignature::PrincipalType,
                    return_offset,
                    return_offset,
                    &Value::Principal(sender),
                    false,
                )?;

                Ok((return_offset, bytes_written))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tx_sender".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `contract_caller`, into the Wasm module.
/// This function is called for use of the builtin variable, `contract-caller`.
fn link_contract_caller_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "contract_caller",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let contract_caller = caller.data().caller.clone().ok_or(Error::Runtime(
                    RuntimeErrorType::NoCallerInContext.into(),
                    None,
                ))?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let (_, bytes_written) = write_to_wasm(
                    &mut caller,
                    memory,
                    &TypeSignature::PrincipalType,
                    return_offset,
                    return_offset,
                    &Value::Principal(contract_caller),
                    false,
                )?;

                Ok((return_offset, bytes_written))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "contract_caller".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tx_sponsor`, into the Wasm module.
/// This function is called for use of the builtin variable, `tx-sponsor`.
fn link_tx_sponsor_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tx_sponsor",
            |mut caller: Caller<'_, ClarityWasmContext>,
             return_offset: i32,
             _return_length: i32| {
                let opt_sponsor = caller.data().sponsor.clone();
                if let Some(sponsor) = opt_sponsor {
                    let memory = caller
                        .get_export("memory")
                        .and_then(|export| export.into_memory())
                        .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                    let (_, bytes_written) = write_to_wasm(
                        &mut caller,
                        memory,
                        &TypeSignature::PrincipalType,
                        return_offset,
                        return_offset,
                        &Value::Principal(sponsor),
                        false,
                    )?;

                    Ok((1i32, return_offset, bytes_written))
                } else {
                    Ok((0i32, return_offset, 0i32))
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tx_sponsor".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `block_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `block-height`.
fn link_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_block_height();
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stacks_block_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `stacks_block-height`.
fn link_stacks_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stacks_block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_block_height();
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stacks_block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `tenure_height`, into the Wasm module.
/// This function is called for use of the builtin variable, `tenure-height`.
fn link_tenure_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "tenure_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_tenure_height()?;
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "tenure_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `burn_block_height`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `burn-block-height`.
fn link_burn_block_height_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "burn_block_height",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let height = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_current_burnchain_block_height()?;
                Ok((height as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "burn_block_height".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_liquid_supply`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `stx-liquid-supply`.
fn link_stx_liquid_supply_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_liquid_supply",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let supply = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_total_liquid_ustx()?;
                let upper = (supply >> 64) as u64;
                let lower = supply as u64;
                Ok((lower as i64, upper as i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_liquid_supply".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `is_in_regtest`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `is-in-regtest`.
fn link_is_in_regtest_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "is_in_regtest",
            |caller: Caller<'_, ClarityWasmContext>| {
                if caller.data().global_context.database.is_in_regtest() {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "is_in_regtest".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `is_in_mainnet`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `is-in-mainnet`.
fn link_is_in_mainnet_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "is_in_mainnet",
            |caller: Caller<'_, ClarityWasmContext>| {
                if caller.data().global_context.mainnet {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "is_in_mainnet".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `chain_id`, into the Wasm module.
/// This function is called for use of the builtin variable,
/// `chain-id`.
fn link_chain_id_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "chain_id",
            |caller: Caller<'_, ClarityWasmContext>| {
                let chain_id = caller.data().global_context.chain_id;
                Ok((chain_id as i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "chain_id".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `enter_as_contract`, into the Wasm module.
/// This function is called before processing the inner-expression of
/// `as-contract`.
fn link_enter_as_contract_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "enter_as_contract",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                let contract_principal: PrincipalData = caller
                    .data()
                    .contract_context()
                    .contract_identifier
                    .clone()
                    .into();
                caller.data_mut().push_sender(contract_principal.clone());
                caller.data_mut().push_caller(contract_principal);
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "enter_as_contract".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `exit_as_contract`, into the Wasm module.
/// This function is after before processing the inner-expression of
/// `as-contract`, and is used to restore the caller and sender.
fn link_exit_as_contract_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "exit_as_contract",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().pop_sender()?;
                caller.data_mut().pop_caller()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "exit_as_contract".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_get_balance`, into the Wasm module.
/// This function is called for the clarity expression, `stx-get-balance`.
fn link_stx_get_balance_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_get_balance",
            |mut caller: Caller<'_, ClarityWasmContext>,
             principal_offset: i32,
             principal_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let principal = value_as_principal(&value)?;

                let balance = {
                    let mut snapshot = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_stx_balance_snapshot(principal)?;
                    snapshot.get_available_balance()?
                };
                let high = (balance >> 64) as u64;
                let low = (balance & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_get_balance".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `stx_account`, into the Wasm module.
/// This function is called for the clarity expression, `stx-account`.
fn link_stx_account_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_account",
            |mut caller: Caller<'_, ClarityWasmContext>,
             principal_offset: i32,
             principal_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let principal = value_as_principal(&value)?;

                let account = {
                    let mut snapshot = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_stx_balance_snapshot(principal)?;
                    snapshot.canonical_balance_repr()?
                };
                let v1_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v1_unlock_height();
                let v2_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v2_unlock_height()?;
                let v3_unlock_ht = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_v3_unlock_height()?;

                let locked = account.amount_locked();
                let locked_high = (locked >> 64) as u64;
                let locked_low = (locked & 0xffff_ffff_ffff_ffff) as u64;
                let unlock_height =
                    account.effective_unlock_height(v1_unlock_ht, v2_unlock_ht, v3_unlock_ht);
                let unlocked = account.amount_unlocked();
                let unlocked_high = (unlocked >> 64) as u64;
                let unlocked_low = (unlocked & 0xffff_ffff_ffff_ffff) as u64;

                // Return value is a tuple: `{locked: uint, unlock-height: uint, unlocked: uint}`
                Ok((
                    locked_low,
                    locked_high,
                    unlock_height as i64,
                    0i64,
                    unlocked_low,
                    unlocked_high,
                ))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_account".to_string(),
                e,
            ))
        })
}

fn link_stx_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             amount_lo: i64,
             amount_hi: i64,
             principal_offset: i32,
             principal_length: i32| {
                let amount = (amount_hi as u128) << 64 | ((amount_lo as u64) as u128);

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    principal_offset,
                    principal_length,
                    epoch,
                )?;
                let from = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((0i32, 0i32, StxErrorCodes::NON_POSITIVE_AMOUNT as i64, 0i64));
                }

                if Some(from) != caller.data().sender.as_ref() {
                    return Ok((
                        0i32,
                        0i32,
                        StxErrorCodes::SENDER_IS_NOT_TX_SENDER as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(|e| Error::from(e))?;

                let mut burner_snapshot = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_stx_balance_snapshot(&from)?;
                if !burner_snapshot.can_transfer(amount)? {
                    return Ok((0i32, 0i32, StxErrorCodes::NOT_ENOUGH_BALANCE as i64, 0i64));
                }

                burner_snapshot.debit(amount)?;
                burner_snapshot.save()?;

                caller
                    .data_mut()
                    .global_context
                    .database
                    .decrement_ustx_liquid_supply(amount)?;

                caller
                    .data_mut()
                    .global_context
                    .log_stx_burn(&from, amount)?;
                caller
                    .data_mut()
                    .register_stx_burn_event(from.clone(), amount)?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_burn".to_string(),
                e,
            ))
        })
}

fn link_stx_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "stx_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32,
             memo_offset: i32,
             memo_length: i32| {
                let amount = (amount_hi as u128) << 64 | ((amount_lo as u64) as u128);

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let sender = value_as_principal(&value)?;

                // Read the to principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let recipient = value_as_principal(&value)?;

                // Read the memo from the Wasm memory
                let memo = if memo_length > 0 {
                    let value = read_from_wasm(
                        memory,
                        &mut caller,
                        &TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(memo_length as u32)?,
                        )),
                        memo_offset,
                        memo_length,
                        epoch,
                    )?;
                    value_as_buffer(value)?
                } else {
                    BuffData::empty()
                };

                if amount == 0 {
                    return Ok((0i32, 0i32, StxErrorCodes::NON_POSITIVE_AMOUNT as i64, 0i64));
                }

                if sender == recipient {
                    return Ok((0i32, 0i32, StxErrorCodes::SENDER_IS_RECIPIENT as i64, 0i64));
                }

                if Some(sender) != caller.data().sender.as_ref() {
                    return Ok((
                        0i32,
                        0i32,
                        StxErrorCodes::SENDER_IS_NOT_TX_SENDER as i64,
                        0i64,
                    ));
                }

                // loading sender/recipient principals and balances
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                // loading sender's locked amount and height
                // TODO: this does not count the inner stacks block header load, but arguably,
                // this could be optimized away, so it shouldn't penalize the caller.
                caller
                    .data_mut()
                    .global_context
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(STXBalance::unlocked_and_v1_size as u64)
                    .map_err(|e| Error::from(e))?;

                let mut sender_snapshot = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_stx_balance_snapshot(sender)?;
                if !sender_snapshot.can_transfer(amount)? {
                    return Ok((0i32, 0i32, StxErrorCodes::NOT_ENOUGH_BALANCE as i64, 0i64));
                }

                sender_snapshot.transfer_to(recipient, amount)?;

                caller
                    .data_mut()
                    .global_context
                    .log_stx_transfer(&sender, amount)?;
                caller.data_mut().register_stx_transfer_event(
                    sender.clone(),
                    recipient.clone(),
                    amount,
                    memo,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "stx_transfer".to_string(),
                e,
            ))
        })
}

fn link_ft_get_supply_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_get_supply",
            |mut caller: Caller<'_, ClarityWasmContext>, name_offset: i32, name_length: i32| {
                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                // runtime_cost(ClarityCostFunction::FtSupply, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the token name
                let token_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let supply = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_ft_supply(&contract_identifier, &token_name)?;

                let high = (supply >> 64) as u64;
                let low = (supply & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_get_supply".to_string(),
                e,
            ))
        })
}

fn link_ft_get_balance_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_get_balance",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             owner_offset: i32,
             owner_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBalance, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the owner principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    owner_offset,
                    owner_length,
                    epoch,
                )?;
                let owner = value_as_principal(&value)?;

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(&token_name)
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                let balance = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    owner,
                    Some(&ft_info),
                )?;

                let high = (balance >> 64) as u64;
                let low = (balance & 0xffff_ffff_ffff_ffff) as u64;
                Ok((low, high))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_get_balance".to_string(),
                e,
            ))
        })
}

fn link_ft_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBurn, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = (amount_hi as u128) << 64 | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let burner = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        BurnTokenErrorCodes::NOT_ENOUGH_BALANCE_OR_NON_POSITIVE as i64,
                        0i64,
                    ));
                }

                let burner_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    burner,
                    None,
                )?;

                if amount > burner_bal {
                    return Ok((
                        0i32,
                        0i32,
                        BurnTokenErrorCodes::NOT_ENOUGH_BALANCE_OR_NON_POSITIVE as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .database
                    .checked_decrease_token_supply(
                        &contract_identifier,
                        token_name.as_str(),
                        amount,
                    )?;

                let final_burner_bal = burner_bal - amount;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    burner,
                    final_burner_bal,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_burn_event(
                    burner.clone(),
                    amount,
                    asset_identifier,
                )?;

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.log_token_transfer(
                    burner,
                    &contract_identifier,
                    &token_name,
                    amount,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_burn".to_string(),
                e,
            ))
        })
}

fn link_ft_mint_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_mint",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32| {
                // runtime_cost(ClarityCostFunction::FtBurn, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = (amount_hi as u128) << 64 | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        MintTokenErrorCodes::NON_POSITIVE_AMOUNT as i64,
                        0i64,
                    ));
                }

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(token_name.as_str())
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                caller
                    .data_mut()
                    .global_context
                    .database
                    .checked_increase_token_supply(
                        &contract_identifier,
                        token_name.as_str(),
                        amount,
                        &ft_info,
                    )?;

                let to_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    Some(&ft_info),
                )?;

                // This `expect` is safe because the `checked_increase_token_supply` call above
                // would have failed if the addition would have overflowed.
                let final_to_bal = to_bal
                    .checked_add(amount)
                    .ok_or(Error::Runtime(RuntimeErrorType::ArithmeticOverflow, None))?;

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    final_to_bal,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_mint_event(
                    to_principal.clone(),
                    amount,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_mint".to_string(),
                e,
            ))
        })
}

fn link_ft_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "ft_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             amount_lo: i64,
             amount_hi: i64,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // runtime_cost(ClarityCostFunction::FtTransfer, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let token_name = ClarityName::try_from(name.clone())?;

                // Compute the amount
                let amount = (amount_hi as u128) << 64 | ((amount_lo as u64) as u128);

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let from_principal = value_as_principal(&value)?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                if amount == 0 {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::NON_POSITIVE_AMOUNT as i64,
                        0i64,
                    ));
                }

                if from_principal == to_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::SENDER_IS_RECIPIENT as i64,
                        0i64,
                    ));
                }

                let ft_info = caller
                    .data()
                    .contract_context()
                    .meta_ft
                    .get(&token_name)
                    .ok_or(CheckErrors::NoSuchFT(token_name.to_string()))?
                    .clone();

                let from_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    from_principal,
                    Some(&ft_info),
                )?;

                if from_bal < amount {
                    return Ok((
                        0i32,
                        0i32,
                        TransferTokenErrorCodes::NOT_ENOUGH_BALANCE as i64,
                        0i64,
                    ));
                }

                let final_from_bal = from_bal - amount;

                let to_bal = caller.data_mut().global_context.database.get_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    Some(&ft_info),
                )?;

                let final_to_bal = to_bal
                    .checked_add(amount)
                    .ok_or(RuntimeErrorType::ArithmeticOverflow)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::UIntType.size()? as u64)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    &token_name,
                    from_principal,
                    final_from_bal,
                )?;
                caller.data_mut().global_context.database.set_ft_balance(
                    &contract_identifier,
                    token_name.as_str(),
                    to_principal,
                    final_to_bal,
                )?;

                caller.data_mut().global_context.log_token_transfer(
                    from_principal,
                    &contract_identifier,
                    &token_name,
                    amount,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier: contract_identifier.clone(),
                    asset_name: token_name.clone(),
                };
                caller.data_mut().register_ft_transfer_event(
                    from_principal.clone(),
                    to_principal.clone(),
                    amount,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 1i32, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "ft_transfer".to_string(),
                e,
            ))
        })
}

fn link_nft_get_owner_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_get_owner",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                let _asset_size = asset.serialized_size()? as u64;

                // runtime_cost(ClarityCostFunction::NftOwner, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Ok(owner) => {
                        // Write the principal to the return buffer
                        let memory = caller
                            .get_export("memory")
                            .and_then(|export| export.into_memory())
                            .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                        let (_, bytes_written) = write_to_wasm(
                            caller,
                            memory,
                            &TypeSignature::PrincipalType,
                            return_offset,
                            return_offset,
                            &Value::Principal(owner),
                            false,
                        )?;

                        Ok((1i32, return_offset, bytes_written))
                    }
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => Ok((0i32, 0i32, 0i32)),
                    Err(e) => Err(e)?,
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_get_owner".to_string(),
                e,
            ))
        })
}

fn link_nft_burn_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_burn",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             sender_offset: i32,
             sender_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let sender_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;

                // runtime_cost(ClarityCostFunction::NftBurn, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                let owner = match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => {
                        return Ok((0i32, 0i32, BurnAssetErrorCodes::DOES_NOT_EXIST as i64, 0i64));
                    }
                    Ok(owner) => Ok(owner),
                    Err(e) => Err(e),
                }?;

                if &owner != sender_principal {
                    return Ok((0i32, 0i32, BurnAssetErrorCodes::NOT_OWNED_BY as i64, 0i64));
                }

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.database.burn_nft(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                    &epoch,
                )?;

                caller.data_mut().global_context.log_asset_transfer(
                    sender_principal,
                    &contract_identifier,
                    &asset_name,
                    asset.clone(),
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name: asset_name.clone(),
                };
                caller.data_mut().register_nft_burn_event(
                    sender_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_burn".to_string(),
                e,
            ))
        })
}

fn link_nft_mint_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_mint",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;
                // runtime_cost(ClarityCostFunction::NftMint, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => Ok(()),
                    Ok(_owner) => {
                        return Ok((0i32, 0i32, MintAssetErrorCodes::ALREADY_EXIST as i64, 0i64))
                    }
                    Err(e) => Err(e),
                }?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.database.set_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    to_principal,
                    expected_asset_type,
                    &epoch,
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name: asset_name.clone(),
                };
                caller.data_mut().register_nft_mint_event(
                    to_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_mint".to_string(),
                e,
            ))
        })
}

fn link_nft_transfer_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "nft_transfer",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut asset_offset: i32,
             mut asset_length: i32,
             sender_offset: i32,
             sender_length: i32,
             recipient_offset: i32,
             recipient_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let contract_identifier =
                    caller.data().contract_context().contract_identifier.clone();

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the token name
                let name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let asset_name = ClarityName::try_from(name.clone())?;

                let nft_metadata = caller
                    .data()
                    .contract_context()
                    .meta_nft
                    .get(&asset_name)
                    .ok_or(CheckErrors::NoSuchNFT(asset_name.to_string()))?
                    .clone();

                let expected_asset_type = &nft_metadata.key_type;

                // Read in the NFT identifier from the Wasm memory
                if is_in_memory_type(expected_asset_type) {
                    (asset_offset, asset_length) =
                        read_indirect_offset_and_length(memory, &mut caller, asset_offset)?;
                }
                let asset = read_from_wasm(
                    memory,
                    &mut caller,
                    expected_asset_type,
                    asset_offset,
                    asset_length,
                    epoch,
                )?;

                // Read the sender principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    sender_offset,
                    sender_length,
                    epoch,
                )?;
                let from_principal = value_as_principal(&value)?;

                // Read the recipient principal from the Wasm memory
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    recipient_offset,
                    recipient_length,
                    epoch,
                )?;
                let to_principal = value_as_principal(&value)?;

                let asset_size = asset.serialized_size()? as u64;
                // runtime_cost(ClarityCostFunction::NftTransfer, env, asset_size)?;

                if !expected_asset_type.admits(&caller.data().global_context.epoch_id, &asset)? {
                    return Err(
                        CheckErrors::TypeValueError(expected_asset_type.clone(), asset).into(),
                    );
                }

                if from_principal == to_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferAssetErrorCodes::SENDER_IS_RECIPIENT as i64,
                        0i64,
                    ));
                }

                let current_owner = match caller.data_mut().global_context.database.get_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    expected_asset_type,
                ) {
                    Ok(owner) => Ok(owner),
                    Err(Error::Runtime(RuntimeErrorType::NoSuchToken, _)) => {
                        return Ok((
                            0i32,
                            0i32,
                            TransferAssetErrorCodes::DOES_NOT_EXIST as i64,
                            0i64,
                        ))
                    }
                    Err(e) => Err(e),
                }?;

                if current_owner != *from_principal {
                    return Ok((
                        0i32,
                        0i32,
                        TransferAssetErrorCodes::NOT_OWNED_BY as i64,
                        0i64,
                    ));
                }

                caller
                    .data_mut()
                    .global_context
                    .add_memory(TypeSignature::PrincipalType.size()? as u64)
                    .map_err(|e| Error::from(e))?;
                caller
                    .data_mut()
                    .global_context
                    .add_memory(asset_size)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.database.set_nft_owner(
                    &contract_identifier,
                    asset_name.as_str(),
                    &asset,
                    to_principal,
                    expected_asset_type,
                    &epoch,
                )?;

                caller.data_mut().global_context.log_asset_transfer(
                    from_principal,
                    &contract_identifier,
                    &asset_name,
                    asset.clone(),
                )?;

                let asset_identifier = AssetIdentifier {
                    contract_identifier,
                    asset_name,
                };
                caller.data_mut().register_nft_transfer_event(
                    from_principal.clone(),
                    to_principal.clone(),
                    asset,
                    asset_identifier,
                )?;

                // (ok true)
                Ok((1i32, 132, 0i64, 0i64))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "nft_transfer".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_get`, into the Wasm module.
/// This function is called for the `map-get?` expression.
fn link_map_get_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_get",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the metadata for this map
                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(CheckErrors::NoSuchMap(map_name.to_string()))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                let result = caller
                    .data_mut()
                    .global_context
                    .database
                    .fetch_entry_with_size(&contract, &map_name, &key, &data_types, &epoch);

                let _result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::FetchEntry, env, result_size)?;

                let value = result.map(|data| data.value)?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let ty = TypeSignature::OptionalType(Box::new(data_types.value_type));
                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    return_offset,
                    return_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_get".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_set`, into the Wasm module.
/// This function is called for the `map-set` expression.
fn link_map_set_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_set",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // Store the value in the map in the global context
                let result = caller.data_mut().global_context.database.set_entry(
                    &contract,
                    map_name.as_str(),
                    key,
                    value,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(|e| Error::from(e))?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_set".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_insert`, into the Wasm module.
/// This function is called for the `map-insert` expression.
fn link_map_insert_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_insert",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32,
             mut value_offset: i32,
             mut value_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Read in the value from the Wasm memory
                if is_in_memory_type(&data_types.value_type) {
                    (value_offset, value_length) =
                        read_indirect_offset_and_length(memory, &mut caller, value_offset)?;
                }
                let value = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.value_type,
                    value_offset,
                    value_length,
                    epoch,
                )?;

                // Insert the value into the map
                let result = caller.data_mut().global_context.database.insert_entry(
                    &contract,
                    map_name.as_str(),
                    key,
                    value,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(|e| Error::from(e))?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_insert".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `map_delete`, into the Wasm module.
/// This function is called for the `map-delete` expression.
fn link_map_delete_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "map_delete",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             mut key_offset: i32,
             mut key_length: i32| {
                if caller.data().global_context.is_read_only() {
                    return Err(CheckErrors::WriteAttemptedInReadOnly.into());
                }

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Retrieve the map name
                let map_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                let contract = caller.data().contract_context().contract_identifier.clone();
                let epoch = caller.data_mut().global_context.epoch_id;

                let data_types = caller
                    .data()
                    .contract_context()
                    .meta_data_map
                    .get(map_name.as_str())
                    .ok_or(Error::Unchecked(CheckErrors::NoSuchMap(
                        map_name.to_string(),
                    )))?
                    .clone();

                // Read in the key from the Wasm memory
                if is_in_memory_type(&data_types.key_type) {
                    (key_offset, key_length) =
                        read_indirect_offset_and_length(memory, &mut caller, key_offset)?;
                }
                let key = read_from_wasm(
                    memory,
                    &mut caller,
                    &data_types.key_type,
                    key_offset,
                    key_length,
                    epoch,
                )?;

                // Delete the key from the map in the global context
                let result = caller.data_mut().global_context.database.delete_entry(
                    &contract,
                    map_name.as_str(),
                    &key,
                    &data_types,
                    &epoch,
                );

                let result_size = match &result {
                    Ok(data) => data.serialized_byte_len,
                    Err(_e) => (data_types.value_type.size()? + data_types.key_type.size()?) as u64,
                };

                // runtime_cost(ClarityCostFunction::SetEntry, env, result_size)?;

                caller
                    .data_mut()
                    .global_context
                    .add_memory(result_size)
                    .map_err(|e| Error::from(e))?;

                let value = result.map(|data| data.value)?;
                if let Value::Bool(true) = value {
                    Ok(1i32)
                } else {
                    Ok(0i32)
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "map_delete".to_string(),
                e,
            ))
        })
}

fn check_height_valid(
    caller: &mut Caller<'_, ClarityWasmContext>,
    memory: Memory,
    height_lo: i64,
    height_hi: i64,
    return_offset: i32,
) -> Result<Option<u32>, Error> {
    let height = (height_hi as u128) << 64 | ((height_lo as u64) as u128);

    let height_value = match u32::try_from(height) {
        Ok(result) => result,
        _ => {
            // Write a 0 to the return buffer for `none`
            write_to_wasm(
                caller,
                memory,
                &TypeSignature::BoolType,
                return_offset,
                return_offset + get_type_size(&TypeSignature::BoolType),
                &Value::Bool(false),
                true,
            )?;
            return Ok(None);
        }
    };

    let current_block_height = caller
        .data_mut()
        .global_context
        .database
        .get_current_block_height();
    if height_value >= current_block_height {
        // Write a 0 to the return buffer for `none`
        write_to_wasm(
            caller,
            memory,
            &TypeSignature::BoolType,
            return_offset,
            return_offset + get_type_size(&TypeSignature::BoolType),
            &Value::Bool(false),
            true,
        )?;
        return Ok(None);
    }
    Ok(Some(height_value))
}

/// Link host interface function, `get_block_info_time`, into the Wasm module.
/// This function is called for the `get-block-info? time` expression.
fn link_get_block_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_time(height_value)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_vrf_seed`, into the Wasm module.
/// This function is called for the `get-block-info? vrf-seed` expression.
fn link_get_block_info_vrf_seed_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_vrf_seed_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let vrf_seed = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_vrf_seed(height_value)?;
                    let data = vrf_seed.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_vrf_seed_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? header-hash` expression.
fn link_get_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_header_hash(height_value)?;
                    let data = header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_burnchain_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? burnchain-header-hash` expression.
fn link_get_block_info_burnchain_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_burnchain_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let burnchain_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burnchain_block_header_hash(height_value)?;
                    let data = burnchain_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_burnchain_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_id_header_hash`, into the Wasm module.
/// This function is called for the `get-block-info? id-header-hash` expression.
fn link_get_block_info_identity_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_identity_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let id_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_index_block_header_hash(height_value)?;
                    let data = id_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_identity_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_address`, into the Wasm module.
/// This function is called for the `get-block-info? miner-address` expression.
fn link_get_block_info_miner_address_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_address_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let miner_address = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_address(height_value)?;
                    let (result, result_ty) =
                        (Value::from(miner_address), TypeSignature::PrincipalType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_address_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_spend_winner`, into the Wasm module.
/// This function is called for the `get-block-info? miner-spend-winner` expression.
fn link_get_block_info_miner_spend_winner_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_spend_winner_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let winner_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_winner(height_value)?;
                    let (result, result_ty) = (Value::UInt(winner_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_spend_winner_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_miner_spend_total`, into the Wasm module.
/// This function is called for the `get-block-info? miner-spend-total` expression.
fn link_get_block_info_miner_spend_total_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_miner_spend_total_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let total_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_total(height_value)?;
                    let (result, result_ty) = (Value::UInt(total_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_miner_spend_total_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_block_info_block_reward`, into the Wasm module.
/// This function is called for the `get-block-info? block-reward` expression.
fn link_get_block_info_block_reward_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_block_info_block_reward_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_reward_opt = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_reward(height_value)?;
                    let (result, result_ty) = (
                        match block_reward_opt {
                            Some(x) => Value::UInt(x),
                            None => {
                                // Write a 0 to the return buffer for `none`
                                write_to_wasm(
                                    &mut caller,
                                    memory,
                                    &TypeSignature::BoolType,
                                    return_offset,
                                    return_offset + get_type_size(&TypeSignature::BoolType),
                                    &Value::Bool(false),
                                    true,
                                )?;
                                return Ok(());
                            }
                        },
                        TypeSignature::UIntType,
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_block_info_block_reward_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_burn_block_info_header_hash_property`, into the Wasm module.
/// This function is called for the `get-burn-block-info? header-hash` expression.
fn link_get_burn_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_burn_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
                let height = (height_hi as u128) << 64 | ((height_lo as u64) as u128);

                // Note: we assume that we will not have a height bigger than u32::MAX.
                let height_value = match u32::try_from(height) {
                    Ok(result) => result,
                    _ => {
                        // Write a 0 to the return buffer for `none`
                        write_to_wasm(
                            &mut caller,
                            memory,
                            &TypeSignature::BoolType,
                            return_offset,
                            return_offset + get_type_size(&TypeSignature::BoolType),
                            &Value::Bool(false),
                            true,
                        )?;
                        return Ok(());
                    }
                };
                let burnchain_header_hash_opt = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_burnchain_block_header_hash_for_burnchain_height(height_value)?;
                let (result, result_ty) = (
                    match burnchain_header_hash_opt {
                        Some(burnchain_header_hash) => {
                            Value::some(Value::Sequence(SequenceData::Buffer(BuffData {
                                data: burnchain_header_hash.as_bytes().to_vec(),
                            })))?
                        }
                        None => Value::none(),
                    },
                    TypeSignature::OptionalType(Box::new(BUFF_32.clone())),
                );

                write_to_wasm(
                    &mut caller,
                    memory,
                    &result_ty,
                    return_offset,
                    return_offset + get_type_size(&result_ty),
                    &result,
                    true,
                )?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_burn_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_burn_block_info_pox_addrs_property`, into the Wasm module.
/// This function is called for the `get-burn-block-info? pox-addrs` expression.
fn link_get_burn_block_info_pox_addrs_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_burn_block_info_pox_addrs_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let height = (height_hi as u128) << 64 | ((height_lo as u64) as u128);

                // Note: we assume that we will not have a height bigger than u32::MAX.
                let height_value = match u32::try_from(height) {
                    Ok(result) => result,
                    _ => {
                        // Write a 0 to the return buffer for `none`
                        write_to_wasm(
                            &mut caller,
                            memory,
                            &TypeSignature::BoolType,
                            return_offset,
                            return_offset + get_type_size(&TypeSignature::BoolType),
                            &Value::Bool(false),
                            true,
                        )?;
                        return Ok(());
                    }
                };

                let pox_addrs_and_payout = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_pox_payout_addrs_for_burnchain_height(height_value)?;
                let addr_ty: TypeSignature = TupleTypeSignature::try_from(vec![
                    ("hashbytes".into(), BUFF_32.clone()),
                    ("version".into(), BUFF_1.clone()),
                ])?
                .into();
                let addrs_ty = TypeSignature::list_of(addr_ty.clone(), 2)?;
                let tuple_ty = TupleTypeSignature::try_from(vec![
                    ("addrs".into(), addrs_ty),
                    ("payout".into(), TypeSignature::UIntType),
                ])?;
                let value = match pox_addrs_and_payout {
                    Some((addrs, payout)) => {
                        Value::some(Value::Tuple(TupleData::from_data(vec![
                            (
                                "addrs".into(),
                                Value::list_with_type(
                                    &caller.data_mut().global_context.epoch_id,
                                    addrs.into_iter().map(Value::Tuple).collect(),
                                    ListTypeData::new_list(addr_ty, 2)?,
                                )?,
                            ),
                            ("payout".into(), Value::UInt(payout)),
                        ])?))?
                    }
                    None => Value::none(),
                };
                let ty = TypeSignature::OptionalType(Box::new(tuple_ty.into()));

                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    return_offset,
                    return_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_burn_block_info_pox_addrs_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_time`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? id-header-hash` expression.
fn link_get_stacks_block_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Get the memory from the caller
                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_time(height_value)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_header_hash`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? header-hash` expression.
fn link_get_stacks_block_info_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Get the memory from the caller
                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_header_hash(height_value)?;
                    let data = header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_stacks_block_info_identity_header_hash_`, into the Wasm module.
/// This function is called for the `get-stacks-block-info? time` expression.
fn link_get_stacks_block_info_identity_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_stacks_block_info_identity_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let id_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_index_block_header_hash(height_value)?;
                    let data = id_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_stacks_block_info_identity_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_burnchain_header_hash`, into the Wasm module.
/// This function is called for the `get-tenure-info? burnchain-header-hash` expression.
fn link_get_tenure_info_burnchain_header_hash_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_burnchain_header_hash_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let burnchain_header_hash = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burnchain_block_header_hash(height_value)?;
                    let data = burnchain_header_hash.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_burnchain_header_hash_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_address`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-address` expression.
fn link_get_tenure_info_miner_address_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_address_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let miner_address = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_address(height_value)?;
                    let (result, result_ty) =
                        (Value::from(miner_address), TypeSignature::PrincipalType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_address_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_time`, into the Wasm module.
/// This function is called for the `get-tenure-info? time` expression.
fn link_get_tenure_info_time_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_time_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_time = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_burn_block_time(height_value, None)?;
                    let (result, result_ty) =
                        (Value::UInt(block_time as u128), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_time_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_vrf_seed_property`, into the Wasm module.
/// This function is called for the `get-tenure-info? vrf-seed` expression.
fn link_get_tenure_info_vrf_seed_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_vrf_seed_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let vrf_seed = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_vrf_seed(height_value)?;
                    let data = vrf_seed.as_bytes().to_vec();
                    let len = data.len() as u32;
                    let (result, result_ty) = (
                        Value::Sequence(SequenceData::Buffer(BuffData { data })),
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(
                            BufferLength::try_from(len)?,
                        )),
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_vrf_seed_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_block_reward`, into the Wasm module.
/// This function is called for the `get-tenure-info? block-reward` expression.
fn link_get_tenure_info_block_reward_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_block_reward_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let block_reward_opt = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_block_reward(height_value)?;
                    let (result, result_ty) = (
                        match block_reward_opt {
                            Some(x) => Value::UInt(x),
                            None => {
                                // Write a 0 to the return buffer for `none`
                                write_to_wasm(
                                    &mut caller,
                                    memory,
                                    &TypeSignature::BoolType,
                                    return_offset,
                                    return_offset + get_type_size(&TypeSignature::BoolType),
                                    &Value::Bool(false),
                                    true,
                                )?;
                                return Ok(());
                            }
                        },
                        TypeSignature::UIntType,
                    );
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_block_reward_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_spend_total`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-spend-total` expression.
fn link_get_tenure_info_miner_spend_total_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_spend_total_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let total_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_total(height_value)?;
                    let (result, result_ty) = (Value::UInt(total_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_spend_total_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `get_tenure_info_miner_spend_winner`, into the Wasm module.
/// This function is called for the `get-tenure-info? miner-spend-winner` expression.
fn link_get_tenure_info_miner_spend_winner_property_fn(
    linker: &mut Linker<ClarityWasmContext>,
) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "get_tenure_info_miner_spend_winner_property",
            |mut caller: Caller<'_, ClarityWasmContext>,
             height_lo: i64,
             height_hi: i64,
             return_offset: i32,
             _return_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                if let Some(height_value) =
                    check_height_valid(&mut caller, memory, height_lo, height_hi, return_offset)?
                {
                    let winner_spend = caller
                        .data_mut()
                        .global_context
                        .database
                        .get_miner_spend_winner(height_value)?;
                    let (result, result_ty) = (Value::UInt(winner_spend), TypeSignature::UIntType);
                    let ty = TypeSignature::OptionalType(Box::new(result_ty));

                    write_to_wasm(
                        &mut caller,
                        memory,
                        &ty,
                        return_offset,
                        return_offset + get_type_size(&ty),
                        &Value::some(result)?,
                        true,
                    )?;
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "get_tenure_info_miner_spend_winner_property".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `contract_call`, into the Wasm module.
/// This function is called for `contract-call?`s.
fn link_contract_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "contract_call",
            |mut caller: Caller<'_, ClarityWasmContext>,
             trait_name_offset: i32,
             trait_name_length: i32,
             contract_offset: i32,
             contract_length: i32,
             function_offset: i32,
             function_length: i32,
             args_offset: i32,
             _args_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // the second part of the contract_call cost (i.e., the load contract cost)
                //   is checked in `execute_contract`, and the function _application_ cost
                //   is checked in callables::DefinedFunction::execute_apply.
                // runtime_cost(ClarityCostFunction::ContractCall, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the contract identifier from the Wasm memory
                let contract_val = read_from_wasm(
                    memory,
                    &mut caller,
                    &TypeSignature::PrincipalType,
                    contract_offset,
                    contract_length,
                    epoch,
                )?;
                let contract_id = match &contract_val {
                    Value::Principal(PrincipalData::Contract(contract_id)) => contract_id,
                    _ => {
                        return Err(CheckErrors::ContractCallExpectName.into());
                    }
                };

                // Read the function name from the Wasm memory
                let function_name = read_identifier_from_wasm(
                    memory,
                    &mut caller,
                    function_offset,
                    function_length,
                )?;

                // Retrieve the contract context for the contract we're calling
                let contract = caller
                    .data_mut()
                    .global_context
                    .database
                    .get_contract(contract_id)?;

                // Retrieve the function we're calling
                let function = contract
                    .contract_context
                    .functions
                    .get(function_name.as_str())
                    .ok_or(CheckErrors::NoSuchPublicFunction(
                        contract_id.to_string(),
                        function_name.to_string(),
                    ))?;

                let mut args = Vec::new();
                let mut args_sizes = Vec::new();
                let mut arg_offset = args_offset;
                // Read the arguments from the Wasm memory
                for arg_ty in function.get_arg_types() {
                    let arg =
                        read_from_wasm_indirect(memory, &mut caller, arg_ty, arg_offset, epoch)?;
                    args_sizes.push(arg.size()? as u64);
                    args.push(arg);

                    arg_offset += get_type_size(arg_ty);
                }

                let caller_contract: PrincipalData = caller
                    .data()
                    .contract_context()
                    .contract_identifier
                    .clone()
                    .into();
                caller.data_mut().push_caller(caller_contract.clone());

                let mut call_stack = caller.data().call_stack.clone();
                let sender = caller.data().sender.clone();
                let sponsor = caller.data().sponsor.clone();

                let short_circuit_cost = caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .short_circuit_contract_call(
                        contract_id,
                        &ClarityName::try_from(function_name.clone())?,
                        &args_sizes,
                    )?;

                let mut env = Environment {
                    global_context: caller.data_mut().global_context,
                    contract_context: &contract.contract_context,
                    call_stack: &mut call_stack,
                    sender,
                    caller: Some(caller_contract),
                    sponsor,
                };

                let result = if short_circuit_cost {
                    env.run_free(|free_env| {
                        free_env.execute_contract_from_wasm(contract_id, &function_name, &args)
                    })
                } else {
                    env.execute_contract_from_wasm(contract_id, &function_name, &args)
                }?;

                // Write the result to the return buffer
                let return_ty = if trait_name_length == 0 {
                    // This is a direct call
                    function.get_return_type().as_ref()
                } else {
                    // This is a dynamic call
                    let trait_name = read_identifier_from_wasm(
                        memory,
                        &mut caller,
                        trait_name_offset,
                        trait_name_length,
                    )?;
                    contract
                        .contract_context
                        .defined_traits
                        .get(trait_name.as_str())
                        .and_then(|trait_functions| trait_functions.get(function_name.as_str()))
                        .map(|f_ty| &f_ty.returns)
                }
                .ok_or(CheckErrors::DefineFunctionBadSignature)?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                write_to_wasm(
                    &mut caller,
                    memory,
                    return_ty,
                    return_offset,
                    return_offset + get_type_size(return_ty),
                    &result,
                    false,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "contract_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `begin_public_call`, into the Wasm module.
/// This function is called before a local call to a public function.
fn link_begin_public_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "begin_public_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.begin();
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "begin_public_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `begin_read_only_call`, into the Wasm module.
/// This function is called before a local call to a public function.
fn link_begin_read_only_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "begin_read_only_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.begin_read_only();
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "begin_read_only_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `commit_call`, into the Wasm module.
/// This function is called after a local call to a public function to commit
/// it's changes into the global context.
fn link_commit_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "commit_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.commit()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "commit_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `roll_back_call`, into the Wasm module.
/// This function is called after a local call to roll back it's changes from
/// the global context. It is called when a public function errors, or a
/// read-only call completes.
fn link_roll_back_call_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "roll_back_call",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                caller.data_mut().global_context.roll_back()?;
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "roll_back_call".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `print`, into the Wasm module.
/// This function is called for all contract print statements (`print`).
fn link_print_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "print",
            |mut caller: Caller<'_, ClarityWasmContext>,
             value_offset: i32,
             _value_length: i32,
             serialized_ty_offset: i32,
             serialized_ty_length: i32| {
                // runtime_cost(ClarityCostFunction::Print, env, input.size())?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let serialized_ty = read_identifier_from_wasm(
                    memory,
                    &mut caller,
                    serialized_ty_offset,
                    serialized_ty_length,
                )?;

                let epoch = caller.data().global_context.epoch_id;
                let version = caller.data().contract_context().get_clarity_version();

                let value_ty = signature_from_string(&serialized_ty, *version, epoch)?;
                let clarity_val =
                    read_from_wasm_indirect(memory, &mut caller, &value_ty, value_offset, epoch)?;

                caller.data_mut().register_print_event(clarity_val)?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("print".to_string(), e)))
}

/// Link host interface function, `enter_at_block`, into the Wasm module.
/// This function is called before evaluating the inner expression of an
/// `at-block` expression.
fn link_enter_at_block_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "enter_at_block",
            |mut caller: Caller<'_, ClarityWasmContext>,
             block_hash_offset: i32,
             block_hash_length: i32| {
                // runtime_cost(ClarityCostFunction::AtBlock, env, 0)?;

                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;
                let epoch = caller.data_mut().global_context.epoch_id;

                let block_hash = read_from_wasm(
                    memory,
                    &mut caller,
                    &BUFF_32,
                    block_hash_offset,
                    block_hash_length,
                    epoch,
                )?;

                let bhh = match block_hash {
                    Value::Sequence(SequenceData::Buffer(BuffData { data })) => {
                        if data.len() != 32 {
                            return Err(RuntimeErrorType::BadBlockHash(data).into());
                        }
                        StacksBlockId::from(data.as_slice())
                    }
                    x => return Err(CheckErrors::TypeValueError(BUFF_32.clone(), x).into()),
                };

                caller
                    .data_mut()
                    .global_context
                    .add_memory(cost_constants::AT_BLOCK_MEMORY)
                    .map_err(|e| Error::from(e))?;

                caller.data_mut().global_context.begin_read_only();

                let prev_bhh = caller
                    .data_mut()
                    .global_context
                    .database
                    .set_block_hash(bhh, false)?;

                caller.data_mut().push_at_block(prev_bhh);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "enter_at_block".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `exit_at_block`, into the Wasm module.
/// This function is called after evaluating the inner expression of an
/// `at-block` expression, resetting the state back to the current block.
fn link_exit_at_block_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "exit_at_block",
            |mut caller: Caller<'_, ClarityWasmContext>| {
                // Pop back to the current block
                let bhh = caller.data_mut().pop_at_block()?;
                caller
                    .data_mut()
                    .global_context
                    .database
                    .set_block_hash(bhh, true)?;

                // Roll back any changes that occurred during the `at-block`
                // expression. This is precautionary, since only read-only
                // operations are allowed during an `at-block` expression.
                caller.data_mut().global_context.roll_back()?;

                caller
                    .data_mut()
                    .global_context
                    .cost_track
                    .drop_memory(cost_constants::AT_BLOCK_MEMORY)?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "exit_at_block".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `keccak256`, into the Wasm module.
/// This function is called for the Clarity expression, `keccak256`.
fn link_keccak256_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "keccak256",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Keccak256Hash::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "keccak256".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `sha512`, into the Wasm module.
/// This function is called for the Clarity expression, `sha512`.
fn link_sha512_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "sha512",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Sha512Sum::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("sha512".to_string(), e)))
}

/// Link host interface function, `sha512_256`, into the Wasm module.
/// This function is called for the Clarity expression, `sha512/256`.
fn link_sha512_256_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "sha512_256",
            |mut caller: Caller<'_, ClarityWasmContext>,
             buffer_offset: i32,
             buffer_length: i32,
             return_offset: i32,
             return_length: i32| {
                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the bytes from the memory
                let bytes =
                    read_bytes_from_wasm(memory, &mut caller, buffer_offset, buffer_length)?;

                let hash = Sha512Trunc256Sum::from_data(&bytes);

                // Write the hash to the return buffer
                memory.write(&mut caller, return_offset as usize, hash.as_bytes())?;

                Ok((return_offset, return_length))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "sha512_256".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `secp256k1_recover`, into the Wasm module.
/// This function is called for the Clarity expression, `secp256k1-recover?`.
fn link_secp256k1_recover_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "secp256k1_recover",
            |mut caller: Caller<'_, ClarityWasmContext>,
             msg_offset: i32,
             msg_length: i32,
             sig_offset: i32,
             sig_length: i32,
             return_offset: i32,
             _return_length: i32| {
                // runtime_cost(ClarityCostFunction::Secp256k1recover, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let ret_ty = TypeSignature::new_response(BUFF_33.clone(), TypeSignature::UIntType)?;
                let repr_size = get_type_size(&ret_ty);

                // Read the message bytes from the memory
                let msg_bytes = read_bytes_from_wasm(memory, &mut caller, msg_offset, msg_length)?;
                // To match the interpreter behavior, if the message is the
                // wrong length, throw a runtime type error.
                if msg_bytes.len() != 32 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_32.clone(),
                        Value::buff_from(msg_bytes)?,
                    )
                    .into());
                }

                // Read the signature bytes from the memory
                let sig_bytes = read_bytes_from_wasm(memory, &mut caller, sig_offset, sig_length)?;
                // To match the interpreter behavior, if the signature is the
                // wrong length, return a Clarity error.
                if sig_bytes.len() != 65 || sig_bytes[64] > 3 {
                    let result = Value::err_uint(2);
                    write_to_wasm(
                        caller,
                        memory,
                        &ret_ty,
                        return_offset,
                        return_offset + repr_size,
                        &result,
                        true,
                    )?;
                    return Ok(());
                }

                let result = match secp256k1_recover(&msg_bytes, &sig_bytes) {
                    Ok(pubkey) => Value::okay(Value::buff_from(pubkey.to_vec()).unwrap()).unwrap(),
                    _ => Value::err_uint(1),
                };

                // Write the result to the return buffer
                write_to_wasm(
                    caller,
                    memory,
                    &ret_ty,
                    return_offset,
                    return_offset + repr_size,
                    &result,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_recover".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `secp256k1_verify`, into the Wasm module.
/// This function is called for the Clarity expression, `secp256k1-verify`.
fn link_secp256k1_verify_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "secp256k1_verify",
            |mut caller: Caller<'_, ClarityWasmContext>,
             msg_offset: i32,
             msg_length: i32,
             sig_offset: i32,
             sig_length: i32,
             pk_offset: i32,
             pk_length: i32| {
                // runtime_cost(ClarityCostFunction::Secp256k1verify, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read the message bytes from the memory
                let msg_bytes = read_bytes_from_wasm(memory, &mut caller, msg_offset, msg_length)?;
                // To match the interpreter behavior, if the message is the
                // wrong length, throw a runtime type error.
                if msg_bytes.len() != 32 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_32.clone(),
                        Value::buff_from(msg_bytes)?,
                    )
                    .into());
                }

                // Read the signature bytes from the memory
                let sig_bytes = read_bytes_from_wasm(memory, &mut caller, sig_offset, sig_length)?;
                // To match the interpreter behavior, if the signature is the
                // wrong length, return a Clarity error.
                if sig_bytes.len() < 64
                    || sig_bytes.len() > 65
                    || sig_bytes.len() == 65 && sig_bytes[64] > 3
                {
                    return Ok(0i32);
                }

                // Read the public-key bytes from the memory
                let pk_bytes = read_bytes_from_wasm(memory, &mut caller, pk_offset, pk_length)?;
                // To match the interpreter behavior, if the public key is the
                // wrong length, throw a runtime type error.
                if pk_bytes.len() != 33 {
                    return Err(CheckErrors::TypeValueError(
                        BUFF_33.clone(),
                        Value::buff_from(pk_bytes)?,
                    )
                    .into());
                }

                Ok(secp256k1_verify(&msg_bytes, &sig_bytes, &pk_bytes).map_or(0i32, |_| 1i32))
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_verify".to_string(),
                e,
            ))
        })
}

/// Link host interface function, `principal_of`, into the Wasm module.
/// This function is called for the Clarity expression, `principal-of?`.
fn link_principal_of_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "principal_of",
            |mut caller: Caller<'_, ClarityWasmContext>,
             key_offset: i32,
             key_length: i32,
             principal_offset: i32| {
                // runtime_cost(ClarityCostFunction::PrincipalOf, env, 0)?;

                // Get the memory from the caller
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Read the public key from the memory
                let key_val = read_from_wasm(
                    memory,
                    &mut caller,
                    &BUFF_33.clone(),
                    key_offset,
                    key_length,
                    epoch,
                )?;

                let pub_key = match key_val {
                    Value::Sequence(SequenceData::Buffer(BuffData { ref data })) => {
                        if data.len() != 33 {
                            return Err(
                                CheckErrors::TypeValueError(BUFF_33.clone(), key_val).into()
                            );
                        }
                        data
                    }
                    _ => return Err(CheckErrors::TypeValueError(BUFF_33.clone(), key_val).into()),
                };

                if let Ok(pub_key) = Secp256k1PublicKey::from_slice(&pub_key) {
                    // Note: Clarity1 had a bug in how the address is computed (issues/2619).
                    // We want to preserve the old behavior unless the version is greater.
                    let addr = if *caller.data().contract_context().get_clarity_version()
                        > ClarityVersion::Clarity1
                    {
                        pubkey_to_address_v2(pub_key, caller.data().global_context.mainnet)?
                    } else {
                        pubkey_to_address_v1(pub_key)?
                    };
                    let principal = addr.to_account_principal();

                    // Write the principal to the return buffer
                    write_to_wasm(
                        &mut caller,
                        memory,
                        &TypeSignature::PrincipalType,
                        principal_offset,
                        principal_offset,
                        &Value::Principal(principal),
                        false,
                    )?;

                    // (ok principal)
                    Ok((
                        1i32,
                        principal_offset,
                        STANDARD_PRINCIPAL_BYTES as i32,
                        0i64,
                        0i64,
                    ))
                } else {
                    // (err u1)
                    Ok((0i32, 0i32, 0i32, 1i64, 0i64))
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "secp256k1_verify".to_string(),
                e,
            ))
        })
}

fn link_save_constant_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "save_constant",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             value_offset: i32,
             _value_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                let epoch = caller.data_mut().global_context.epoch_id;

                // Get constant name from the memory.
                let const_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;
                let cname = ClarityName::from(const_name.as_str());

                // Get constant value type.
                let value_ty = caller
                    .data()
                    .contract_analysis
                    .ok_or(Error::Wasm(WasmError::DefinesNotFound))?
                    .get_variable_type(const_name.as_str())
                    .ok_or(Error::Wasm(WasmError::DefinesNotFound))?;

                let value =
                    read_from_wasm_indirect(memory, &mut caller, value_ty, value_offset, epoch)?;

                // Insert constant name and expression value into a persistent data structure.
                caller
                    .data_mut()
                    .contract_context_mut()?
                    .variables
                    .insert(cname, value);

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "save_constant".to_string(),
                e,
            ))
        })
}

fn link_load_constant_fn(linker: &mut Linker<ClarityWasmContext>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "load_constant",
            |mut caller: Caller<'_, ClarityWasmContext>,
             name_offset: i32,
             name_length: i32,
             value_offset: i32,
             _value_length: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // Read constant name from the memory.
                let const_name =
                    read_identifier_from_wasm(memory, &mut caller, name_offset, name_length)?;

                // Constant value
                let value = caller
                    .data()
                    .contract_context()
                    .variables
                    .get(&ClarityName::from(const_name.as_str()))
                    .ok_or(CheckErrors::UndefinedVariable(const_name.to_string()))?
                    .clone();

                // Constant value type
                let ty = TypeSignature::type_of(&value)?;

                write_to_wasm(
                    &mut caller,
                    memory,
                    &ty,
                    value_offset,
                    value_offset + get_type_size(&ty),
                    &value,
                    true,
                )?;

                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "load_constant".to_string(),
                e,
            ))
        })
}

fn link_skip_list<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap(
            "clarity",
            "skip_list",
            |mut caller: Caller<'_, T>, offset_beg: i32, offset_end: i32| {
                let memory = caller
                    .get_export("memory")
                    .and_then(|export| export.into_memory())
                    .ok_or(Error::Wasm(WasmError::MemoryNotFound))?;

                // we will read the remaining serialized buffer here, and start it with the list type prefix
                let mut serialized_buffer = vec![0u8; (offset_end - offset_beg) as usize + 1];
                serialized_buffer[0] = super::types::serialization::TypePrefix::List as u8;
                memory
                    .read(
                        &mut caller,
                        offset_beg as usize,
                        &mut serialized_buffer[1..],
                    )
                    .map_err(|e| Error::Wasm(WasmError::Runtime(e.into())))?;

                match Value::deserialize_read_count(&mut serialized_buffer.as_slice(), None, false)
                {
                    Ok((_, bytes_read)) => Ok(offset_beg + bytes_read as i32 - 1),
                    Err(_) => Ok(0),
                }
            },
        )
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "skip_list".to_string(),
                e,
            ))
        })
}

/// Link host-interface function, `log`, into the Wasm module.
/// This function is used for debugging the Wasm, and should not be called in
/// production.
fn link_log<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap("", "log", |_: Caller<'_, T>, param: i64| {
            println!("log: {param}");
        })
        .map(|_| ())
        .map_err(|e| Error::Wasm(WasmError::UnableToLinkHostFunction("log".to_string(), e)))
}

/// Link host-interface function, `debug_msg`, into the Wasm module.
/// This function is used for debugging the Wasm, and should not be called in
/// production.
fn link_debug_msg<T>(linker: &mut Linker<T>) -> Result<(), Error> {
    linker
        .func_wrap("", "debug_msg", |_caller: Caller<'_, T>, param: i32| {
            println!("debug messages are currently not supported in cross-contract calls ({param})")
        })
        .map(|_| ())
        .map_err(|e| {
            Error::Wasm(WasmError::UnableToLinkHostFunction(
                "debug_msg".to_string(),
                e,
            ))
        })
}

#[cfg(test)]
mod tests {
    use wasmtime::*;

    use super::*;

    #[test]
    fn test_read_bytes_from_wasm() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 0;
        let bytes = vec![0x01, 0x02, 0x03, 0x04];
        memory
            .write(&mut store, offset, bytes.as_slice())
            .expect("write failed");

        let read = read_bytes_from_wasm(memory, &mut store, offset as i32, bytes.len() as i32)
            .expect("failed to read bytes");
        assert_eq!(read, bytes);
    }

    #[test]
    fn test_read_identifier_from_wasm() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 1;
        let expected = "hello-world";
        memory
            .write(&mut store, offset, expected.as_bytes())
            .expect("write failed");

        let read =
            read_identifier_from_wasm(memory, &mut store, offset as i32, expected.len() as i32)
                .expect("failed to read id");
        assert_eq!(&read, expected);
    }

    #[test]
    fn test_read_from_wasm_indirect_uint() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 2;
        memory
            .write(&mut store, offset, &3i64.to_le_bytes())
            .expect("write failed");
        memory
            .write(&mut store, offset + 8, &0i64.to_le_bytes())
            .expect("write failed");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &&TypeSignature::UIntType,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, Value::UInt(3),);
    }

    #[test]
    fn test_read_from_wasm_indirect_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 3;
        let expected = "hello-world";
        memory
            .write(&mut store, offset + 8, expected.as_bytes())
            .expect("write failed");
        let offset_bytes = (offset as i32 + 8).to_le_bytes();
        memory
            .write(&mut store, offset, &offset_bytes)
            .expect("write failed");
        let length_bytes = (expected.len() as i32).to_le_bytes();
        memory
            .write(&mut store, offset + 4, &length_bytes)
            .expect("write failed");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &TypeSignature::max_string_ascii().unwrap(),
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(
            read,
            Value::string_ascii_from_bytes(expected.as_bytes().to_vec()).unwrap()
        );
    }

    #[test]
    fn test_write_read_wasm_int() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 4;
        let expected = Value::Int(42);
        let expected_ty = TypeSignature::IntType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            16,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_uint() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 5;
        let expected = Value::UInt(1234);
        let expected_ty = TypeSignature::UIntType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            16,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_buffer() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 6;
        let expected = Value::buff_from(vec![0x01, 0x02, 0x03, 0x04]).unwrap();
        let expected_ty = TypeSignature::max_buffer().unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            4,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_string_ascii() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 7;
        let expected =
            Value::string_ascii_from_bytes("Party on, Wayne!".as_bytes().to_vec()).unwrap();
        let expected_ty = TypeSignature::max_string_ascii().unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            16,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_list() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected =
            Value::list_from(vec![Value::UInt(1), Value::UInt(2), Value::UInt(3)]).unwrap();
        let expected_ty = TypeSignature::list_of(TypeSignature::UIntType, 8).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            48,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_list_strings() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::list_from(vec![
            Value::string_ascii_from_bytes("this ".as_bytes().to_vec()).unwrap(),
            Value::string_ascii_from_bytes("should".as_bytes().to_vec()).unwrap(),
            Value::string_ascii_from_bytes("work.".as_bytes().to_vec()).unwrap(),
        ])
        .unwrap();
        let expected_ty = TypeSignature::list_of(
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(16u32).unwrap(),
            ))),
            8,
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            24,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_response_ok() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::okay_true();
        let expected_ty =
            TypeSignature::new_response(TypeSignature::BoolType, TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            24,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_response_err() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::err_uint(123);
        let expected_ty =
            TypeSignature::new_response(TypeSignature::BoolType, TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            24,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_response_ok_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 11;
        let expected =
            Value::okay(Value::string_ascii_from_bytes("okay!!".as_bytes().to_vec()).unwrap())
                .unwrap();
        let expected_ty = TypeSignature::new_response(
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(8u32).unwrap(),
            ))),
            TypeSignature::UIntType,
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 28,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            28,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_response_err_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 12;
        let expected = Value::error(
            Value::string_ascii_from_bytes("it's an error :(".as_bytes().to_vec()).unwrap(),
        )
        .unwrap();
        let expected_ty = TypeSignature::new_response(
            TypeSignature::BoolType,
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(32u32).unwrap(),
            ))),
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            28,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_bool() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 13;
        let expected = Value::Bool(true);
        let expected_ty = TypeSignature::BoolType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 4,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            4,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_optional_none() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::none();
        let expected_ty = TypeSignature::new_option(TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 20,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            20,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_optional_some() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected =
            Value::some(Value::UInt(0x1234_5678_9abc_def0_0fed_cba9_8765_4321u128)).unwrap();
        let expected_ty = TypeSignature::new_option(TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            24,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_optional_some_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::some(
            Value::string_ascii_from_bytes(
                "Some people are like clouds. When they disappear, it's a beautiful day."
                    .as_bytes()
                    .to_vec(),
            )
            .unwrap(),
        )
        .unwrap();
        let expected_ty =
            TypeSignature::new_option(TypeSignature::SequenceType(SequenceSubtype::StringType(
                StringSubtype::ASCII(BufferLength::try_from(80u32).unwrap()),
            )))
            .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            24,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_principal_standard() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Principal(
            PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap(),
        );
        let expected_ty = TypeSignature::PrincipalType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            STANDARD_PRINCIPAL_BYTES as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_principal_contract() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Principal(
            PrincipalData::parse("SPXACZ2NS34QHWCMAK1V2QJK0XB6WM6N5AB7RWYB.hiro-values-award-nft")
                .unwrap(),
        );
        let expected_ty = TypeSignature::PrincipalType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            STANDARD_PRINCIPAL_BYTES as i32 + 21,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_tuple_simple() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Tuple(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(42)),
                ("b".into(), Value::Bool(false)),
                ("another".into(), Value::UInt(1234)),
            ])
            .unwrap(),
        );
        let expected_ty = expected
            .clone()
            .expect_tuple()
            .unwrap()
            .type_signature
            .into();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            36,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_tuple_compound() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "a".into(),
                    Value::list_from(vec![Value::Int(42), Value::Int(-42)]).unwrap(),
                ),
                ("b".into(), Value::Bool(false)),
                (
                    "another".into(),
                    Value::string_ascii_from_bytes("this is a string!".as_bytes().to_vec())
                        .unwrap(),
                ),
            ])
            .unwrap(),
        );
        let expected_ty = expected
            .clone()
            .expect_tuple()
            .unwrap()
            .type_signature
            .into();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 20,
            &expected,
            false,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            20,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    //- Indirect

    #[test]
    fn test_write_read_wasm_indirect_int() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 4;
        let expected = Value::Int(42);
        let expected_ty = TypeSignature::IntType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_uint() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 5;
        let expected = Value::UInt(1234);
        let expected_ty = TypeSignature::UIntType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_buffer() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 6;
        let expected = Value::buff_from(vec![0x01, 0x02, 0x03, 0x04]).unwrap();
        let expected_ty = TypeSignature::max_buffer().unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_string_ascii() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 7;
        let expected =
            Value::string_ascii_from_bytes("Party on, Wayne!".as_bytes().to_vec()).unwrap();
        let expected_ty = TypeSignature::max_string_ascii().unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_list() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected =
            Value::list_from(vec![Value::UInt(1), Value::UInt(2), Value::UInt(3)]).unwrap();
        let expected_ty = TypeSignature::list_of(TypeSignature::UIntType, 8).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_list_strings() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::list_from(vec![
            Value::string_ascii_from_bytes("this ".as_bytes().to_vec()).unwrap(),
            Value::string_ascii_from_bytes("should".as_bytes().to_vec()).unwrap(),
            Value::string_ascii_from_bytes("work.".as_bytes().to_vec()).unwrap(),
        ])
        .unwrap();
        let expected_ty = TypeSignature::list_of(
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(16u32).unwrap(),
            ))),
            8,
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_response_ok() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::okay_true();
        let expected_ty =
            TypeSignature::new_response(TypeSignature::BoolType, TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_response_err() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::err_uint(123);
        let expected_ty =
            TypeSignature::new_response(TypeSignature::BoolType, TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_response_ok_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 11;
        let expected =
            Value::okay(Value::string_ascii_from_bytes("okay!!".as_bytes().to_vec()).unwrap())
                .unwrap();
        let expected_ty = TypeSignature::new_response(
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(8u32).unwrap(),
            ))),
            TypeSignature::UIntType,
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 28,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_response_err_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 12;
        let expected = Value::error(
            Value::string_ascii_from_bytes("it's an error :(".as_bytes().to_vec()).unwrap(),
        )
        .unwrap();
        let expected_ty = TypeSignature::new_response(
            TypeSignature::BoolType,
            TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
                BufferLength::try_from(32u32).unwrap(),
            ))),
        )
        .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_bool() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 13;
        let expected = Value::Bool(true);
        let expected_ty = TypeSignature::BoolType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 4,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_optional_none() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::none();
        let expected_ty = TypeSignature::new_option(TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 20,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_optional_some() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected =
            Value::some(Value::UInt(0x1234_5678_9abc_def0_0fed_cba9_8765_4321u128)).unwrap();
        let expected_ty = TypeSignature::new_option(TypeSignature::UIntType).unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_optional_some_string() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 8;
        let expected = Value::some(
            Value::string_ascii_from_bytes(
                "Some people are like clouds. When they disappear, it's a beautiful day."
                    .as_bytes()
                    .to_vec(),
            )
            .unwrap(),
        )
        .unwrap();
        let expected_ty =
            TypeSignature::new_option(TypeSignature::SequenceType(SequenceSubtype::StringType(
                StringSubtype::ASCII(BufferLength::try_from(80u32).unwrap()),
            )))
            .unwrap();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 24,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_principal_standard() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Principal(
            PrincipalData::parse("ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM").unwrap(),
        );
        let expected_ty = TypeSignature::PrincipalType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_principal_contract() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Principal(
            PrincipalData::parse("SPXACZ2NS34QHWCMAK1V2QJK0XB6WM6N5AB7RWYB.hiro-values-award-nft")
                .unwrap(),
        );
        let expected_ty = TypeSignature::PrincipalType;

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 8,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_tuple_simple() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Tuple(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(42)),
                ("b".into(), Value::Bool(false)),
                ("another".into(), Value::UInt(1234)),
            ])
            .unwrap(),
        );
        let expected_ty = expected
            .clone()
            .expect_tuple()
            .unwrap()
            .type_signature
            .into();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }

    #[test]
    fn test_write_read_wasm_indirect_tuple_compound() {
        let engine = Engine::default();
        let mut store = Store::new(&engine, ());
        let memory =
            Memory::new(&mut store, MemoryType::new(1, None)).expect("failed to create memory");

        let offset = 14;
        let expected = Value::Tuple(
            TupleData::from_data(vec![
                (
                    "a".into(),
                    Value::list_from(vec![Value::Int(42), Value::Int(-42)]).unwrap(),
                ),
                ("b".into(), Value::Bool(false)),
                (
                    "another".into(),
                    Value::string_ascii_from_bytes("this is a string!".as_bytes().to_vec())
                        .unwrap(),
                ),
            ])
            .unwrap(),
        );
        let expected_ty = expected
            .clone()
            .expect_tuple()
            .unwrap()
            .type_signature
            .into();

        write_to_wasm(
            &mut store,
            memory,
            &expected_ty,
            offset as i32,
            offset as i32 + 20,
            &expected,
            true,
        )
        .expect("failed to write bytes");

        let read = read_from_wasm_indirect(
            memory,
            &mut store,
            &expected_ty,
            offset as i32,
            StacksEpochId::latest(),
        )
        .expect("failed to read bytes");
        assert_eq!(read, expected);
    }
}

mod error_mapping {
    use stacks_common::types::StacksEpochId;
    use wasmtime::{AsContextMut, Instance, Trap};

    use super::{
        read_bytes_from_wasm, read_from_wasm_indirect, read_identifier_from_wasm,
        signature_from_string,
    };
    use crate::vm::errors::{CheckErrors, Error, RuntimeErrorType, ShortReturnType, WasmError};
    use crate::vm::types::{OptionalData, ResponseData};
    use crate::vm::{ClarityVersion, Value};

    const LOG2_ERROR_MESSAGE: &str = "log2 must be passed a positive integer";
    const SQRTI_ERROR_MESSAGE: &str = "sqrti must be passed a positive integer";
    const POW_ERROR_MESSAGE: &str = "Power argument to (pow ...) must be a u32 integer";

    /// Represents various error conditions that can occur
    /// during Clarity contract execution
    /// or other Stacks blockchain operations.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ErrorMap {
        /// Indicates that the error is not related to Clarity contract execution.
        NotClarityError = -1,

        /// Represents an arithmetic overflow error in Clarity contract execution.
        /// This occurs when a calculation exceeds the maximum value representable.
        ArithmeticOverflow = 0,

        /// Represents an arithmetic underflow error in Clarity contract execution.
        /// This occurs when a calculation results in a value below the minimum representable value.
        ArithmeticUnderflow = 1,

        /// Indicates an attempt to divide by zero in a Clarity contract.
        DivisionByZero = 2,

        /// Represents an error in calculating the logarithm base 2 in a Clarity contract.
        /// This could occur for negative inputs.
        ArithmeticLog2Error = 3,

        /// Represents an error in calculating the integer square root in a Clarity contract.
        /// This could occur for negative inputs.
        ArithmeticSqrtiError = 4,

        /// Indicates an error in constructing a type, possibly due to invalid parameters.
        BadTypeConstruction = 5,

        /// Represents a deliberate panic in contract execution,
        /// usually triggered by `(unwrap-panic...)` and `(unwrap-err-panic...)`.
        Panic = 6,

        /// Indicates a failure in an assertion that was expected to cause a short return,
        /// usually triggered by `(asserts!...)`.
        ShortReturnAssertionFailure = 7,

        /// Represents an error in exponentiation operations in a Clarity contract.
        /// This could occur for invalid bases or exponents.
        ArithmeticPowError = 8,

        /// Indicates an attempt to use a name that is already in use, possibly for a variable or function.
        NameAlreadyUsed = 9,

        /// Represents a short-return error for an expected value that wraps a Response type.
        /// Usually triggered by `(try!...)`.
        ShortReturnExpectedValueResponse = 10,

        /// Represents a short-return error for an expected value that wraps an Optional type.
        /// Usually triggered by `(try!...)`.
        ShortReturnExpectedValueOptional = 11,

        /// Represents a short-return error for an expected value.
        /// usually triggered by `(unwrap!...)` and `(unwrap-err!...)`.
        ShortReturnExpectedValue = 12,

        /// Indicates an attempt to use a function with the wrong amount of arguments
        ArgumentCountMismatch = 13,

        /// Indicates an attempt to use a function with too few arguments
        ArgumentCountAtLeast = 14,

        /// Indicates an attempt to use a function with too many arguments
        ArgumentCountAtMost = 15,

        /// A catch-all for errors that are not mapped to specific error codes.
        /// This might be used for unexpected or unclassified errors.
        NotMapped = 99,
    }

    impl From<i32> for ErrorMap {
        fn from(error_code: i32) -> Self {
            match error_code {
                -1 => ErrorMap::NotClarityError,
                0 => ErrorMap::ArithmeticOverflow,
                1 => ErrorMap::ArithmeticUnderflow,
                2 => ErrorMap::DivisionByZero,
                3 => ErrorMap::ArithmeticLog2Error,
                4 => ErrorMap::ArithmeticSqrtiError,
                5 => ErrorMap::BadTypeConstruction,
                6 => ErrorMap::Panic,
                7 => ErrorMap::ShortReturnAssertionFailure,
                8 => ErrorMap::ArithmeticPowError,
                9 => ErrorMap::NameAlreadyUsed,
                10 => ErrorMap::ShortReturnExpectedValueResponse,
                11 => ErrorMap::ShortReturnExpectedValueOptional,
                12 => ErrorMap::ShortReturnExpectedValue,
                13 => ErrorMap::ArgumentCountMismatch,
                14 => ErrorMap::ArgumentCountAtLeast,
                15 => ErrorMap::ArgumentCountAtMost,
                _ => ErrorMap::NotMapped,
            }
        }
    }

    pub(crate) fn resolve_error(
        e: wasmtime::Error,
        instance: Instance,
        mut store: impl AsContextMut,
        epoch_id: &StacksEpochId,
        clarity_version: &ClarityVersion,
    ) -> Error {
        if let Some(vm_error) = e.root_cause().downcast_ref::<Error>() {
            // SAFETY:
            //
            // This unsafe operation returns the value of a location pointed by `*mut T`.
            //
            // The purpose of this code is to take the ownership of the `vm_error` value
            // since clarity::vm::errors::Error is not a Clonable type.
            //
            // Converting a `&T` (vm_error) to a `*mut T` doesn't cause any issues here
            // because the reference is not borrowed elsewhere.
            //
            // The replaced `T` value is deallocated after the operation. Therefore, the chosen `T`
            // is a dummy value, solely to satisfy the signature of the replace function
            // and not cause harm when it is deallocated.
            //
            // Specifically, Error::Wasm(WasmError::ModuleNotFound) was selected as the placeholder value.
            return unsafe {
                core::ptr::replace(
                    (vm_error as *const Error) as *mut Error,
                    Error::Wasm(WasmError::ModuleNotFound),
                )
            };
        }

        if let Some(vm_error) = e.root_cause().downcast_ref::<CheckErrors>() {
            // SAFETY:
            //
            // This unsafe operation returns the value of a location pointed by `*mut T`.
            //
            // The purpose of this code is to take the ownership of the `vm_error` value
            // since clarity::vm::errors::Error is not a Clonable type.
            //
            // Converting a `&T` (vm_error) to a `*mut T` doesn't cause any issues here
            // because the reference is not borrowed elsewhere.
            //
            // The replaced `T` value is deallocated after the operation. Therefore, the chosen `T`
            // is a dummy value, solely to satisfy the signature of the replace function
            // and not cause harm when it is deallocated.
            //
            // Specifically, CheckErrors::ExpectedName was selected as the placeholder value.
            return unsafe {
                let err = core::ptr::replace(
                    (vm_error as *const CheckErrors) as *mut CheckErrors,
                    CheckErrors::ExpectedName,
                );

                <CheckErrors as std::convert::Into<Error>>::into(err)
            };
        }

        // Check if the error is caused by
        // an unreachable Wasm trap.
        //
        // In this case, runtime errors are handled
        // by being mapped to the corresponding ClarityWasm Errors.
        if let Some(Trap::UnreachableCodeReached) = e.root_cause().downcast_ref::<Trap>() {
            return from_runtime_error_code(instance, &mut store, e, epoch_id, clarity_version);
        }

        // All other errors are treated as general runtime errors.
        Error::Wasm(WasmError::Runtime(e))
    }

    /// Converts a WebAssembly runtime error code into a Clarity `Error`.
    ///
    /// This function interprets an error code from a WebAssembly runtime execution and
    /// translates it into an appropriate Clarity error type. It handles various categories
    /// of errors including arithmetic errors, short returns, and other runtime issues.
    ///
    /// # Returns
    ///
    /// Returns a Clarity `Error` that corresponds to the runtime error encountered during
    /// WebAssembly execution.
    ///
    fn from_runtime_error_code(
        instance: Instance,
        mut store: impl AsContextMut,
        e: wasmtime::Error,
        epoch_id: &StacksEpochId,
        clarity_version: &ClarityVersion,
    ) -> Error {
        let runtime_error_code = get_global_i32(&instance, &mut store, "runtime-error-code");

        match ErrorMap::from(runtime_error_code) {
            ErrorMap::NotClarityError => Error::Wasm(WasmError::Runtime(e)),
            ErrorMap::ArithmeticOverflow => {
                Error::Runtime(RuntimeErrorType::ArithmeticOverflow, Some(Vec::new()))
            }
            ErrorMap::ArithmeticUnderflow => {
                Error::Runtime(RuntimeErrorType::ArithmeticUnderflow, Some(Vec::new()))
            }
            ErrorMap::DivisionByZero => {
                Error::Runtime(RuntimeErrorType::DivisionByZero, Some(Vec::new()))
            }
            ErrorMap::ArithmeticLog2Error => Error::Runtime(
                RuntimeErrorType::Arithmetic(LOG2_ERROR_MESSAGE.into()),
                Some(Vec::new()),
            ),
            ErrorMap::ArithmeticSqrtiError => Error::Runtime(
                RuntimeErrorType::Arithmetic(SQRTI_ERROR_MESSAGE.into()),
                Some(Vec::new()),
            ),
            ErrorMap::BadTypeConstruction => {
                Error::Runtime(RuntimeErrorType::BadTypeConstruction, Some(Vec::new()))
            }
            ErrorMap::Panic => {
                // TODO: see issue: #531
                // This RuntimeErrorType::UnwrapFailure need to have a proper context.
                Error::Runtime(RuntimeErrorType::UnwrapFailure, Some(Vec::new()))
            }
            ErrorMap::ShortReturnAssertionFailure => {
                let clarity_val =
                    short_return_value(&instance, &mut store, epoch_id, clarity_version);
                Error::ShortReturn(ShortReturnType::AssertionFailed(clarity_val))
            }
            ErrorMap::ArithmeticPowError => Error::Runtime(
                RuntimeErrorType::Arithmetic(POW_ERROR_MESSAGE.into()),
                Some(Vec::new()),
            ),
            ErrorMap::NameAlreadyUsed => {
                let runtime_error_arg_offset =
                    get_global_i32(&instance, &mut store, "runtime-error-arg-offset");
                let runtime_error_arg_len =
                    get_global_i32(&instance, &mut store, "runtime-error-arg-len");

                let memory = instance
                    .get_memory(&mut store, "memory")
                    .unwrap_or_else(|| panic!("Could not find wasm instance memory"));
                let arg_name = read_identifier_from_wasm(
                    memory,
                    &mut store,
                    runtime_error_arg_offset,
                    runtime_error_arg_len,
                )
                .unwrap_or_else(|e| panic!("Could not recover arg_name: {e}"));

                Error::Unchecked(CheckErrors::NameAlreadyUsed(arg_name))
            }
            ErrorMap::ShortReturnExpectedValueResponse => {
                let clarity_val =
                    short_return_value(&instance, &mut store, epoch_id, clarity_version);
                Error::ShortReturn(ShortReturnType::ExpectedValue(Value::Response(
                    ResponseData {
                        committed: false,
                        data: Box::new(clarity_val),
                    },
                )))
            }
            ErrorMap::ShortReturnExpectedValueOptional => Error::ShortReturn(
                ShortReturnType::ExpectedValue(Value::Optional(OptionalData { data: None })),
            ),
            ErrorMap::ShortReturnExpectedValue => {
                let clarity_val =
                    short_return_value(&instance, &mut store, epoch_id, clarity_version);
                Error::ShortReturn(ShortReturnType::ExpectedValue(clarity_val))
            }
            ErrorMap::ArgumentCountMismatch => {
                let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
                Error::Unchecked(CheckErrors::IncorrectArgumentCount(expected, got))
            }
            ErrorMap::ArgumentCountAtLeast => {
                let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
                Error::Unchecked(CheckErrors::RequiresAtLeastArguments(expected, got))
            }
            ErrorMap::ArgumentCountAtMost => {
                let (expected, got) = get_runtime_error_arg_lengths(&instance, &mut store);
                Error::Unchecked(CheckErrors::RequiresAtMostArguments(expected, got))
            }
            _ => panic!("Runtime error code {} not supported", runtime_error_code),
        }
    }

    /// Retrieves the value of a 32-bit integer global variable from a WebAssembly instance.
    ///
    /// This function attempts to fetch a global variable by name from the provided WebAssembly
    /// instance and return its value as an `i32`. It's designed to simplify the process of
    /// reading global variables in WebAssembly modules.
    ///
    /// # Returns
    ///
    /// Returns the value of the global variable as an `i32`.
    ///
    fn get_global_i32(instance: &Instance, store: &mut impl AsContextMut, name: &str) -> i32 {
        instance
            .get_global(&mut *store, name)
            .and_then(|glob| glob.get(store).i32())
            .unwrap_or_else(|| panic!("Could not find ${} global with i32 value", name))
    }

    /// Retrieves the expected and actual argument counts from a byte-encoded string.
    ///
    /// This function interprets a string as a sequence of bytes, where the first 4 bytes
    /// represent the expected number of arguments, and the bytes at positions 16 to 19
    /// represent the actual number of arguments received. It converts these byte sequences
    /// into `usize` values and returns them as a tuple.
    ///
    /// # Returns
    ///
    /// A tuple `(expected, got)` where:
    /// - `expected` is the number of arguments expected.
    /// - `got` is the number of arguments actually received.
    fn extract_expected_and_got(bytes: &[u8]) -> (usize, usize) {
        // Assuming the first 4 bytes represent the expected value
        let expected = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as usize;

        // Assuming the next 4 bytes represent the got value
        let got = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]) as usize;

        (expected, got)
    }

    /// Retrieves and deserializes a Clarity value from WebAssembly memory in the context of a short return.
    ///
    /// This function is used to extract a Clarity value that has been stored in WebAssembly memory
    /// as part of a short return operation. It reads necessary metadata from global variables,
    /// deserializes the type information, and then reads and deserializes the actual value.
    ///
    /// # Returns
    ///
    /// Returns a deserialized Clarity `Value` representing the short return value.
    ///
    fn short_return_value(
        instance: &Instance,
        store: &mut impl AsContextMut,
        epoch_id: &StacksEpochId,
        clarity_version: &ClarityVersion,
    ) -> Value {
        let val_offset = get_global_i32(instance, store, "runtime-error-value-offset");
        let type_ser_offset = get_global_i32(instance, store, "runtime-error-type-ser-offset");
        let type_ser_len = get_global_i32(instance, store, "runtime-error-type-ser-len");

        let memory = instance
            .get_memory(&mut *store, "memory")
            .unwrap_or_else(|| panic!("Could not find wasm instance memory"));

        let type_ser_str = read_identifier_from_wasm(memory, store, type_ser_offset, type_ser_len)
            .unwrap_or_else(|e| panic!("Could not recover stringified type: {}", e));

        let value_ty = signature_from_string(&type_ser_str, *clarity_version, *epoch_id)
            .unwrap_or_else(|e| panic!("Could not recover thrown value: {}", e));

        read_from_wasm_indirect(memory, store, &value_ty, val_offset, *epoch_id)
            .unwrap_or_else(|e| panic!("Could not read thrown value from memory: {}", e))
    }

    /// Retrieves the argument lengths from the runtime error global variables.
    ///
    /// This function reads the global variables `runtime-error-arg-offset` and `runtime-error-arg-len`
    /// from the WebAssembly instance and constructs a string representing the argument lengths.
    ///
    /// # Returns
    ///
    /// A string representing the argument lengths.
    fn get_runtime_error_arg_lengths(
        instance: &Instance,
        store: &mut impl AsContextMut,
    ) -> (usize, usize) {
        let runtime_error_arg_offset = get_global_i32(instance, store, "runtime-error-arg-offset");
        let runtime_error_arg_len = get_global_i32(instance, store, "runtime-error-arg-len");

        let memory = instance
            .get_memory(&mut *store, "memory")
            .unwrap_or_else(|| panic!("Could not find wasm instance memory"));
        let arg_lengths = read_bytes_from_wasm(
            memory,
            store,
            runtime_error_arg_offset,
            runtime_error_arg_len,
        )
        .unwrap_or_else(|e| panic!("Could not recover arg_lengths: {e}"));

        extract_expected_and_got(&arg_lengths)
    }
}
