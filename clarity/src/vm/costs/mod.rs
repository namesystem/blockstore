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
use std::{cmp, fmt};

use hashbrown::HashMap;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use stacks_common::types::StacksEpochId;

use crate::boot_util::boot_code_id;
use crate::vm::ast::ContractAST;
use crate::vm::contexts::{ContractContext, Environment, GlobalContext, OwnedEnvironment};
use crate::vm::costs::cost_functions::ClarityCostFunction;
use crate::vm::database::clarity_store::NullBackingStore;
use crate::vm::database::ClarityDatabase;
use crate::vm::errors::{Error, InterpreterResult};
use crate::vm::types::signatures::FunctionType::Fixed;
use crate::vm::types::signatures::{FunctionSignature, TupleTypeSignature};
use crate::vm::types::Value::UInt;
use crate::vm::types::{
    FunctionArg, FunctionType, PrincipalData, QualifiedContractIdentifier, TupleData,
    TypeSignature, NONE,
};
use crate::vm::{ast, eval_all, ClarityName, SymbolicExpression, Value};

pub mod constants;
pub mod cost_functions;

type Result<T> = std::result::Result<T, CostErrors>;

pub const CLARITY_MEMORY_LIMIT: u64 = 100 * 1000 * 1000;

// TODO: factor out into a boot lib?
pub const COSTS_1_NAME: &str = "costs";
pub const COSTS_2_NAME: &str = "costs-2";
pub const COSTS_3_NAME: &str = "costs-3";

lazy_static! {
    static ref COST_TUPLE_TYPE_SIGNATURE: TypeSignature = {
        #[allow(clippy::expect_used)]
        TypeSignature::TupleType(
            TupleTypeSignature::try_from(vec![
                ("runtime".into(), TypeSignature::UIntType),
                ("write_length".into(), TypeSignature::UIntType),
                ("write_count".into(), TypeSignature::UIntType),
                ("read_count".into(), TypeSignature::UIntType),
                ("read_length".into(), TypeSignature::UIntType),
            ])
            .expect("BUG: failed to construct type signature for cost tuple"),
        )
    };
}

pub fn runtime_cost<T: TryInto<u64>, C: CostTracker>(
    cost_function: ClarityCostFunction,
    tracker: &mut C,
    input: T,
) -> Result<()> {
    let size: u64 = input.try_into().map_err(|_| CostErrors::CostOverflow)?;
    let cost = tracker.compute_cost(cost_function, &[size])?;

    tracker.add_cost(cost)
}

macro_rules! finally_drop_memory {
    ( $env: expr, $used_mem:expr; $exec:expr ) => {{
        let result = (|| $exec)();
        $env.drop_memory($used_mem)?;
        result
    }};
}

pub fn analysis_typecheck_cost<T: CostTracker>(
    track: &mut T,
    t1: &TypeSignature,
    t2: &TypeSignature,
) -> Result<()> {
    let t1_size = t1.type_size().map_err(|_| CostErrors::CostOverflow)?;
    let t2_size = t2.type_size().map_err(|_| CostErrors::CostOverflow)?;
    let cost = track.compute_cost(
        ClarityCostFunction::AnalysisTypeCheck,
        &[cmp::max(t1_size, t2_size) as u64],
    )?;
    track.add_cost(cost)
}

pub trait MemoryConsumer {
    fn get_memory_use(&self) -> Result<u64>;
}

impl MemoryConsumer for Value {
    fn get_memory_use(&self) -> Result<u64> {
        Ok(self
            .size()
            .map_err(|_| CostErrors::InterpreterFailure)?
            .into())
    }
}

pub trait CostTracker {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> Result<ExecutionCost>;
    fn add_cost(&mut self, cost: ExecutionCost) -> Result<()>;
    fn add_memory(&mut self, memory: u64) -> Result<()>;
    fn drop_memory(&mut self, memory: u64) -> Result<()>;
    fn reset_memory(&mut self);
    /// Check if the given contract-call should be short-circuited.
    ///  If so: this charges the cost to the CostTracker, and return true
    ///  If not: return false
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> Result<bool>;
}

// Don't track!
impl CostTracker for () {
    fn compute_cost(
        &mut self,
        _cost_function: ClarityCostFunction,
        _input: &[u64],
    ) -> std::result::Result<ExecutionCost, CostErrors> {
        Ok(ExecutionCost::ZERO)
    }
    fn add_cost(&mut self, _cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        Ok(())
    }
    fn add_memory(&mut self, _memory: u64) -> std::result::Result<(), CostErrors> {
        Ok(())
    }
    fn drop_memory(&mut self, _memory: u64) -> Result<()> {
        Ok(())
    }
    fn reset_memory(&mut self) {}
    fn short_circuit_contract_call(
        &mut self,
        _contract: &QualifiedContractIdentifier,
        _function: &ClarityName,
        _input: &[u64],
    ) -> Result<bool> {
        Ok(false)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
pub struct ClarityCostFunctionReference {
    pub contract_id: QualifiedContractIdentifier,
    pub function_name: String,
}

impl ::std::fmt::Display for ClarityCostFunctionReference {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "{}.{}", &self.contract_id, &self.function_name)
    }
}

impl ClarityCostFunctionReference {
    fn new(id: QualifiedContractIdentifier, name: String) -> ClarityCostFunctionReference {
        ClarityCostFunctionReference {
            contract_id: id,
            function_name: name,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CostStateSummary {
    pub contract_call_circuits:
        HashMap<(QualifiedContractIdentifier, ClarityName), ClarityCostFunctionReference>,
    pub cost_function_references: HashMap<ClarityCostFunction, ClarityCostFunctionReference>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SerializedCostStateSummary {
    contract_call_circuits: Vec<(
        (QualifiedContractIdentifier, ClarityName),
        ClarityCostFunctionReference,
    )>,
    cost_function_references: Vec<(ClarityCostFunction, ClarityCostFunctionReference)>,
}

impl From<CostStateSummary> for SerializedCostStateSummary {
    fn from(other: CostStateSummary) -> SerializedCostStateSummary {
        let CostStateSummary {
            contract_call_circuits,
            cost_function_references,
        } = other;
        SerializedCostStateSummary {
            contract_call_circuits: contract_call_circuits.into_iter().collect(),
            cost_function_references: cost_function_references.into_iter().collect(),
        }
    }
}

impl From<SerializedCostStateSummary> for CostStateSummary {
    fn from(other: SerializedCostStateSummary) -> CostStateSummary {
        let SerializedCostStateSummary {
            contract_call_circuits,
            cost_function_references,
        } = other;
        CostStateSummary {
            contract_call_circuits: contract_call_circuits.into_iter().collect(),
            cost_function_references: cost_function_references.into_iter().collect(),
        }
    }
}

impl CostStateSummary {
    pub fn empty() -> CostStateSummary {
        CostStateSummary {
            contract_call_circuits: HashMap::new(),
            cost_function_references: HashMap::new(),
        }
    }
}

#[derive(Clone)]
/// This struct holds all of the data required for non-free LimitedCostTracker instances
pub struct TrackerData {
    cost_function_references: HashMap<&'static ClarityCostFunction, ClarityCostFunctionReference>,
    cost_contracts: HashMap<QualifiedContractIdentifier, ContractContext>,
    contract_call_circuits:
        HashMap<(QualifiedContractIdentifier, ClarityName), ClarityCostFunctionReference>,
    total: ExecutionCost,
    limit: ExecutionCost,
    memory: u64,
    memory_limit: u64,
    /// if the cost tracker is non-free, this holds the StacksEpochId that should be used to evaluate
    ///  the Clarity cost functions. If the tracker *is* free, then those functions do not need to be
    ///  evaluated, so no epoch identifier is necessary.
    epoch: StacksEpochId,
    mainnet: bool,
    chain_id: u32,
}

#[derive(Clone)]
#[allow(clippy::large_enum_variant)]
pub enum LimitedCostTracker {
    Limited(TrackerData),
    Free,
}

#[cfg(any(test, feature = "testing"))]
impl LimitedCostTracker {
    pub fn contract_call_circuits(
        &self,
    ) -> HashMap<(QualifiedContractIdentifier, ClarityName), ClarityCostFunctionReference> {
        match self {
            Self::Free => panic!("Cannot get contract call circuits on free tracker"),
            Self::Limited(TrackerData {
                ref contract_call_circuits,
                ..
            }) => contract_call_circuits.clone(),
        }
    }
    pub fn cost_function_references(
        &self,
    ) -> HashMap<&'static ClarityCostFunction, ClarityCostFunctionReference> {
        match self {
            Self::Free => panic!("Cannot get cost function references on free tracker"),
            Self::Limited(TrackerData {
                ref cost_function_references,
                ..
            }) => cost_function_references.clone(),
        }
    }
}

impl fmt::Debug for LimitedCostTracker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Free => f.debug_struct("LimitedCostTracker::Free").finish(),
            Self::Limited(TrackerData {
                total,
                limit,
                memory,
                memory_limit,
                ..
            }) => f
                .debug_struct("LimitedCostTracker")
                .field("total", total)
                .field("limit", limit)
                .field("memory", memory)
                .field("memory_limit", memory_limit)
                .finish(),
        }
    }
}

impl PartialEq for LimitedCostTracker {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Free, Self::Free) => true,
            (Self::Limited(self_data), Self::Limited(other_data)) => {
                self_data.total == other_data.total
                    && other_data.limit == self_data.limit
                    && self_data.memory == other_data.memory
                    && self_data.memory_limit == other_data.memory_limit
            }
            (_, _) => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CostErrors {
    CostComputationFailed(String),
    CostOverflow,
    CostBalanceExceeded(ExecutionCost, ExecutionCost),
    MemoryBalanceExceeded(u64, u64),
    CostContractLoadFailure,
    InterpreterFailure,
    Expect(String),
}

impl CostErrors {
    fn rejectable(&self) -> bool {
        matches!(self, CostErrors::InterpreterFailure | CostErrors::Expect(_))
    }
}

impl fmt::Display for CostErrors {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for CostErrors {}

fn load_state_summary(mainnet: bool, clarity_db: &mut ClarityDatabase) -> Result<CostStateSummary> {
    let cost_voting_contract = boot_code_id("cost-voting", mainnet);

    let clarity_epoch = clarity_db
        .get_clarity_epoch_version()
        .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?;
    let last_processed_at = match clarity_db.get_value(
        "vm-costs::last-processed-at-height",
        &TypeSignature::UIntType,
        &clarity_epoch,
    ) {
        Ok(Some(v)) => u32::try_from(
            v.value
                .expect_u128()
                .map_err(|_| CostErrors::InterpreterFailure)?,
        )
        .map_err(|_| CostErrors::InterpreterFailure)?,
        Ok(None) => return Ok(CostStateSummary::empty()),
        Err(e) => return Err(CostErrors::CostComputationFailed(e.to_string())),
    };

    let metadata_result = clarity_db
        .fetch_metadata_manual::<String>(
            last_processed_at,
            &cost_voting_contract,
            "::state_summary",
        )
        .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?;
    let serialized: SerializedCostStateSummary = match metadata_result {
        Some(serialized) => {
            serde_json::from_str(&serialized).map_err(|_| CostErrors::InterpreterFailure)?
        }
        None => return Ok(CostStateSummary::empty()),
    };
    Ok(CostStateSummary::from(serialized))
}

fn store_state_summary(
    mainnet: bool,
    clarity_db: &mut ClarityDatabase,
    to_store: &CostStateSummary,
) -> Result<()> {
    let block_height = clarity_db.get_current_block_height();
    let cost_voting_contract = boot_code_id("cost-voting", mainnet);
    let epoch = clarity_db
        .get_clarity_epoch_version()
        .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?;
    clarity_db
        .put_value(
            "vm-costs::last-processed-at-height",
            Value::UInt(block_height as u128),
            &epoch,
        )
        .map_err(|_e| CostErrors::CostContractLoadFailure)?;
    let serialized_summary =
        serde_json::to_string(&SerializedCostStateSummary::from(to_store.clone()))
            .map_err(|_| CostErrors::InterpreterFailure)?;
    clarity_db
        .set_metadata(
            &cost_voting_contract,
            "::state_summary",
            &serialized_summary,
        )
        .map_err(|e| CostErrors::Expect(e.to_string()))?;

    Ok(())
}

///
/// This method loads a cost state summary structure from the currently open stacks chain tip
///   In doing so, it reads from the cost-voting contract to find any newly confirmed proposals,
///    checks those proposals for validity, and then applies those changes to the cached set
///    of cost functions.
///
/// `apply_updates` - tells this function to look for any changes in the cost voting contract
///   which would need to be applied. if `false`, just load the last computed cost state in this
///   fork.
///
fn load_cost_functions(
    mainnet: bool,
    clarity_db: &mut ClarityDatabase,
    apply_updates: bool,
) -> Result<CostStateSummary> {
    let clarity_epoch = clarity_db
        .get_clarity_epoch_version()
        .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?;
    let last_processed_count = clarity_db
        .get_value(
            "vm-costs::last_processed_count",
            &TypeSignature::UIntType,
            &clarity_epoch,
        )
        .map_err(|_e| CostErrors::CostContractLoadFailure)?
        .map(|result| result.value)
        .unwrap_or(Value::UInt(0))
        .expect_u128()
        .map_err(|_| CostErrors::InterpreterFailure)?;
    let cost_voting_contract = boot_code_id("cost-voting", mainnet);
    let confirmed_proposals_count = clarity_db
        .lookup_variable_unknown_descriptor(
            &cost_voting_contract,
            "confirmed-proposal-count",
            &clarity_epoch,
        )
        .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?
        .expect_u128()
        .map_err(|_| CostErrors::InterpreterFailure)?;
    debug!("Check cost voting contract";
           "confirmed_proposal_count" => confirmed_proposals_count,
           "last_processed_count" => last_processed_count);

    // we need to process any confirmed proposals in the range [fetch-start, fetch-end)
    let (fetch_start, fetch_end) = (last_processed_count, confirmed_proposals_count);
    let mut state_summary = load_state_summary(mainnet, clarity_db)?;
    if !apply_updates {
        return Ok(state_summary);
    }

    for confirmed_proposal in fetch_start..fetch_end {
        // fetch the proposal data
        let entry = clarity_db
            .fetch_entry_unknown_descriptor(
                &cost_voting_contract,
                "confirmed-proposals",
                &Value::from(
                    TupleData::from_data(vec![(
                        "confirmed-id".into(),
                        Value::UInt(confirmed_proposal),
                    )])
                    .map_err(|_| {
                        CostErrors::Expect("BUG: failed to construct simple tuple".into())
                    })?,
                ),
                &clarity_epoch,
            )
            .map_err(|_| CostErrors::Expect("BUG: Failed querying confirmed-proposals".into()))?
            .expect_optional()
            .map_err(|_| CostErrors::InterpreterFailure)?
            .ok_or_else(|| {
                CostErrors::Expect("BUG: confirmed-proposal-count exceeds stored proposals".into())
            })?
            .expect_tuple()
            .map_err(|_| CostErrors::InterpreterFailure)?;
        let target_contract = match entry
            .get("function-contract")
            .map_err(|_| CostErrors::Expect("BUG: malformed cost proposal tuple".into()))?
            .clone()
            .expect_principal()
            .map_err(|_| CostErrors::InterpreterFailure)?
        {
            PrincipalData::Contract(contract_id) => contract_id,
            _ => {
                warn!("Confirmed cost proposal invalid: function-contract is not a contract principal";
                          "confirmed_proposal_id" => confirmed_proposal);
                continue;
            }
        };
        let target_function = match ClarityName::try_from(
            entry
                .get("function-name")
                .map_err(|_| CostErrors::Expect("BUG: malformed cost proposal tuple".into()))?
                .clone()
                .expect_ascii()
                .map_err(|_| CostErrors::InterpreterFailure)?,
        ) {
            Ok(x) => x,
            Err(_) => {
                warn!("Confirmed cost proposal invalid: function-name is not a valid function name";
                          "confirmed_proposal_id" => confirmed_proposal);
                continue;
            }
        };
        let cost_contract = match entry
            .get("cost-function-contract")
            .map_err(|_| CostErrors::Expect("BUG: malformed cost proposal tuple".into()))?
            .clone()
            .expect_principal()
            .map_err(|_| CostErrors::InterpreterFailure)?
        {
            PrincipalData::Contract(contract_id) => contract_id,
            _ => {
                warn!("Confirmed cost proposal invalid: cost-function-contract is not a contract principal";
                          "confirmed_proposal_id" => confirmed_proposal);
                continue;
            }
        };

        let cost_function = match ClarityName::try_from(
            entry
                .get_owned("cost-function-name")
                .map_err(|_| CostErrors::Expect("BUG: malformed cost proposal tuple".into()))?
                .expect_ascii()
                .map_err(|_| CostErrors::InterpreterFailure)?,
        ) {
            Ok(x) => x,
            Err(_) => {
                warn!("Confirmed cost proposal invalid: cost-function-name is not a valid function name";
                          "confirmed_proposal_id" => confirmed_proposal);
                continue;
            }
        };

        // Here is where we perform the required validity checks for a confirmed proposal:
        //  * Replaced contract-calls _must_ be `define-read-only` _or_ refer to one of the boot code
        //      cost functions
        //  * cost-function contracts must be arithmetic only

        // make sure the contract is "cost contract eligible" via the
        //  arithmetic-checking analysis pass
        let (cost_func_ref, cost_func_type) = match clarity_db
            .load_contract_analysis(&cost_contract)
            .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?
        {
            Some(c) => {
                if !c.is_cost_contract_eligible {
                    warn!("Confirmed cost proposal invalid: cost-function-contract uses non-arithmetic or otherwise illegal operations";
                          "confirmed_proposal_id" => confirmed_proposal,
                          "contract_name" => %cost_contract,
                    );
                    continue;
                }

                if let Some(FunctionType::Fixed(cost_function_type)) = c
                    .read_only_function_types
                    .get(&cost_function)
                    .or_else(|| c.private_function_types.get(&cost_function))
                {
                    if !cost_function_type.returns.eq(&COST_TUPLE_TYPE_SIGNATURE) {
                        warn!("Confirmed cost proposal invalid: cost-function-name does not return a cost tuple";
                              "confirmed_proposal_id" => confirmed_proposal,
                              "contract_name" => %cost_contract,
                              "function_name" => %cost_function,
                              "return_type" => %cost_function_type.returns,
                        );
                        continue;
                    }
                    if !cost_function_type.args.len() == 1
                        || cost_function_type.args[0].signature != TypeSignature::UIntType
                    {
                        warn!("Confirmed cost proposal invalid: cost-function-name args should be length-1 and only uint";
                              "confirmed_proposal_id" => confirmed_proposal,
                              "contract_name" => %cost_contract,
                              "function_name" => %cost_function,
                        );
                        continue;
                    }
                    (
                        ClarityCostFunctionReference {
                            contract_id: cost_contract,
                            function_name: cost_function.to_string(),
                        },
                        cost_function_type.clone(),
                    )
                } else {
                    warn!("Confirmed cost proposal invalid: cost-function-name not defined";
                          "confirmed_proposal_id" => confirmed_proposal,
                          "contract_name" => %cost_contract,
                          "function_name" => %cost_function,
                    );
                    continue;
                }
            }
            None => {
                warn!("Confirmed cost proposal invalid: cost-function-contract is not a published contract";
                      "confirmed_proposal_id" => confirmed_proposal,
                      "contract_name" => %cost_contract,
                );
                continue;
            }
        };

        if target_contract == boot_code_id("costs", mainnet) {
            // refering to one of the boot code cost functions
            let target = match ClarityCostFunction::lookup_by_name(&target_function) {
                Some(ClarityCostFunction::Unimplemented) => {
                    warn!("Attempted vote on unimplemented cost function";
                              "confirmed_proposal_id" => confirmed_proposal,
                              "cost_function" => %target_function);
                    continue;
                }
                Some(cost_func) => cost_func,
                None => {
                    warn!("Confirmed cost proposal invalid: function-name does not reference a Clarity cost function";
                              "confirmed_proposal_id" => confirmed_proposal,
                              "cost_function" => %target_function);
                    continue;
                }
            };
            state_summary
                .cost_function_references
                .insert(target, cost_func_ref);
        } else {
            // referring to a user-defined function
            match clarity_db
                .load_contract_analysis(&target_contract)
                .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?
            {
                Some(c) => {
                    if let Some(Fixed(tf)) = c.read_only_function_types.get(&target_function) {
                        if cost_func_type.args.len() != tf.args.len() {
                            warn!("Confirmed cost proposal invalid: cost-function contains the wrong number of arguments";
                                  "confirmed_proposal_id" => confirmed_proposal,
                                  "target_contract_name" => %target_contract,
                                  "target_function_name" => %target_function,
                            );
                            continue;
                        }
                        for arg in &cost_func_type.args {
                            if arg.signature != TypeSignature::UIntType {
                                warn!("Confirmed cost proposal invalid: contains non uint argument";
                                      "confirmed_proposal_id" => confirmed_proposal,
                                );
                                continue;
                            }
                        }
                    } else {
                        warn!("Confirmed cost proposal invalid: function-name not defined or is not read-only";
                              "confirmed_proposal_id" => confirmed_proposal,
                              "target_contract_name" => %target_contract,
                              "target_function_name" => %target_function,
                        );
                        continue;
                    }
                }
                None => {
                    warn!("Confirmed cost proposal invalid: contract-name not a published contract";
                          "confirmed_proposal_id" => confirmed_proposal,
                          "target_contract_name" => %target_contract,
                    );
                    continue;
                }
            }
            state_summary
                .contract_call_circuits
                .insert((target_contract, target_function), cost_func_ref);
        }
    }
    if confirmed_proposals_count > last_processed_count {
        store_state_summary(mainnet, clarity_db, &state_summary)?;
        clarity_db
            .put_value(
                "vm-costs::last_processed_count",
                Value::UInt(confirmed_proposals_count),
                &clarity_epoch,
            )
            .map_err(|_e| CostErrors::CostContractLoadFailure)?;
    }

    Ok(state_summary)
}

impl LimitedCostTracker {
    pub fn new(
        mainnet: bool,
        chain_id: u32,
        limit: ExecutionCost,
        clarity_db: &mut ClarityDatabase,
        epoch: StacksEpochId,
    ) -> Result<LimitedCostTracker> {
        let mut cost_tracker = TrackerData {
            cost_function_references: HashMap::new(),
            cost_contracts: HashMap::new(),
            contract_call_circuits: HashMap::new(),
            limit,
            memory_limit: CLARITY_MEMORY_LIMIT,
            total: ExecutionCost::ZERO,
            memory: 0,
            epoch,
            mainnet,
            chain_id,
        };
        assert!(clarity_db.is_stack_empty());
        cost_tracker.load_costs(clarity_db, true)?;
        Ok(Self::Limited(cost_tracker))
    }

    pub fn new_mid_block(
        mainnet: bool,
        chain_id: u32,
        limit: ExecutionCost,
        clarity_db: &mut ClarityDatabase,
        epoch: StacksEpochId,
    ) -> Result<LimitedCostTracker> {
        let mut cost_tracker = TrackerData {
            cost_function_references: HashMap::new(),
            cost_contracts: HashMap::new(),
            contract_call_circuits: HashMap::new(),
            limit,
            memory_limit: CLARITY_MEMORY_LIMIT,
            total: ExecutionCost::ZERO,
            memory: 0,
            epoch,
            mainnet,
            chain_id,
        };
        cost_tracker.load_costs(clarity_db, false)?;
        Ok(Self::Limited(cost_tracker))
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn new_max_limit(
        clarity_db: &mut ClarityDatabase,
        epoch: StacksEpochId,
        use_mainnet: bool,
    ) -> Result<LimitedCostTracker> {
        use crate::vm::tests::test_only_mainnet_to_chain_id;
        let chain_id = test_only_mainnet_to_chain_id(use_mainnet);
        assert!(clarity_db.is_stack_empty());
        LimitedCostTracker::new(
            use_mainnet,
            chain_id,
            ExecutionCost::max_value(),
            clarity_db,
            epoch,
        )
    }

    pub fn new_free() -> LimitedCostTracker {
        Self::Free
    }

    fn default_cost_contract_for_epoch(epoch_id: StacksEpochId) -> Result<String> {
        let result = match epoch_id {
            StacksEpochId::Epoch10 => {
                return Err(CostErrors::Expect("Attempted to get default cost functions for Epoch 1.0 where Clarity does not exist".into()));
            }
            StacksEpochId::Epoch20 => COSTS_1_NAME.to_string(),
            StacksEpochId::Epoch2_05 => COSTS_2_NAME.to_string(),
            StacksEpochId::Epoch21
            | StacksEpochId::Epoch22
            | StacksEpochId::Epoch23
            | StacksEpochId::Epoch24
            | StacksEpochId::Epoch25
            | StacksEpochId::Epoch30
            | StacksEpochId::Epoch31 => COSTS_3_NAME.to_string(),
        };
        Ok(result)
    }
}

impl TrackerData {
    // TODO: add tests from mutation testing results #4831
    #[cfg_attr(test, mutants::skip)]
    /// `apply_updates` - tells this function to look for any changes in the cost voting contract
    ///   which would need to be applied. if `false`, just load the last computed cost state in this
    ///   fork.
    fn load_costs(&mut self, clarity_db: &mut ClarityDatabase, apply_updates: bool) -> Result<()> {
        clarity_db.begin();
        let epoch_id = clarity_db
            .get_clarity_epoch_version()
            .map_err(|e| CostErrors::CostComputationFailed(e.to_string()))?;
        let boot_costs_id = boot_code_id(
            &LimitedCostTracker::default_cost_contract_for_epoch(epoch_id)?,
            self.mainnet,
        );

        let CostStateSummary {
            contract_call_circuits,
            mut cost_function_references,
        } = load_cost_functions(self.mainnet, clarity_db, apply_updates).map_err(|e| {
            let result = clarity_db
                .roll_back()
                .map_err(|e| CostErrors::Expect(e.to_string()));
            match result {
                Ok(_) => e,
                Err(rollback_err) => rollback_err,
            }
        })?;

        self.contract_call_circuits = contract_call_circuits;

        let iter = ClarityCostFunction::ALL.iter();
        let iter_len = iter.len();
        let mut cost_contracts = HashMap::with_capacity(iter_len);
        let mut m = HashMap::with_capacity(iter_len);
        for f in iter {
            let cost_function_ref = cost_function_references.remove(f).unwrap_or_else(|| {
                ClarityCostFunctionReference::new(boot_costs_id.clone(), f.get_name())
            });
            if !cost_contracts.contains_key(&cost_function_ref.contract_id) {
                let contract_context = match clarity_db.get_contract(&cost_function_ref.contract_id)
                {
                    Ok(contract) => contract.contract_context,
                    Err(e) => {
                        error!("Failed to load intended Clarity cost contract";
                               "contract" => %cost_function_ref.contract_id,
                               "error" => ?e);
                        clarity_db
                            .roll_back()
                            .map_err(|e| CostErrors::Expect(e.to_string()))?;
                        return Err(CostErrors::CostContractLoadFailure);
                    }
                };
                cost_contracts.insert(cost_function_ref.contract_id.clone(), contract_context);
            }

            m.insert(f, cost_function_ref);
        }

        for (_, circuit_target) in self.contract_call_circuits.iter() {
            if !cost_contracts.contains_key(&circuit_target.contract_id) {
                let contract_context = match clarity_db.get_contract(&circuit_target.contract_id) {
                    Ok(contract) => contract.contract_context,
                    Err(e) => {
                        error!("Failed to load intended Clarity cost contract";
                               "contract" => %boot_costs_id.to_string(),
                               "error" => %format!("{:?}", e));
                        clarity_db
                            .roll_back()
                            .map_err(|e| CostErrors::Expect(e.to_string()))?;
                        return Err(CostErrors::CostContractLoadFailure);
                    }
                };
                cost_contracts.insert(circuit_target.contract_id.clone(), contract_context);
            }
        }

        self.cost_function_references = m;
        self.cost_contracts = cost_contracts;

        if apply_updates {
            clarity_db
                .commit()
                .map_err(|e| CostErrors::Expect(e.to_string()))?;
        } else {
            clarity_db
                .roll_back()
                .map_err(|e| CostErrors::Expect(e.to_string()))?;
        }

        Ok(())
    }
}

impl LimitedCostTracker {
    pub fn get_total(&self) -> ExecutionCost {
        match self {
            Self::Limited(TrackerData { total, .. }) => total.clone(),
            Self::Free => ExecutionCost::ZERO,
        }
    }
    #[allow(clippy::panic)]
    pub fn set_total(&mut self, total: ExecutionCost) {
        // used by the miner to "undo" the cost of a transaction when trying to pack a block.
        match self {
            Self::Limited(ref mut data) => data.total = total,
            Self::Free => panic!("Cannot set total on free tracker"),
        }
    }
    pub fn get_limit(&self) -> ExecutionCost {
        match self {
            Self::Limited(TrackerData { limit, .. }) => limit.clone(),
            Self::Free => ExecutionCost::max_value(),
        }
    }

    pub fn get_memory(&self) -> u64 {
        match self {
            Self::Limited(TrackerData { memory, .. }) => *memory,
            Self::Free => 0,
        }
    }
    pub fn get_memory_limit(&self) -> u64 {
        match self {
            Self::Limited(TrackerData { memory_limit, .. }) => *memory_limit,
            Self::Free => u64::MAX,
        }
    }
}

fn parse_cost(
    cost_function_name: &str,
    eval_result: InterpreterResult<Option<Value>>,
) -> Result<ExecutionCost> {
    match eval_result {
        Ok(Some(Value::Tuple(data))) => {
            let results = (
                data.data_map.get("write_length"),
                data.data_map.get("write_count"),
                data.data_map.get("runtime"),
                data.data_map.get("read_length"),
                data.data_map.get("read_count"),
            );

            match results {
                (
                    Some(UInt(write_length)),
                    Some(UInt(write_count)),
                    Some(UInt(runtime)),
                    Some(UInt(read_length)),
                    Some(UInt(read_count)),
                ) => Ok(ExecutionCost {
                    write_length: (*write_length as u64),
                    write_count: (*write_count as u64),
                    runtime: (*runtime as u64),
                    read_length: (*read_length as u64),
                    read_count: (*read_count as u64),
                }),
                _ => Err(CostErrors::CostComputationFailed(
                    "Execution Cost tuple does not contain only UInts".to_string(),
                )),
            }
        }
        Ok(Some(_)) => Err(CostErrors::CostComputationFailed(
            "Clarity cost function returned something other than a Cost tuple".to_string(),
        )),
        Ok(None) => Err(CostErrors::CostComputationFailed(
            "Clarity cost function returned nothing".to_string(),
        )),
        Err(e) => Err(CostErrors::CostComputationFailed(format!(
            "Error evaluating result of cost function {}: {}",
            cost_function_name, e
        ))),
    }
}

// TODO: add tests from mutation testing results #4832
#[cfg_attr(test, mutants::skip)]
fn compute_cost(
    cost_tracker: &mut TrackerData,
    cost_function_reference: ClarityCostFunctionReference,
    input_sizes: &[u64],
    eval_in_epoch: StacksEpochId,
) -> Result<ExecutionCost> {
    let mainnet = cost_tracker.mainnet;
    let chain_id = cost_tracker.chain_id;
    let mut null_store = NullBackingStore::new();
    let conn = null_store.as_clarity_db();
    let mut global_context = GlobalContext::new(
        mainnet,
        chain_id,
        conn,
        LimitedCostTracker::new_free(),
        eval_in_epoch,
    );

    let cost_contract = cost_tracker
        .cost_contracts
        .get_mut(&cost_function_reference.contract_id)
        .ok_or(CostErrors::CostComputationFailed(format!(
            "CostFunction not found: {cost_function_reference}"
        )))?;

    let mut program = vec![SymbolicExpression::atom(
        cost_function_reference.function_name[..].into(),
    )];

    for input_size in input_sizes.iter() {
        program.push(SymbolicExpression::atom_value(Value::UInt(
            *input_size as u128,
        )));
    }

    let function_invocation = [SymbolicExpression::list(program)];

    let eval_result = eval_all(
        &function_invocation,
        cost_contract,
        &mut global_context,
        None,
    );

    parse_cost(&cost_function_reference.to_string(), eval_result)
}

fn add_cost(s: &mut TrackerData, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
    s.total.add(&cost)?;
    if cfg!(feature = "disable-costs") {
        // Disable check for exceeding the cost limit to allow mining large blocks for profiling purposes.
        return Ok(());
    }
    if s.total.exceeds(&s.limit) {
        Err(CostErrors::CostBalanceExceeded(
            s.total.clone(),
            s.limit.clone(),
        ))
    } else {
        Ok(())
    }
}

fn add_memory(s: &mut TrackerData, memory: u64) -> std::result::Result<(), CostErrors> {
    s.memory = s.memory.cost_overflow_add(memory)?;
    if s.memory > s.memory_limit {
        Err(CostErrors::MemoryBalanceExceeded(s.memory, s.memory_limit))
    } else {
        Ok(())
    }
}

fn drop_memory(s: &mut TrackerData, memory: u64) -> Result<()> {
    s.memory = s
        .memory
        .checked_sub(memory)
        .ok_or_else(|| CostErrors::Expect("Underflowed dropped memory".into()))?;
    Ok(())
}

impl CostTracker for LimitedCostTracker {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> std::result::Result<ExecutionCost, CostErrors> {
        match self {
            Self::Free => {
                // tracker is free, return zero!
                Ok(ExecutionCost::ZERO)
            }
            Self::Limited(ref mut data) => {
                if cost_function == ClarityCostFunction::Unimplemented {
                    return Err(CostErrors::Expect(
                        "Used unimplemented cost function".into(),
                    ));
                }
                let cost_function_ref = data
                    .cost_function_references
                    .get(&cost_function)
                    .ok_or(CostErrors::CostComputationFailed(format!(
                        "CostFunction not defined: {cost_function}"
                    )))?
                    .clone();

                compute_cost(data, cost_function_ref, input, data.epoch)
            }
        }
    }
    fn add_cost(&mut self, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        match self {
            Self::Free => Ok(()),
            Self::Limited(ref mut data) => add_cost(data, cost),
        }
    }
    fn add_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        match self {
            Self::Free => Ok(()),
            Self::Limited(ref mut data) => add_memory(data, memory),
        }
    }
    fn drop_memory(&mut self, memory: u64) -> Result<()> {
        match self {
            Self::Free => Ok(()),
            Self::Limited(ref mut data) => drop_memory(data, memory),
        }
    }
    fn reset_memory(&mut self) {
        match self {
            Self::Free => {}
            Self::Limited(ref mut data) => {
                data.memory = 0;
            }
        }
    }
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> Result<bool> {
        match self {
            Self::Free => {
                // if we're already free, no need to worry about short circuiting contract-calls
                Ok(false)
            }
            Self::Limited(data) => {
                // grr, if HashMap::get didn't require Borrow, we wouldn't need this cloning.
                let lookup_key = (contract.clone(), function.clone());
                if let Some(cost_function) = data.contract_call_circuits.get(&lookup_key).cloned() {
                    compute_cost(data, cost_function, input, data.epoch)?;
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

impl CostTracker for &mut LimitedCostTracker {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> std::result::Result<ExecutionCost, CostErrors> {
        LimitedCostTracker::compute_cost(self, cost_function, input)
    }
    fn add_cost(&mut self, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        LimitedCostTracker::add_cost(self, cost)
    }
    fn add_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        LimitedCostTracker::add_memory(self, memory)
    }
    fn drop_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        LimitedCostTracker::drop_memory(self, memory)
    }
    fn reset_memory(&mut self) {
        LimitedCostTracker::reset_memory(self)
    }
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> Result<bool> {
        LimitedCostTracker::short_circuit_contract_call(self, contract, function, input)
    }
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq, Hash)]
pub struct ExecutionCost {
    pub write_length: u64,
    pub write_count: u64,
    pub read_length: u64,
    pub read_count: u64,
    pub runtime: u64,
}

impl fmt::Display for ExecutionCost {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{\"runtime\": {}, \"write_len\": {}, \"write_cnt\": {}, \"read_len\": {}, \"read_cnt\": {}}}",
               self.runtime, self.write_length, self.write_count, self.read_length, self.read_count)
    }
}

pub trait CostOverflowingMath<T> {
    fn cost_overflow_mul(self, other: T) -> Result<T>;
    fn cost_overflow_add(self, other: T) -> Result<T>;
    fn cost_overflow_sub(self, other: T) -> Result<T>;
    fn cost_overflow_div(self, other: T) -> Result<T>;
}

impl CostOverflowingMath<u64> for u64 {
    fn cost_overflow_mul(self, other: u64) -> Result<u64> {
        self.checked_mul(other).ok_or(CostErrors::CostOverflow)
    }
    fn cost_overflow_add(self, other: u64) -> Result<u64> {
        self.checked_add(other).ok_or(CostErrors::CostOverflow)
    }
    fn cost_overflow_sub(self, other: u64) -> Result<u64> {
        self.checked_sub(other).ok_or(CostErrors::CostOverflow)
    }
    fn cost_overflow_div(self, other: u64) -> Result<u64> {
        self.checked_div(other).ok_or(CostErrors::CostOverflow)
    }
}

impl ExecutionCost {
    pub const ZERO: Self = Self {
        runtime: 0,
        write_length: 0,
        read_count: 0,
        write_count: 0,
        read_length: 0,
    };

    /// Returns the percentage of self consumed in `numerator`'s largest proportion dimension.
    pub fn proportion_largest_dimension(&self, numerator: &ExecutionCost) -> u64 {
        // max() should always return because there are > 0 elements
        #[allow(clippy::expect_used)]
        *[
            numerator.runtime / cmp::max(1, self.runtime / 100),
            numerator.write_length / cmp::max(1, self.write_length / 100),
            numerator.write_count / cmp::max(1, self.write_count / 100),
            numerator.read_length / cmp::max(1, self.read_length / 100),
            numerator.read_count / cmp::max(1, self.read_count / 100),
        ]
        .iter()
        .max()
        .expect("BUG: should find maximum")
    }

    /// Returns the dot product of this execution cost with `resolution`/block_limit
    /// This provides a scalar value representing the cumulative consumption
    /// of `self` in the provided block_limit.
    pub fn proportion_dot_product(&self, block_limit: &ExecutionCost, resolution: u64) -> u64 {
        [
            // each field here is calculating `r * self / limit`, using f64
            //  use MAX(1, block_limit) to guard against divide by zero
            //  use MIN(1, self/block_limit) to guard against self > block_limit
            resolution as f64
                * 1_f64.min(self.runtime as f64 / 1_f64.max(block_limit.runtime as f64)),
            resolution as f64
                * 1_f64.min(self.read_count as f64 / 1_f64.max(block_limit.read_count as f64)),
            resolution as f64
                * 1_f64.min(self.write_count as f64 / 1_f64.max(block_limit.write_count as f64)),
            resolution as f64
                * 1_f64.min(self.read_length as f64 / 1_f64.max(block_limit.read_length as f64)),
            resolution as f64
                * 1_f64.min(self.write_length as f64 / 1_f64.max(block_limit.write_length as f64)),
        ]
        .iter()
        .fold(0, |acc, dim| {
            acc.checked_add(cmp::max(*dim as u64, 1))
                .unwrap_or(u64::MAX)
        })
    }

    pub fn max_value() -> ExecutionCost {
        Self {
            runtime: u64::MAX,
            write_length: u64::MAX,
            read_count: u64::MAX,
            write_count: u64::MAX,
            read_length: u64::MAX,
        }
    }

    pub fn runtime(runtime: u64) -> ExecutionCost {
        Self {
            runtime,
            write_length: 0,
            read_count: 0,
            write_count: 0,
            read_length: 0,
        }
    }

    pub fn add_runtime(&mut self, runtime: u64) -> Result<()> {
        self.runtime = self.runtime.cost_overflow_add(runtime)?;
        Ok(())
    }

    pub fn add(&mut self, other: &ExecutionCost) -> Result<()> {
        self.runtime = self.runtime.cost_overflow_add(other.runtime)?;
        self.read_count = self.read_count.cost_overflow_add(other.read_count)?;
        self.read_length = self.read_length.cost_overflow_add(other.read_length)?;
        self.write_length = self.write_length.cost_overflow_add(other.write_length)?;
        self.write_count = self.write_count.cost_overflow_add(other.write_count)?;
        Ok(())
    }

    pub fn sub(&mut self, other: &ExecutionCost) -> Result<()> {
        self.runtime = self.runtime.cost_overflow_sub(other.runtime)?;
        self.read_count = self.read_count.cost_overflow_sub(other.read_count)?;
        self.read_length = self.read_length.cost_overflow_sub(other.read_length)?;
        self.write_length = self.write_length.cost_overflow_sub(other.write_length)?;
        self.write_count = self.write_count.cost_overflow_sub(other.write_count)?;
        Ok(())
    }

    pub fn multiply(&mut self, times: u64) -> Result<()> {
        self.runtime = self.runtime.cost_overflow_mul(times)?;
        self.read_count = self.read_count.cost_overflow_mul(times)?;
        self.read_length = self.read_length.cost_overflow_mul(times)?;
        self.write_length = self.write_length.cost_overflow_mul(times)?;
        self.write_count = self.write_count.cost_overflow_mul(times)?;
        Ok(())
    }

    pub fn divide(&mut self, divisor: u64) -> Result<()> {
        self.runtime = self.runtime.cost_overflow_div(divisor)?;
        self.read_count = self.read_count.cost_overflow_div(divisor)?;
        self.read_length = self.read_length.cost_overflow_div(divisor)?;
        self.write_length = self.write_length.cost_overflow_div(divisor)?;
        self.write_count = self.write_count.cost_overflow_div(divisor)?;
        Ok(())
    }

    /// Returns whether or not this cost exceeds any dimension of the
    ///  other cost.
    pub fn exceeds(&self, other: &ExecutionCost) -> bool {
        self.runtime > other.runtime
            || self.write_length > other.write_length
            || self.write_count > other.write_count
            || self.read_count > other.read_count
            || self.read_length > other.read_length
    }

    pub fn max_cost(first: ExecutionCost, second: ExecutionCost) -> ExecutionCost {
        Self {
            runtime: first.runtime.max(second.runtime),
            write_length: first.write_length.max(second.write_length),
            write_count: first.write_count.max(second.write_count),
            read_count: first.read_count.max(second.read_count),
            read_length: first.read_length.max(second.read_length),
        }
    }

    pub fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

// ONLY WORKS IF INPUT IS u64
fn int_log2(input: u64) -> Option<u64> {
    63_u32.checked_sub(input.leading_zeros()).map(|floor_log| {
        if input.trailing_zeros() == floor_log {
            u64::from(floor_log)
        } else {
            u64::from(floor_log + 1)
        }
    })
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn test_simple_overflows() {
        assert_eq!(u64::MAX.cost_overflow_add(1), Err(CostErrors::CostOverflow));
        assert_eq!(u64::MAX.cost_overflow_mul(2), Err(CostErrors::CostOverflow));
    }

    #[test]
    fn test_simple_sub() {
        assert_eq!(0u64.cost_overflow_sub(1), Err(CostErrors::CostOverflow));
    }

    #[test]
    fn test_simple_log2s() {
        let inputs = [
            1,
            2,
            4,
            8,
            16,
            31,
            32,
            33,
            39,
            64,
            128,
            2_u64.pow(63),
            u64::MAX,
        ];
        let expected = [0, 1, 2, 3, 4, 5, 5, 6, 6, 6, 7, 63, 64];
        for (input, expected) in inputs.iter().zip(expected.iter()) {
            assert_eq!(int_log2(*input).unwrap(), *expected);
        }
    }
}
