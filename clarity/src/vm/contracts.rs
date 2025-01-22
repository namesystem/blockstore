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

use stacks_common::types::StacksEpochId;

use super::analysis::ContractAnalysis;
use super::CallStack;
use crate::vm::ast::ContractAST;
use crate::vm::callables::CallableType;
#[cfg(feature = "clarity-wasm")]
use crate::vm::clarity_wasm::initialize_contract;
use crate::vm::contexts::{ContractContext, Environment, GlobalContext, LocalContext};
use crate::vm::errors::InterpreterResult as Result;
use crate::vm::representations::SymbolicExpression;
use crate::vm::types::{PrincipalData, QualifiedContractIdentifier};
use crate::vm::version::ClarityVersion;
use crate::vm::{apply, eval_all, Value};

#[derive(Serialize, Deserialize)]
pub struct Contract {
    pub contract_context: ContractContext,
}

// AARON: this is an increasingly useless wrapper around a ContractContext struct.
//          will probably be removed soon.
impl Contract {
    pub fn initialize_from_ast(
        contract_identifier: QualifiedContractIdentifier,
        contract: &mut ContractAST,
        contract_analysis: &ContractAnalysis,
        sponsor: Option<PrincipalData>,
        global_context: &mut GlobalContext,
        version: ClarityVersion,
    ) -> Result<Contract> {
        let mut contract_context = ContractContext::new(contract_identifier, version);

        #[cfg(feature = "clarity-wasm")]
        if let Some(wasm_module) = contract.wasm_module.take() {
            contract_context.set_wasm_module(wasm_module);

            // Initialize the contract via the compiled Wasm module
            global_context.execute(|global_context| {
                initialize_contract(
                    global_context,
                    &mut contract_context,
                    sponsor,
                    contract_analysis,
                )
            })?;
        } else {
            // Interpret the contract
            eval_all(
                &contract.expressions,
                &mut contract_context,
                global_context,
                sponsor,
            )?;
        }

        #[cfg(not(feature = "clarity-wasm"))]
        eval_all(
            &contract.expressions,
            &mut contract_context,
            global_context,
            sponsor,
        )?;

        Ok(Contract { contract_context })
    }

    pub fn canonicalize_types(&mut self, epoch: &StacksEpochId) {
        self.contract_context.canonicalize_types(epoch);
    }
}
