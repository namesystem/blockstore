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

use std::vec::Drain;

use hashbrown::{HashMap, HashSet};

use crate::vm::ast::errors::ParseResult;
use crate::vm::representations::{PreSymbolicExpression, SymbolicExpression, TraitDefinition};
use crate::vm::types::signatures::FunctionSignature;
use crate::vm::types::{QualifiedContractIdentifier, TraitIdentifier};
use crate::vm::{ClarityName, ClarityVersion};

pub trait BuildASTPass {
    fn run_pass(contract_ast: &mut ContractAST, _version: ClarityVersion) -> ParseResult<()>;
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContractAST {
    pub contract_identifier: QualifiedContractIdentifier,
    pub pre_expressions: Vec<PreSymbolicExpression>,
    pub expressions: Vec<SymbolicExpression>,
    pub top_level_expression_sorting: Option<Vec<usize>>,
    pub referenced_traits: HashMap<ClarityName, TraitDefinition>,
    pub implemented_traits: HashSet<TraitIdentifier>,
    pub wasm_module: Option<Vec<u8>>,
}

impl ContractAST {
    pub fn new(
        contract_identifier: QualifiedContractIdentifier,
        pre_expressions: Vec<PreSymbolicExpression>,
    ) -> ContractAST {
        ContractAST {
            contract_identifier,
            pre_expressions,
            expressions: Vec::new(),
            top_level_expression_sorting: Some(Vec::new()),
            referenced_traits: HashMap::new(),
            implemented_traits: HashSet::new(),
            wasm_module: None,
        }
    }

    pub fn pre_expressions_drain(&mut self) -> PreExpressionsDrain {
        let sorting = self
            .top_level_expression_sorting
            .as_ref()
            .map(|exprs_ids| exprs_ids[..].to_vec());
        PreExpressionsDrain::new(self.pre_expressions.drain(..), sorting)
    }

    pub fn add_implemented_trait(&mut self, trait_identifier: TraitIdentifier) {
        self.implemented_traits.insert(trait_identifier);
    }

    pub fn get_referenced_trait(&self, name: &str) -> Option<&TraitDefinition> {
        self.referenced_traits.get(name)
    }
}

pub struct PreExpressionsDrain {
    pre_expressions: HashMap<usize, PreSymbolicExpression>,
    sorting: Option<Vec<usize>>,
    index: usize,
    len: usize,
}

impl PreExpressionsDrain {
    pub fn new(pre_exprs_drain: Drain<PreSymbolicExpression>, sorting: Option<Vec<usize>>) -> Self {
        let pre_expressions: HashMap<_, _> = pre_exprs_drain.enumerate().collect();

        let sorting = match sorting {
            Some(sorting) if !sorting.is_empty() => Some(sorting),
            _ => None,
        };
        PreExpressionsDrain {
            len: pre_expressions.len(),
            pre_expressions,
            sorting,
            index: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl Iterator for PreExpressionsDrain {
    type Item = PreSymbolicExpression;

    fn next(&mut self) -> Option<PreSymbolicExpression> {
        if self.index >= self.len {
            return None;
        }
        let expr_index = match self.sorting {
            Some(ref indirections) => indirections[self.index],
            None => self.index,
        };
        let result = self.pre_expressions.remove(&expr_index);
        self.index += 1;
        result
    }
}
