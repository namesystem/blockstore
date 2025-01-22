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

use hashbrown::{HashMap, HashSet};

use crate::vm::ast::errors::{ParseError, ParseErrors, ParseResult};
use crate::vm::ast::types::{BuildASTPass, ContractAST, PreExpressionsDrain};
use crate::vm::functions::define::{DefineFunctions, DefineFunctionsParsed};
use crate::vm::functions::NativeFunctions;
use crate::vm::representations::{
    ClarityName, PreSymbolicExpression, PreSymbolicExpressionType, SymbolicExpression,
    SymbolicExpressionType,
};
use crate::vm::types::{
    PrincipalData, QualifiedContractIdentifier, StandardPrincipalData, TraitIdentifier, Value,
};
use crate::vm::ClarityVersion;

pub struct SugarExpander {
    issuer: StandardPrincipalData,
    defined_traits: HashSet<ClarityName>,
    imported_traits: HashMap<ClarityName, TraitIdentifier>,
}

impl BuildASTPass for SugarExpander {
    fn run_pass(contract_ast: &mut ContractAST, _version: ClarityVersion) -> ParseResult<()> {
        let pass = SugarExpander::new(contract_ast.contract_identifier.issuer.clone());
        pass.run(contract_ast)?;
        Ok(())
    }
}

impl SugarExpander {
    fn new(issuer: StandardPrincipalData) -> Self {
        Self {
            issuer,
            defined_traits: HashSet::new(),
            imported_traits: HashMap::new(),
        }
    }

    pub fn run(&self, contract_ast: &mut ContractAST) -> ParseResult<()> {
        let expressions = self.transform(contract_ast.pre_expressions_drain(), contract_ast)?;
        contract_ast.expressions = expressions;
        Ok(())
    }

    // TODO: add tests from mutation testing results #4830
    #[cfg_attr(test, mutants::skip)]
    pub fn transform(
        &self,
        pre_exprs_iter: PreExpressionsDrain,
        contract_ast: &mut ContractAST,
    ) -> ParseResult<Vec<SymbolicExpression>> {
        let mut expressions: Vec<SymbolicExpression> = Vec::with_capacity(pre_exprs_iter.len());
        #[cfg(feature = "developer-mode")]
        let mut comments = Vec::new();

        for pre_expr in pre_exprs_iter {
            let span = pre_expr.span().clone();
            let mut expr = match pre_expr.pre_expr {
                PreSymbolicExpressionType::AtomValue(content) => {
                    SymbolicExpression::literal_value(content)
                }
                PreSymbolicExpressionType::Atom(content) => SymbolicExpression::atom(content),
                PreSymbolicExpressionType::List(pre_exprs) => {
                    let drain = PreExpressionsDrain::new(pre_exprs.to_vec().drain(..), None);
                    let expression = self.transform(drain, contract_ast)?;
                    SymbolicExpression::list(expression)
                }
                PreSymbolicExpressionType::Tuple(pre_exprs) => {
                    let drain = PreExpressionsDrain::new(pre_exprs.to_vec().drain(..), None);
                    let expression = self.transform(drain, contract_ast)?;
                    let mut pairs = expression
                        .chunks(2)
                        .map(|pair| {
                            let mut l = SymbolicExpression::list(pair.to_vec());
                            if let (Some(first), Some(last)) = (pair.first(), pair.last()) {
                                l.set_span(
                                    first.span().start_line,
                                    first.span().start_column,
                                    last.span().end_line,
                                    last.span().end_column,
                                )
                            }
                            l
                        })
                        .collect::<Vec<_>>();
                    pairs.insert(
                        0,
                        SymbolicExpression::atom(
                            "tuple"
                                .to_string()
                                .try_into()
                                .map_err(|_| ParseErrors::InterpreterFailure)?,
                        ),
                    );
                    SymbolicExpression::list(pairs)
                }
                PreSymbolicExpressionType::SugaredContractIdentifier(contract_name) => {
                    let contract_identifier =
                        QualifiedContractIdentifier::new(self.issuer.clone(), contract_name);
                    SymbolicExpression::literal_value(Value::Principal(PrincipalData::Contract(
                        contract_identifier,
                    )))
                }
                PreSymbolicExpressionType::SugaredFieldIdentifier(contract_name, name) => {
                    let contract_identifier =
                        QualifiedContractIdentifier::new(self.issuer.clone(), contract_name);
                    SymbolicExpression::field(TraitIdentifier {
                        name,
                        contract_identifier,
                    })
                }
                PreSymbolicExpressionType::FieldIdentifier(trait_identifier) => {
                    SymbolicExpression::field(trait_identifier)
                }
                PreSymbolicExpressionType::TraitReference(name) => {
                    if let Some(trait_reference) = contract_ast.get_referenced_trait(&name) {
                        SymbolicExpression::trait_reference(name, trait_reference.clone())
                    } else {
                        return Err(ParseErrors::TraitReferenceUnknown(name.to_string()).into());
                    }
                }
                #[cfg(not(feature = "developer-mode"))]
                PreSymbolicExpressionType::Comment(_) => continue,
                #[cfg(feature = "developer-mode")]
                PreSymbolicExpressionType::Comment(comment) => {
                    if let Some(last_expr) = expressions.last_mut() {
                        // If this comment is on the same line as the last expression attach it
                        if last_expr.span().end_line == span.start_line {
                            last_expr.end_line_comment = Some(comment);
                        } else {
                            // Else, attach it to the next expression
                            comments.push((comment, span));
                        }
                    } else {
                        comments.push((comment, span));
                    }
                    continue;
                }
                PreSymbolicExpressionType::Placeholder(_) => continue,
            };
            // expr.id will be set by the subsequent expression identifier pass.
            expr.copy_span(&span);

            #[cfg(feature = "developer-mode")]
            // If there were comments above this expression, attach them.
            if !comments.is_empty() {
                expr.pre_comments = std::mem::take(&mut comments);
            }

            expressions.push(expr);
        }

        #[cfg(feature = "developer-mode")]
        // If there were comments after the last expression, attach them.
        if !comments.is_empty() {
            if let Some(expr) = expressions.last_mut() {
                expr.post_comments = comments;
            }
        }
        Ok(expressions)
    }
}

#[cfg(test)]
mod test {
    use crate::vm::ast::errors::{ParseError, ParseErrors};
    use crate::vm::ast::sugar_expander::SugarExpander;
    use crate::vm::ast::types::ContractAST;
    use crate::vm::representations::{
        ContractName, PreSymbolicExpression, Span, SymbolicExpression,
    };
    use crate::vm::types::{PrincipalData, QualifiedContractIdentifier, StandardPrincipalData};
    use crate::vm::{ast, Value};

    fn make_pre_atom(
        x: &str,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::atom(x.into());
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_pre_atom_value(
        x: Value,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::atom_value(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_pre_list(
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
        x: Vec<PreSymbolicExpression>,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::list(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_pre_tuple(
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
        x: Vec<PreSymbolicExpression>,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::tuple(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_sugared_contract_identifier(
        x: ContractName,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::sugared_contract_identifier(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_pre_comment(
        comment: String,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> PreSymbolicExpression {
        let mut e = PreSymbolicExpression::comment(comment);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_atom(
        x: &str,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> SymbolicExpression {
        let mut e = SymbolicExpression::atom(x.into());
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_atom_value(
        x: Value,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> SymbolicExpression {
        let mut e = SymbolicExpression::atom_value(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_list(
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
        x: Vec<SymbolicExpression>,
    ) -> SymbolicExpression {
        let mut e = SymbolicExpression::list(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    fn make_literal_value(
        x: Value,
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
    ) -> SymbolicExpression {
        let mut e = SymbolicExpression::literal_value(x);
        e.set_span(start_line, start_column, end_line, end_column);
        e
    }

    #[test]
    fn test_transform_pre_ast() {
        let pre_ast = vec![
            make_pre_atom("z", 1, 1, 1, 1),
            make_pre_list(
                1,
                3,
                6,
                11,
                vec![
                    make_pre_atom("let", 1, 4, 1, 6),
                    make_pre_list(
                        1,
                        8,
                        1,
                        20,
                        vec![
                            make_pre_list(
                                1,
                                9,
                                1,
                                13,
                                vec![
                                    make_pre_atom("x", 1, 10, 1, 10),
                                    make_pre_atom_value(Value::Int(1), 1, 12, 1, 12),
                                ],
                            ),
                            make_pre_list(
                                1,
                                15,
                                1,
                                19,
                                vec![
                                    make_pre_atom("y", 1, 16, 1, 16),
                                    make_pre_atom_value(Value::Int(2), 1, 18, 1, 18),
                                ],
                            ),
                        ],
                    ),
                    make_pre_list(
                        2,
                        5,
                        6,
                        10,
                        vec![
                            make_pre_atom("+", 2, 6, 2, 6),
                            make_pre_atom("x", 2, 8, 2, 8),
                            make_pre_list(
                                4,
                                9,
                                5,
                                16,
                                vec![
                                    make_pre_atom("let", 4, 10, 4, 12),
                                    make_pre_list(
                                        4,
                                        14,
                                        4,
                                        20,
                                        vec![make_pre_list(
                                            4,
                                            15,
                                            4,
                                            19,
                                            vec![
                                                make_pre_atom("x", 4, 16, 4, 16),
                                                make_pre_atom_value(Value::Int(3), 4, 18, 4, 18),
                                            ],
                                        )],
                                    ),
                                    make_pre_list(
                                        5,
                                        9,
                                        5,
                                        15,
                                        vec![
                                            make_pre_atom("+", 5, 10, 5, 10),
                                            make_pre_atom("x", 5, 12, 5, 12),
                                            make_pre_atom("y", 5, 14, 5, 14),
                                        ],
                                    ),
                                ],
                            ),
                            make_pre_atom("x", 6, 9, 6, 9),
                        ],
                    ),
                ],
            ),
            make_pre_atom("x", 6, 13, 6, 13),
            make_pre_atom("y", 6, 15, 6, 15),
        ];

        let ast = vec![
            make_atom("z", 1, 1, 1, 1),
            make_list(
                1,
                3,
                6,
                11,
                vec![
                    make_atom("let", 1, 4, 1, 6),
                    make_list(
                        1,
                        8,
                        1,
                        20,
                        vec![
                            make_list(
                                1,
                                9,
                                1,
                                13,
                                vec![
                                    make_atom("x", 1, 10, 1, 10),
                                    make_literal_value(Value::Int(1), 1, 12, 1, 12),
                                ],
                            ),
                            make_list(
                                1,
                                15,
                                1,
                                19,
                                vec![
                                    make_atom("y", 1, 16, 1, 16),
                                    make_literal_value(Value::Int(2), 1, 18, 1, 18),
                                ],
                            ),
                        ],
                    ),
                    make_list(
                        2,
                        5,
                        6,
                        10,
                        vec![
                            make_atom("+", 2, 6, 2, 6),
                            make_atom("x", 2, 8, 2, 8),
                            make_list(
                                4,
                                9,
                                5,
                                16,
                                vec![
                                    make_atom("let", 4, 10, 4, 12),
                                    make_list(
                                        4,
                                        14,
                                        4,
                                        20,
                                        vec![make_list(
                                            4,
                                            15,
                                            4,
                                            19,
                                            vec![
                                                make_atom("x", 4, 16, 4, 16),
                                                make_literal_value(Value::Int(3), 4, 18, 4, 18),
                                            ],
                                        )],
                                    ),
                                    make_list(
                                        5,
                                        9,
                                        5,
                                        15,
                                        vec![
                                            make_atom("+", 5, 10, 5, 10),
                                            make_atom("x", 5, 12, 5, 12),
                                            make_atom("y", 5, 14, 5, 14),
                                        ],
                                    ),
                                ],
                            ),
                            make_atom("x", 6, 9, 6, 9),
                        ],
                    ),
                ],
            ),
            make_atom("x", 6, 13, 6, 13),
            make_atom("y", 6, 15, 6, 15),
        ];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.contract-a",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);
        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "Should match expected symbolic expression"
        );
    }

    #[test]
    fn test_transform_tuple_literal() {
        let pre_ast = vec![make_pre_tuple(
            1,
            1,
            1,
            9,
            vec![
                make_pre_atom("id", 1, 2, 1, 3),
                make_pre_atom_value(Value::Int(1337), 1, 5, 1, 8),
            ],
        )];
        let ast = vec![make_list(
            1,
            1,
            1,
            9,
            vec![
                make_atom("tuple", 0, 0, 0, 0),
                make_list(
                    0,
                    0,
                    0,
                    0,
                    vec![
                        make_atom("id", 1, 2, 1, 3),
                        make_literal_value(Value::Int(1337), 1, 5, 1, 8),
                    ],
                ),
            ],
        )];
        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.contract-a",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);
        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "Should match expected tuple symbolic expression"
        );
    }

    #[test]
    fn test_transform_sugared_contract_identifier() {
        let contract_name = "tokens".into();
        let pre_ast = vec![make_sugared_contract_identifier(contract_name, 1, 1, 1, 1)];
        let unsugared_contract_id =
            QualifiedContractIdentifier::parse("S1G2081040G2081040G2081040G208105NK8PE5.tokens")
                .unwrap();
        let ast = vec![make_literal_value(
            Value::Principal(PrincipalData::Contract(unsugared_contract_id)),
            1,
            1,
            1,
            1,
        )];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.contract-a",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);
        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "Should match expected symbolic expression"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_end_line_comment() {
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 1, 5, 1, 21),
            make_pre_atom("bar", 2, 1, 2, 3),
        ];
        let mut foo = make_atom("foo", 1, 1, 1, 3);
        foo.end_line_comment = Some("this is a comment".to_string());
        let bar = make_atom("bar", 2, 1, 2, 3);
        let ast = vec![foo, bar];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`foo` should have the end-line comment attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_pre_comment() {
        // Pre-comment at the top of the file
        let pre_ast = vec![
            make_pre_comment("this is a comment".to_string(), 1, 1, 1, 17),
            make_pre_atom("foo", 2, 1, 2, 3),
            make_pre_atom("bar", 3, 1, 3, 3),
        ];
        let mut foo = make_atom("foo", 2, 1, 2, 3);
        foo.pre_comments = vec![(
            "this is a comment".to_string(),
            Span {
                start_line: 1,
                start_column: 1,
                end_line: 1,
                end_column: 17,
            },
        )];
        let bar = make_atom("bar", 3, 1, 3, 3);
        let ast = vec![foo, bar];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`foo` should have the pre-comment attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_pre_comment_second() {
        // Pre-comment on the second expression
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 2, 1, 2, 17),
            make_pre_atom("bar", 3, 1, 3, 3),
        ];
        let foo = make_atom("foo", 1, 1, 1, 3);
        let mut bar = make_atom("bar", 3, 1, 3, 3);
        bar.pre_comments = vec![(
            "this is a comment".to_string(),
            Span {
                start_line: 2,
                start_column: 1,
                end_line: 2,
                end_column: 17,
            },
        )];
        let ast = vec![foo, bar];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`bar` should have the pre-comment attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_pre_comments_multiple() {
        // Multiple pre-comments
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 2, 1, 2, 17),
            make_pre_comment("this is another".to_string(), 3, 1, 3, 15),
            make_pre_atom("bar", 4, 1, 4, 3),
        ];
        let foo = make_atom("foo", 1, 1, 1, 3);
        let mut bar = make_atom("bar", 4, 1, 4, 3);
        bar.pre_comments = vec![
            (
                "this is a comment".to_string(),
                Span {
                    start_line: 2,
                    start_column: 1,
                    end_line: 2,
                    end_column: 17,
                },
            ),
            (
                "this is another".to_string(),
                Span {
                    start_line: 3,
                    start_column: 1,
                    end_line: 3,
                    end_column: 15,
                },
            ),
        ];
        let ast = vec![foo, bar];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`bar` should have both pre-comments attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_pre_comments_newline() {
        // Multiple pre-comments with a newline in between
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 2, 1, 2, 17),
            make_pre_comment("this is another".to_string(), 4, 1, 4, 15),
            make_pre_atom("bar", 5, 1, 5, 3),
        ];
        let foo = make_atom("foo", 1, 1, 1, 3);
        let mut bar = make_atom("bar", 5, 1, 5, 3);
        bar.pre_comments = vec![
            (
                "this is a comment".to_string(),
                Span {
                    start_line: 2,
                    start_column: 1,
                    end_line: 2,
                    end_column: 17,
                },
            ),
            (
                "this is another".to_string(),
                Span {
                    start_line: 4,
                    start_column: 1,
                    end_line: 4,
                    end_column: 15,
                },
            ),
        ];
        let ast = vec![foo, bar];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`bar` should have both pre-comments attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_post_comment() {
        // Post-comment at end of file
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 2, 1, 2, 17),
        ];
        let mut foo = make_atom("foo", 1, 1, 1, 3);
        foo.post_comments = vec![(
            "this is a comment".to_string(),
            Span {
                start_line: 2,
                start_column: 1,
                end_line: 2,
                end_column: 17,
            },
        )];
        let ast = vec![foo];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`foo` should have post-comment attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_post_comments_multiple() {
        // Multiple post-comments at end of file
        let pre_ast = vec![
            make_pre_atom("foo", 1, 1, 1, 3),
            make_pre_comment("this is a comment".to_string(), 2, 1, 2, 17),
            make_pre_comment("this is another".to_string(), 3, 1, 3, 15),
        ];
        let mut foo = make_atom("foo", 1, 1, 1, 3);
        foo.post_comments = vec![
            (
                "this is a comment".to_string(),
                Span {
                    start_line: 2,
                    start_column: 1,
                    end_line: 2,
                    end_column: 17,
                },
            ),
            (
                "this is another".to_string(),
                Span {
                    start_line: 3,
                    start_column: 1,
                    end_line: 3,
                    end_column: 15,
                },
            ),
        ];
        let ast = vec![foo];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`foo` should have both post-comments attached"
        );
    }

    #[test]
    #[cfg(feature = "developer-mode")]
    fn test_attach_post_comment_inside_list() {
        // Post-comment at end of list:
        // (
        //    foo
        //    ;; this is a comment
        // )
        let pre_foo = make_pre_atom("foo", 2, 4, 2, 6);
        let pre_comment = make_pre_comment("this is a comment".to_string(), 3, 4, 3, 20);
        let pre_ast = vec![make_pre_list(1, 1, 4, 1, vec![pre_foo, pre_comment])];
        let mut foo = make_atom("foo", 2, 4, 2, 6);
        foo.post_comments = vec![(
            "this is a comment".to_string(),
            Span {
                start_line: 3,
                start_column: 4,
                end_line: 3,
                end_column: 20,
            },
        )];
        let list = make_list(1, 1, 4, 1, vec![foo]);
        let ast = vec![list];

        let contract_id = QualifiedContractIdentifier::parse(
            "S1G2081040G2081040G2081040G208105NK8PE5.test-comments",
        )
        .unwrap();
        let mut contract_ast = ContractAST::new(contract_id.clone(), pre_ast);

        let expander = SugarExpander::new(contract_id.issuer);
        expander.run(&mut contract_ast).unwrap();
        assert_eq!(
            contract_ast.expressions, ast,
            "`foo` should have post-comment attached"
        );
    }
}
