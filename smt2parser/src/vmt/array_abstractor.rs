use std::collections::HashMap;

use num::{BigUint, Zero};

use crate::concrete::{Command, Identifier, QualIdentifier, Sort, Symbol, SyntaxBuilder, Term};

/// Rewrites Commands to use uninterpreted functions instead of explicit Arrays.
/// Currently turns all Arrays into Arr-Int-Int, but will be extended to arbitrary
/// Arrays later.
#[derive(Clone)]
pub struct ArrayAbstractor {
    pub visitor: SyntaxBuilder,
    pub array_types: HashMap<String, String>,
}
impl ArrayAbstractor {
    pub(crate) fn get_array_type_definitions(&self) -> Vec<Command> {
        let mut commands = vec![];
        for (index, value) in &self.array_types {
            let arr_sort = Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol(format!("Array-{}-{}", index, value)),
                },
            };
            let index_sort = Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol(index.to_string()),
                },
            };
            let value_sort = Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol(value.to_string()),
                },
            };
            let sort_definition = Command::DeclareSort {
                symbol: Symbol(format!("Array-{}-{}", index, value)),
                arity: BigUint::zero(),
            };
            let read_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("Read-{}-{}", index, value)),
                parameters: vec![arr_sort.clone(), index_sort.clone()],
                sort: value_sort.clone(),
            };
            let write_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("Write-{}-{}", index, value)),
                parameters: vec![arr_sort.clone(), index_sort.clone(), value_sort.clone()],
                sort: arr_sort.clone(),
            };
            let constarr_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("ConstArr-{}-{}", index, value)),
                parameters: vec![value_sort],
                sort: arr_sort,
            };
            commands.push(sort_definition);
            commands.push(constarr_definition);
            commands.push(read_definition);
            commands.push(write_definition);
        }
        commands
    }
}

impl crate::rewriter::Rewriter for ArrayAbstractor {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn visit_declare_fun(
        &mut self,
        symbol: <Self::V as crate::visitors::Smt2Visitor>::Symbol,
        parameters: Vec<<Self::V as crate::visitors::Smt2Visitor>::Sort>,
        sort: <Self::V as crate::visitors::Smt2Visitor>::Sort,
    ) -> Result<<Self::V as crate::visitors::Smt2Visitor>::Command, Self::Error> {
        let new_sort = match sort.clone() {
            crate::concrete::Sort::Simple { identifier: _ } => sort,
            crate::concrete::Sort::Parameterized {
                identifier,
                parameters: _,
            } => {
                if identifier.to_string() == "Array" {
                    crate::concrete::Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Array-Int-Int".to_string()),
                        },
                    }
                } else {
                    sort
                }
            }
        };
        Ok(Command::DeclareFun {
            symbol,
            parameters,
            sort: new_sort,
        })
    }

    fn visit_application(
        &mut self,
        qual_identifier: <Self::V as crate::visitors::Smt2Visitor>::QualIdentifier,
        arguments: Vec<<Self::V as crate::visitors::Smt2Visitor>::Term>,
    ) -> Result<<Self::V as crate::visitors::Smt2Visitor>::Term, Self::Error> {
        let new_identifier = match qual_identifier.clone() {
            crate::concrete::QualIdentifier::Simple { identifier } => {
                if identifier.to_string() == "select" {
                    simple_identifier_with_name("Read-Int-Int")
                } else if identifier.to_string() == "store" {
                    simple_identifier_with_name("Write-Int-Int")
                } else {
                    qual_identifier
                }
            }
            crate::concrete::QualIdentifier::Sorted {
                identifier,
                sort: _,
            } => {
                if identifier.to_string() == "const" {
                    simple_identifier_with_name("ConstArr-Int-Int")
                } else {
                    qual_identifier
                }
            }
        };
        Ok(Term::Application {
            qual_identifier: new_identifier,
            arguments,
        })
    }
}

fn simple_identifier_with_name(name: &str) -> QualIdentifier {
    crate::concrete::QualIdentifier::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(name.to_string()),
        },
    }
}
