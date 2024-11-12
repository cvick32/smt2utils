use std::collections::{HashMap, HashSet};

use crate::concrete::{Command, Identifier, QualIdentifier, Symbol, SyntaxBuilder, Term};

#[derive(Clone)]
pub struct ArrayAbstractor {
    pub visitor: SyntaxBuilder,
    pub array_types: HashSet<String>,
}

impl ArrayAbstractor {
    pub fn add_array_type(&mut self, array_type: String) {
        self.array_types.insert(array_type);
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
                            symbol: Symbol(format!("{}", "Array-Int-Int")),
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
            },
            crate::concrete::QualIdentifier::Sorted { identifier, sort: _ } =>  {
                println!("{}", qual_identifier);
                println!("hehe {}", identifier.to_string());
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
    crate::concrete::QualIdentifier::Simple { identifier: Identifier::Simple { symbol: Symbol(format!("{}", name)) } }
}