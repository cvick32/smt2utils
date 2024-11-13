use crate::{concrete::{Command, Term}, vmt::utils::{assert_term, assert_negation}};

use super::{action::Action, bmc::BMCBuilder, variable::Variable, };


#[derive(Default)]
pub struct SMTProblem {
    sorts: Vec<Command>,
    variable_definitions: Vec<Command>,
    function_definitions: Vec<Command>,
    init_and_trans_assertions: Vec<Term>,
    property_assertion: Option<Term>,
}

impl SMTProblem {
    pub fn new(sorts: &Vec<Command>, function_definitions: &Vec<Command>) -> Self {
        Self {
            sorts: sorts.clone(),
            variable_definitions: vec![],
            function_definitions: function_definitions.clone(),
            init_and_trans_assertions: vec![],
            property_assertion: None,
        }
    }

    pub fn init_and_trans_length(&self) -> usize {
        self.init_and_trans_assertions.len()
    }

    pub fn add_assertion(&mut self, condition: &Term, mut builder: BMCBuilder) {
        let rewritten_condition = match condition {
            Term::Attributes { term, attributes: _ } => term.clone().accept(&mut builder).unwrap(),
            _ => panic!("{}", "Assertion must be a Term::Atrributes! One of {{init, trans, invar-prop}}"),
        };
        self.init_and_trans_assertions.push(rewritten_condition);
    }

    /// Need to assert the negation of the property given in the VMTModel for BMC.
    pub fn add_property_assertion(&mut self, condition: &Term, mut builder: BMCBuilder) {
        let rewritten_property = match condition {
            Term::Attributes { term, attributes: _ } => term.clone().accept(&mut builder).unwrap(),
            _ => panic!("{}", "Assertion must be a Term::Atrributes! One of {{init, trans, invar-prop}}"),
        };
        self.property_assertion = Some(rewritten_property);
    }

    pub fn add_variable_definitions(
        &mut self,
        state_variables: &Vec<Variable>,
        actions: &Vec<Action>,
        mut builder: BMCBuilder,
    ) {
        for state_variable in state_variables {
            let definition_at_time = state_variable.current.clone().accept(&mut builder).unwrap();
            self.variable_definitions.push(definition_at_time);
        }
        for action in actions {
            let action_at_time = action.action.clone().accept(&mut builder).unwrap();
            self.variable_definitions.push(action_at_time);
        }
    }
    pub fn to_smtlib2(&self) -> String {
        assert!(
            self.property_assertion.is_some(),
            "No property assertion for SMTProblem!"
        );
        let sort_names = self
            .sorts
            .iter()
            .map(|sort| sort.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let function_definitions = self
            .function_definitions
            .iter()
            .map(|fd| fd.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let defs = self
            .variable_definitions
            .iter()
            .map(|def| def.to_string())
            .collect::<Vec<String>>()
            .join("\n");
        let init_and_trans_asserts = self
            .init_and_trans_assertions
            .iter()
            .map(|term| assert_term(term))
            .collect::<Vec<String>>()
            .join("\n");
        let prop = self.property_assertion.clone().unwrap();
        let property_assert = assert_negation(&prop);
        format!(
            "{}\n{}\n{}\n{}\n{}",
            sort_names, function_definitions, defs, init_and_trans_asserts, property_assert
        )
    }
}
