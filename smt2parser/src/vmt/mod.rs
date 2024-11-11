use std::collections::HashMap;

use action::Action;
use bmc::BMCBuilder;
use smt::SMTProblem;
use utils::{get_transition_system_component, get_variables_and_actions};
use variable::Variable;

use crate::{
    concrete::{Command, Symbol, SyntaxBuilder, Term},
    lexer::Lexer,
};

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

mod smt;
mod utils;
mod variable;
mod action;
mod bmc;

/// VMTModel represents a transition system given in VMT format.
/// The VMT specification is no longer available but there is an example here:
/// https://es-static.fbk.eu/people/griggio/ic3ia/
#[derive(Clone, Debug)]
pub struct VMTModel {
    sorts: Vec<Command>,
    state_variables: Vec<Variable>,
    actions: Vec<Action>,
    initial_condition: Term,
    transition_condition: Term,
    property_condition: Term,
}

impl VMTModel {
    pub fn checked_from(commands: Vec<Command>) -> Result<Self, ()> {
        let number_of_commands = commands.len();
        assert!(number_of_commands > 3, "Not enough commands for VMT model!");
        let property_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 1], PROPERTY_ATTRIBUTE);
        let transition_condition: Term = get_transition_system_component(
            &commands[number_of_commands - 2],
            TRANSITION_ATTRIBUTE,
        );
        let initial_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 3], INITIAL_ATTRIBUTE);
        let mut variable_commands: HashMap<String, Command> = HashMap::new();
        let mut sorts: Vec<Command> = vec![];
        let mut variable_relationships = vec![];
        for (i, command) in commands.iter().enumerate() {
            if i < number_of_commands - 3 {
                // Check whether a variable should be action, state, or local
                match command {
                    Command::DeclareFun {
                        symbol,
                        parameters: _,
                        sort: _,
                    } => {
                        variable_commands.insert(symbol.0.clone(), command.clone());
                    }
                    Command::DefineFun { sig: _, term: _ } => {
                        variable_relationships.push(command);
                    }
                    Command::DeclareSort {
                        symbol: _,
                        arity: _,
                    } => {
                        sorts.push(command.clone());
                    }
                    _ => {
                        panic!("Unknown VMT command: {:?}", command);
                    }
                }
            }
        }
        let (state_variables, actions) =
            get_variables_and_actions(variable_relationships, variable_commands);

        Ok(VMTModel {
            sorts,
            state_variables,
            actions,
            initial_condition,
            transition_condition,
            property_condition,
        })
    }

    pub fn abstract_array_theory(&self) -> VMTModel {
        self.clone()
    }

    pub fn print_stats(&self) {
        println!("Number of Variables: {}", self.state_variables.len());
        println!("Number of Actions: {}", self.actions.len());
        println!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn print_raw_smtlib2(&self) {
        for sort in &self.sorts {
            println!("{}", sort.clone().accept(&mut SyntaxBuilder).unwrap())
        }
        for var in &self.state_variables {
            println!(
                "{}",
                var.current.clone().accept(&mut SyntaxBuilder).unwrap()
            );
        }
        for action in &self.actions {
            println!(
                "{}",
                action
                    .action_command
                    .clone()
                    .accept(&mut SyntaxBuilder)
                    .unwrap()
            );
        }
        println!(
            "INIT: {}",
            self.initial_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
        println!(
            "TRANS: {}",
            self.transition_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
        println!(
            "PROP: {}",
            self.property_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
    }

    pub fn unroll(&self, length: u8) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_all_next_variable_names(),
            step: 0,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts);

        smt_problem.add_assertion(&self.initial_condition, builder.clone());
        for _ in 0..length {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_definitions(&self.state_variables, &self.actions, builder.clone());
            smt_problem.add_assertion(&self.transition_condition, builder.clone());
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_definitions(&self.state_variables, &self.actions, builder.clone());
        smt_problem.add_property_assertion(&self.property_condition, builder.clone());
        assert!(
            smt_problem.init_and_trans_length() == (length + 1).into(),
            "Unrolling gives incorrect number of steps {} for length {}.",
            smt_problem.init_and_trans_length(),
            length
        );
        smt_problem
    }

    fn get_all_current_variable_names(&self) -> Vec<String> {
        let mut state_variable_names: Vec<String> = self
            .state_variables
            .iter()
            .map(|var| var.get_current_variable_name().clone())
            .collect();
        let mut action_names: Vec<String> = self
            .actions
            .iter()
            .map(|action| action.get_current_action_name().clone())
            .collect();
        state_variable_names.append(&mut action_names);
        state_variable_names
    }

    fn get_all_next_variable_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_next_variable_name().clone(),
                    var.get_current_variable_name().clone(),
                )
            })
            .collect()
    }
}