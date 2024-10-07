use std::{collections::HashMap, ops::Deref};

use crate::concrete::{Command, SyntaxBuilder, Term};

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

#[derive(Clone, Debug)]
pub struct Variable {
    current: Command,
    next: Command,
}

impl Variable {
    fn get_current_variable_name(&self) -> &String {
        match &self.current {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => {
                return &symbol.0;
            }
            _ => panic!("Variable's current Command must be DeclareFun."),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Action {
    action_command: Command,
}

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

    pub fn print_stats(&self) {
        println!("Number of Variables: {}", self.state_variables.len());
        println!("Number of Actions: {}", self.actions.len());
        println!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn print_smtlib2(&self) {
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
            println!("{}", action.action_command.clone().accept(&mut SyntaxBuilder).unwrap());
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
}

fn get_variables_and_actions(
    variable_relationships: Vec<&Command>,
    variable_commands: HashMap<String, Command>,
) -> (Vec<Variable>, Vec<Action>) {
    let mut state_variables: Vec<Variable> = vec![];
    let mut actions: Vec<Action> = vec![];
    for variable_relationship in variable_relationships {
        match variable_relationship {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes { term, attributes } => {
                    assert!(attributes.len() == 1);
                    let (keyword, value) = &attributes[0];
                    let keyword_string = keyword.to_string();
                    if keyword_string == ":next" {
                        let variable_command = get_variable_command(
                            scrub_variable_name(term.to_string()),
                            &variable_commands,
                        );
                        let new_variable_command = get_variable_command(
                            scrub_variable_name(value.to_string()),
                            &variable_commands,
                        );
                        state_variables.push(Variable {
                            current: variable_command,
                            next: new_variable_command,
                        });
                    } else if keyword_string == ":action" {
                        let action_variable_name = scrub_variable_name(term.to_string());
                        if variable_commands.contains_key(&action_variable_name) {
                            for (variable_name, action_command) in &variable_commands {
                                if action_variable_name == *variable_name {
                                    actions.push(Action { action_command: action_command.clone() });
                                    break;
                                }
                            }
                        } else {
                            panic!("Proposed action variable {} not previously defined.", term);
                        }
                    } else {
                        panic!("Only `next` and `action` keyword attributes are allowed in variable relationships found: {}", keyword_string);
                    }
                }
                _ => panic!("Only Attribute terms can define variable relationships."),
            },
            _ => panic!("Variable Relationship is not a (define-fun)."),
        }
    }
    (state_variables, actions)
}

fn scrub_variable_name(variable_name: String) -> String {
    if variable_name.starts_with("|") && variable_name.ends_with("|") {
        let mut chars = variable_name.chars();
        chars.next();
        chars.next_back();
        chars.as_str().to_string()
    } else {
        variable_name
    }
}

fn get_variable_command(
    variable_name: String,
    variable_commands: &HashMap<String, Command>,
) -> Command {
    match variable_commands.get(&variable_name) {
        Some(command) => command.clone(),
        None => panic!(
            "First term in define-fun must be a variable name: {}",
            variable_name
        ),
    }
}

fn get_transition_system_component(command: &Command, attribute: &str) -> Term {
    if command_has_attribute_string(command, attribute) {
        match command {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes {
                    term,
                    attributes: _,
                } => {
                    return *term.clone();
                }
                _ => panic!("{}: Must have attribute.", attribute),
            },
            _ => panic!("{}: Command must be define-fun", attribute),
        }
    } else {
        panic!(
            "Ill-formed system component: {}.\nShould have {} as attribute.",
            command, attribute
        );
    }
}

fn command_has_attribute_string(command: &Command, attribute: &str) -> bool {
    match command {
        Command::DefineFun { sig: _, term } => match term {
            Term::Attributes {
                term: _,
                attributes,
            } => {
                assert!(attributes.len() == 1);
                let keyword = &attributes[0].0 .0;
                keyword == attribute
            }
            _ => false,
        },
        _ => false,
    }
}
