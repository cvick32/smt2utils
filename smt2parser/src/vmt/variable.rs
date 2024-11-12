use crate::concrete::Command;


#[derive(Clone, Debug)]
pub struct Variable {
    pub current: Command,
    pub next: Command,
    pub relationship: Command,
}

impl Variable {
    pub fn get_current_variable_name(&self) -> &String {
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

    pub fn get_next_variable_name(&self) -> &String {
        match &self.next {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => {
                return &symbol.0;
            }
            _ => panic!("Variable's next Command must be DeclareFun."),
        }
    }
    
    pub(crate) fn as_commands(&self) -> Vec<Command> {
        vec![self.current.clone(), self.next.clone(), self.relationship.clone()]
    }
}