use crate::{ast::Program, typed_ast};

pub enum TypeError {

}

impl Program {
    pub fn type_check(&self) -> Result<typed_ast::Program, TypeError> {
        todo!()
    }
}
