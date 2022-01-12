use crate::{
    ast::{MetaInfo, Op, ParamDef, Party, Type},
    circuit::Circuit,
    typed_ast::{Expr, ExprEnum, MainDef, Program},
};

impl Program {
    pub fn compile(&self) -> Circuit {
        todo!()
    }
}

#[test]
fn test_bool_op() {
    let prg = Program {
        fn_defs: vec![],
        main: MainDef {
            ty: Type::Bool,
            params: vec![(Party::InA, ParamDef("x".to_string(), Type::Bool))],
            body: Expr(
                ExprEnum::Op(
                    Op::BitXor,
                    Box::new(Expr(
                        ExprEnum::Identifier("x".to_string()),
                        Type::Bool,
                        MetaInfo {},
                    )),
                    Box::new(Expr(
                        ExprEnum::True,
                        Type::Bool,
                        MetaInfo {},
                    ))
                ),
                Type::Bool,
                MetaInfo {},
            ),
            meta: MetaInfo {},
        },
    };
    let circuit = prg.compile();
    assert_eq!(circuit.eval(&[true], &[]), vec![None, None, Some(false)]);
    assert_eq!(circuit.eval(&[false], &[]), vec![None, None, Some(true)]);
}
