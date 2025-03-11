//! Compiles a [`crate::ast::Program`] to a [`crate::circuit::Circuit`].

use std::{
    cmp::{max, min},
    collections::HashMap,
};

use crate::{
    ast::{
        ConstExpr, ConstExprEnum, EnumDef, Expr, ExprEnum, Op, Pattern, PatternEnum, StmtEnum,
        StructDef, Type, UnaryOp, VariantExprEnum,
    },
    circuit::{Circuit, CircuitBuilder, GateIndex, PanicReason, USIZE_BITS},
    env::Env,
    literal::Literal,
    token::{MetaInfo, SignedNumType, UnsignedNumType},
    TypedExpr, TypedFnDef, TypedPattern, TypedProgram, TypedStmt,
};

/// An error that occurred during compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompilerError {
    /// The specified function could not be compiled, as it was not found in the program.
    FnNotFound(String),
    /// The provided constant was not of the required type.
    InvalidLiteralType(Literal, Type),
    /// The constant was declared in the program but not provided during compilation.
    MissingConstant(String, String, MetaInfo),
}

impl PartialOrd for CompilerError {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CompilerError {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (CompilerError::FnNotFound(fn1), CompilerError::FnNotFound(fn2)) => fn1.cmp(fn2),
            (CompilerError::FnNotFound(_), _) => std::cmp::Ordering::Less,
            (CompilerError::InvalidLiteralType(_, _), CompilerError::FnNotFound(_)) => {
                std::cmp::Ordering::Greater
            }
            (
                CompilerError::InvalidLiteralType(literal1, _),
                CompilerError::InvalidLiteralType(literal2, _),
            ) => literal1.cmp(literal2),
            (CompilerError::InvalidLiteralType(_, _), CompilerError::MissingConstant(_, _, _)) => {
                std::cmp::Ordering::Less
            }
            (
                CompilerError::MissingConstant(_, _, meta1),
                CompilerError::MissingConstant(_, _, meta2),
            ) => meta1.cmp(meta2),
            (CompilerError::MissingConstant(_, _, _), _) => std::cmp::Ordering::Greater,
        }
    }
}

impl std::fmt::Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerError::FnNotFound(fn_name) => f.write_fmt(format_args!(
                "Could not find any function with name '{fn_name}'"
            )),
            CompilerError::InvalidLiteralType(literal, ty) => {
                f.write_fmt(format_args!("The literal is not of type '{ty}': {literal}"))
            }
            CompilerError::MissingConstant(party, identifier, _) => f.write_fmt(format_args!(
                "The constant {party}::{identifier} was declared in the program but never provided"
            )),
        }
    }
}

type CompiledProgram<'a> = (Circuit, &'a TypedFnDef, HashMap<String, usize>);

impl TypedProgram {
    /// Compiles the (type-checked) program, producing a circuit of gates.
    ///
    /// Assumes that the input program has been correctly type-checked and **panics** if
    /// incompatible types are found that should have been caught by the type-checker.
    pub fn compile(&self, fn_name: &str) -> Result<(Circuit, &TypedFnDef), Vec<CompilerError>> {
        self.compile_with_constants(fn_name, HashMap::new())
            .map(|(c, f, _)| (c, f))
    }

    /// Compiles the (type-checked) program with provided constants, producing a circuit of gates.
    ///
    /// Assumes that the input program has been correctly type-checked and **panics** if
    /// incompatible types are found that should have been caught by the type-checker.
    pub fn compile_with_constants(
        &self,
        fn_name: &str,
        consts: HashMap<String, HashMap<String, Literal>>,
    ) -> Result<CompiledProgram, Vec<CompilerError>> {
        let mut env = Env::new();
        let mut const_sizes = HashMap::new();
        let mut consts_unsigned = HashMap::new();
        let mut consts_signed = HashMap::new();

        let mut errs = vec![];
        for (party, deps) in self.const_deps.iter() {
            for (c, (ty, meta)) in deps {
                let Some(party_deps) = consts.get(party) else {
                    errs.push(CompilerError::MissingConstant(
                        party.clone(),
                        c.clone(),
                        *meta,
                    ));
                    continue;
                };
                let Some(literal) = party_deps.get(c) else {
                    errs.push(CompilerError::MissingConstant(
                        party.clone(),
                        c.clone(),
                        *meta,
                    ));
                    continue;
                };
                let identifier = format!("{party}::{c}");
                match literal {
                    Literal::NumUnsigned(n, _) => {
                        consts_unsigned.insert(identifier.clone(), *n);
                    }
                    Literal::NumSigned(n, _) => {
                        consts_signed.insert(identifier.clone(), *n);
                    }
                    _ => {}
                }
                if literal.is_of_type(self, ty) {
                    if let Literal::NumUnsigned(size, UnsignedNumType::Usize) = literal {
                        const_sizes.insert(identifier, *size as usize);
                    }
                }
            }
        }
        if !errs.is_empty() {
            errs.sort();
            return Err(errs);
        }
        fn resolve_const_expr_unsigned(
            ConstExpr(expr, _): &ConstExpr,
            consts_unsigned: &HashMap<String, u64>,
        ) -> u64 {
            match expr {
                ConstExprEnum::NumUnsigned(n, _) => *n,
                ConstExprEnum::ExternalValue { party, identifier } => *consts_unsigned
                    .get(&format!("{party}::{identifier}"))
                    .unwrap(),
                ConstExprEnum::Max(args) => {
                    let mut result = 0;
                    for arg in args {
                        result = max(result, resolve_const_expr_unsigned(arg, consts_unsigned));
                    }
                    result
                }
                ConstExprEnum::Min(args) => {
                    let mut result = u64::MAX;
                    for arg in args {
                        result = min(result, resolve_const_expr_unsigned(arg, consts_unsigned));
                    }
                    result
                }
                expr => panic!("Not an unsigned const expr: {expr:?}"),
            }
        }
        fn resolve_const_expr_signed(
            ConstExpr(expr, _): &ConstExpr,
            consts_signed: &HashMap<String, i64>,
        ) -> i64 {
            match expr {
                ConstExprEnum::NumSigned(n, _) => *n,
                ConstExprEnum::ExternalValue { party, identifier } => *consts_signed
                    .get(&format!("{party}::{identifier}"))
                    .unwrap(),
                ConstExprEnum::Max(args) => {
                    let mut result = 0;
                    for arg in args {
                        result = max(result, resolve_const_expr_signed(arg, consts_signed));
                    }
                    result
                }
                ConstExprEnum::Min(args) => {
                    let mut result = i64::MAX;
                    for arg in args {
                        result = min(result, resolve_const_expr_signed(arg, consts_signed));
                    }
                    result
                }
                expr => panic!("Not an unsigned const expr: {expr:?}"),
            }
        }
        for (const_name, const_def) in self.const_defs.iter() {
            if let Type::Unsigned(UnsignedNumType::Usize) = const_def.ty {
                if let ConstExpr(ConstExprEnum::ExternalValue { party, identifier }, _) =
                    &const_def.value
                {
                    let identifier = format!("{party}::{identifier}");
                    const_sizes.insert(const_name.clone(), *const_sizes.get(&identifier).unwrap());
                }
                let n = resolve_const_expr_unsigned(&const_def.value, &consts_unsigned);
                const_sizes.insert(const_name.clone(), n as usize);
            }
        }

        let mut errs = vec![];
        for (party, deps) in self.const_deps.iter() {
            for (c, (ty, _)) in deps {
                let Some(party_deps) = consts.get(party) else {
                    continue;
                };
                let Some(literal) = party_deps.get(c) else {
                    continue;
                };
                let identifier = format!("{party}::{c}");
                if literal.is_of_type(self, ty) {
                    let bits = literal
                        .as_bits(self, &const_sizes)
                        .iter()
                        .map(|b| *b as usize)
                        .collect();
                    env.let_in_current_scope(identifier.clone(), bits);
                } else {
                    errs.push(CompilerError::InvalidLiteralType(
                        literal.clone(),
                        ty.clone(),
                    ));
                }
            }
        }
        if !errs.is_empty() {
            errs.sort();
            return Err(errs);
        }
        let mut input_gates = vec![];
        let mut wire = 2;
        let Some(fn_def) = self.fn_defs.get(fn_name) else {
            return Err(vec![CompilerError::FnNotFound(fn_name.to_string())]);
        };
        let single_array_as_multiple_parties = if fn_def.params.len() == 1 {
            let param = &fn_def.params[0];
            match &param.ty {
                Type::Array(elem_ty, size) => Some((param, elem_ty, size)),
                Type::ArrayConst(elem_ty, size) => {
                    Some((param, elem_ty, const_sizes.get(size).unwrap()))
                }
                _ => None,
            }
        } else {
            None
        };
        if let Some((param, elem_ty, size)) = single_array_as_multiple_parties {
            let mut wires = vec![];
            for _ in 0..*size {
                let type_size = elem_ty.size_in_bits_for_defs(self, &const_sizes);
                for _ in 0..type_size {
                    wires.push(wire);
                    wire += 1;
                }
                input_gates.push(type_size);
            }
            env.let_in_current_scope(param.name.clone(), wires);
        } else {
            for param in fn_def.params.iter() {
                let type_size = param.ty.size_in_bits_for_defs(self, &const_sizes);
                let mut wires = Vec::with_capacity(type_size);
                for _ in 0..type_size {
                    wires.push(wire);
                    wire += 1;
                }
                input_gates.push(type_size);
                env.let_in_current_scope(param.name.clone(), wires);
            }
        }
        let mut circuit = CircuitBuilder::new(input_gates, const_sizes.clone());
        for (const_name, const_def) in self.const_defs.iter() {
            let ConstExpr(expr, _) = &const_def.value;
            match expr {
                ConstExprEnum::True => env.let_in_current_scope(const_name.clone(), vec![1]),
                ConstExprEnum::False => env.let_in_current_scope(const_name.clone(), vec![0]),
                ConstExprEnum::NumUnsigned(n, ty) => {
                    let ty = Type::Unsigned(*ty);
                    let mut bits =
                        Vec::with_capacity(ty.size_in_bits_for_defs(self, circuit.const_sizes()));
                    unsigned_to_bits(
                        *n,
                        ty.size_in_bits_for_defs(self, circuit.const_sizes()),
                        &mut bits,
                    );
                    let bits = bits.into_iter().map(|b| b as usize).collect();
                    env.let_in_current_scope(const_name.clone(), bits);
                }
                ConstExprEnum::NumSigned(n, ty) => {
                    let ty = Type::Signed(*ty);
                    let mut bits =
                        Vec::with_capacity(ty.size_in_bits_for_defs(self, circuit.const_sizes()));
                    signed_to_bits(
                        *n,
                        ty.size_in_bits_for_defs(self, circuit.const_sizes()),
                        &mut bits,
                    );
                    let bits = bits.into_iter().map(|b| b as usize).collect();
                    env.let_in_current_scope(const_name.clone(), bits);
                }
                ConstExprEnum::ExternalValue { party, identifier } => {
                    let bits = env.get(&format!("{party}::{identifier}")).unwrap();
                    env.let_in_current_scope(const_name.clone(), bits);
                }
                ConstExprEnum::Max(_) | ConstExprEnum::Min(_) => {
                    if let Type::Unsigned(_) = const_def.ty {
                        let result =
                            resolve_const_expr_unsigned(&const_def.value, &consts_unsigned);
                        let mut bits = Vec::with_capacity(
                            const_def
                                .ty
                                .size_in_bits_for_defs(self, circuit.const_sizes()),
                        );
                        unsigned_to_bits(
                            result,
                            const_def
                                .ty
                                .size_in_bits_for_defs(self, circuit.const_sizes()),
                            &mut bits,
                        );
                        let bits = bits.into_iter().map(|b| b as usize).collect();
                        env.let_in_current_scope(const_name.clone(), bits);
                    } else {
                        let result = resolve_const_expr_signed(&const_def.value, &consts_signed);
                        let mut bits = Vec::with_capacity(
                            const_def
                                .ty
                                .size_in_bits_for_defs(self, circuit.const_sizes()),
                        );
                        signed_to_bits(
                            result,
                            const_def
                                .ty
                                .size_in_bits_for_defs(self, circuit.const_sizes()),
                            &mut bits,
                        );
                        let bits = bits.into_iter().map(|b| b as usize).collect();
                        env.let_in_current_scope(const_name.clone(), bits);
                    }
                }
            }
        }
        let output_gates = compile_block(&fn_def.body, self, &mut env, &mut circuit);
        Ok((circuit.build(output_gates), fn_def, const_sizes))
    }
}

fn compile_block(
    stmts: &[TypedStmt],
    prg: &TypedProgram,
    env: &mut Env<Vec<GateIndex>>,
    circuit: &mut CircuitBuilder,
) -> Vec<GateIndex> {
    env.push();
    let mut expr = vec![];
    for stmt in stmts {
        expr = stmt.compile(prg, env, circuit);
    }
    env.pop();
    expr
}

impl TypedStmt {
    fn compile(
        &self,
        prg: &TypedProgram,
        env: &mut Env<Vec<GateIndex>>,
        circuit: &mut CircuitBuilder,
    ) -> Vec<GateIndex> {
        match &self.inner {
            StmtEnum::Let(pattern, binding) => {
                let binding = binding.compile(prg, env, circuit);
                pattern.compile(&binding, prg, env, circuit);
                vec![]
            }
            StmtEnum::Expr(expr) => expr.compile(prg, env, circuit),
            StmtEnum::LetMut(identifier, binding) => {
                let binding = binding.compile(prg, env, circuit);
                env.let_in_current_scope(identifier.clone(), binding);
                vec![]
            }
            StmtEnum::VarAssign(identifier, value) => {
                let value = value.compile(prg, env, circuit);
                env.assign_mut(identifier.clone(), value);
                vec![]
            }
            StmtEnum::ArrayAssign(identifier, index, value) => {
                let elem_bits = value.ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let mut array = env.get(identifier).unwrap();
                let size = array.len() / elem_bits;
                let mut index = index.compile(prg, env, circuit);
                let value = value.compile(prg, env, circuit);
                let index_bits = Type::Unsigned(UnsignedNumType::Usize)
                    .size_in_bits_for_defs(prg, circuit.const_sizes());
                extend_to_bits(
                    &mut index,
                    &Type::Unsigned(UnsignedNumType::Usize),
                    index_bits,
                );

                let mut index_negated = vec![0; index.len()];
                for (i, index) in index.iter().copied().enumerate() {
                    index_negated[i] = circuit.push_not(index);
                }
                // for each array element...
                for i in 0..size {
                    // ...and each bit of that array element...
                    for b in 0..elem_bits {
                        // ...use a index-length chain of mux, select the value if index == i
                        let mut x1 = value[b];
                        for s in 0..index.len() {
                            let s_must_be_negated = ((i >> (index.len() - s - 1)) & 1) > 0;
                            let s = if s_must_be_negated {
                                index_negated[s]
                            } else {
                                index[s]
                            };
                            // x0 is selected by the mux-chain whenever a single bit of index != i
                            let x0 = array[i * elem_bits + b];
                            // x1 is value[b] only if index == i in all bits
                            x1 = circuit.push_mux(s, x0, x1);
                        }
                        array[i * elem_bits + b] = x1;
                    }
                }
                let mut array_len = Vec::with_capacity(index_bits);
                unsigned_to_bits(size as u64, index_bits, &mut array_len);
                let array_len: Vec<usize> = array_len.into_iter().map(|b| b as usize).collect();
                let (index_less_than_array_len, _) =
                    circuit.push_comparator_circuit(index_bits, &index, false, &array_len, false);
                let out_of_bounds = circuit.push_not(index_less_than_array_len);
                circuit.push_panic_if(out_of_bounds, PanicReason::OutOfBounds, self.meta);
                env.assign_mut(identifier.clone(), array);
                vec![]
            }
            StmtEnum::ForEachLoop(pattern, array, body) => {
                let elem_in_bits = match &array.ty {
                    Type::Array(elem_ty, _) | Type::ArrayConst(elem_ty, _) => {
                        elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes())
                    }
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                env.push();
                let array = array.compile(prg, env, circuit);

                let mut i = 0;
                while i < array.len() {
                    let binding = &array[i..i + elem_in_bits];
                    pattern.compile(binding, prg, env, circuit);

                    for stmt in body {
                        stmt.compile(prg, env, circuit);
                    }
                    i += elem_in_bits;
                }
                env.pop();
                vec![]
            }
            StmtEnum::JoinLoop(pattern, join_ty, (a, b), body) => {
                let (elem_bits_a, num_elems_a) = match &a.ty {
                    Type::Array(elem_ty, size) => (
                        elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                        *size,
                    ),
                    Type::ArrayConst(elem_ty, size) => (
                        elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                        *circuit.const_sizes().get(size).unwrap(),
                    ),
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                let (elem_bits_b, num_elems_b) = match &b.ty {
                    Type::Array(elem_ty, size) => (
                        elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                        *size,
                    ),
                    Type::ArrayConst(elem_ty, size) => (
                        elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                        *circuit.const_sizes().get(size).unwrap(),
                    ),
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                let max_elem_bits = max(elem_bits_a, elem_bits_b);
                let num_elems = (num_elems_a + num_elems_b).next_power_of_two();
                let join_ty_size = join_ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let a = a.compile(prg, env, circuit);
                let b = b.compile(prg, env, circuit);
                let mut bitonic = vec![];
                let num_empty_elems = num_elems - num_elems_a - num_elems_b;
                for _ in 0..num_empty_elems {
                    bitonic.push(vec![0; max_elem_bits + 1]);
                }
                for i in 0..num_elems_a {
                    let mut v = a[i * elem_bits_a..(i + 1) * elem_bits_a].to_vec();
                    v.resize(max_elem_bits, 0);
                    v.insert(join_ty_size, 0);
                    bitonic.push(v);
                }
                for i in (0..num_elems_b).rev() {
                    let mut v = b[i * elem_bits_b..(i + 1) * elem_bits_b].to_vec();
                    v.resize(max_elem_bits, 0);
                    v.insert(join_ty_size, 1);
                    bitonic.push(v);
                }
                let mut offset = num_elems / 2;
                while offset > 0 {
                    let mut result = vec![];
                    for _ in 0..num_elems {
                        result.push(vec![]);
                    }
                    let rounds = num_elems / 2 / offset;
                    for r in 0..rounds {
                        for i in 0..offset {
                            let i = i + r * offset * 2;
                            let x = &bitonic[i];
                            let y = &bitonic[i + offset];
                            let (min, max) = circuit.push_sorter(join_ty_size, x, y);
                            result[i] = min;
                            result[i + offset] = max;
                        }
                    }
                    offset /= 2;
                    bitonic = result;
                }
                for slice in bitonic.windows(2).skip(num_empty_elems) {
                    let mut binding = vec![];
                    let (mut a, mut b) =
                        circuit.push_sorter(join_ty_size + 1, &slice[0], &slice[1]);
                    a.remove(join_ty_size);
                    a.truncate(elem_bits_a);
                    b.remove(join_ty_size);
                    b.truncate(elem_bits_b);
                    binding.extend(&a);
                    binding.extend(&b);
                    let join_a = &a[..join_ty_size];
                    let join_b = &b[..join_ty_size];
                    let mut join_eq = 1;
                    for i in 0..join_ty_size {
                        let eq = circuit.push_eq(join_a[i], join_b[i]);
                        join_eq = circuit.push_and(join_eq, eq);
                    }

                    let panic_before_branches = circuit.peek_panic().clone();

                    let mut env_if_join = env.clone();
                    env_if_join.push();
                    pattern.compile(&binding, prg, &mut env_if_join, circuit);

                    for stmt in body {
                        stmt.compile(prg, &mut env_if_join, circuit);
                    }
                    env_if_join.pop();

                    let panic_if_join = circuit.replace_panic_with(panic_before_branches.clone());

                    *env = circuit.mux_envs(join_eq, env_if_join, env.clone());
                    let muxed_panic =
                        circuit.mux_panic(join_eq, &panic_if_join, &panic_before_branches);
                    circuit.replace_panic_with(muxed_panic);
                }
                vec![]
            }
        }
    }
}

impl TypedExpr {
    fn compile(
        &self,
        prg: &TypedProgram,
        env: &mut Env<Vec<GateIndex>>,
        circuit: &mut CircuitBuilder,
    ) -> Vec<GateIndex> {
        let meta = self.meta;
        let ty = &self.ty;
        match &self.inner {
            ExprEnum::True => {
                vec![1]
            }
            ExprEnum::False => {
                vec![0]
            }
            ExprEnum::NumUnsigned(n, _) => {
                let mut bits =
                    Vec::with_capacity(ty.size_in_bits_for_defs(prg, circuit.const_sizes()));
                unsigned_to_bits(
                    *n,
                    ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                    &mut bits,
                );
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::NumSigned(n, _) => {
                let mut bits =
                    Vec::with_capacity(ty.size_in_bits_for_defs(prg, circuit.const_sizes()));
                signed_to_bits(
                    *n,
                    ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                    &mut bits,
                );
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::Identifier(s) => env.get(s).unwrap(),
            ExprEnum::ArrayLiteral(elems) => {
                let mut wires =
                    Vec::with_capacity(ty.size_in_bits_for_defs(prg, circuit.const_sizes()));
                for elem in elems {
                    wires.extend(elem.compile(prg, env, circuit));
                }
                wires
            }
            ExprEnum::ArrayRepeatLiteral(elem, size) => {
                let elem_ty = elem.ty.clone();
                let mut elem = elem.compile(prg, env, circuit);
                extend_to_bits(
                    &mut elem,
                    &elem_ty,
                    elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                );
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let mut array = Vec::with_capacity(bits);
                for _ in 0..*size {
                    array.extend_from_slice(&elem);
                }
                array
            }
            ExprEnum::ArrayRepeatLiteralConst(elem, size) => {
                let size = *circuit.const_sizes().get(size).unwrap();
                let elem_ty = elem.ty.clone();
                let mut elem = elem.compile(prg, env, circuit);
                extend_to_bits(
                    &mut elem,
                    &elem_ty,
                    elem_ty.size_in_bits_for_defs(prg, circuit.const_sizes()),
                );
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let mut array = Vec::with_capacity(bits);
                for _ in 0..size {
                    array.extend_from_slice(&elem);
                }
                array
            }
            ExprEnum::ArrayAccess(array, index) => {
                let num_elems = match &array.ty {
                    Type::Array(_, size) => *size,
                    Type::ArrayConst(_, size) => *circuit.const_sizes().get(size).unwrap(),
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                let elem_bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let mut array = array.compile(prg, env, circuit);
                let mut index = index.compile(prg, env, circuit);
                let index_bits = Type::Unsigned(UnsignedNumType::Usize)
                    .size_in_bits_for_defs(prg, circuit.const_sizes());
                extend_to_bits(
                    &mut index,
                    &Type::Unsigned(UnsignedNumType::Usize),
                    index_bits,
                );
                let out_of_bounds_elem = 1;
                for mux_layer in (0..index.len()).rev() {
                    let mut muxed_array = Vec::new();
                    let s = index[mux_layer];
                    let mut i = 0;
                    while i < array.len() {
                        for _ in 0..elem_bits {
                            if i + elem_bits < array.len() {
                                let a0 = array[i];
                                let a1 = array[i + elem_bits];
                                muxed_array.push(circuit.push_mux(s, a1, a0));
                            } else if i < array.len() {
                                let a0 = array[i];
                                muxed_array.push(circuit.push_mux(s, out_of_bounds_elem, a0));
                            }
                            i += 1;
                        }
                        i += elem_bits;
                    }
                    array = muxed_array;
                }
                let mut array_len = Vec::with_capacity(index_bits);
                unsigned_to_bits(num_elems as u64, index_bits, &mut array_len);
                let array_len: Vec<usize> = array_len.into_iter().map(|b| b as usize).collect();
                let (index_less_than_array_len, _) =
                    circuit.push_comparator_circuit(index_bits, &index, false, &array_len, false);
                let out_of_bounds = circuit.push_not(index_less_than_array_len);
                circuit.push_panic_if(out_of_bounds, PanicReason::OutOfBounds, meta);
                if array.is_empty() {
                    // accessing a 0-size array will result in a panic, but we still need to return
                    // an element of a valid size (even though it will not be used)
                    vec![0; elem_bits]
                } else {
                    array
                }
            }
            ExprEnum::TupleLiteral(tuple) => {
                let mut wires =
                    Vec::with_capacity(ty.size_in_bits_for_defs(prg, circuit.const_sizes()));
                for value in tuple {
                    wires.extend(value.compile(prg, env, circuit));
                }
                wires
            }
            ExprEnum::TupleAccess(tuple, index) => {
                let (wires_before, wires_at_index) = match &tuple.ty {
                    Type::Tuple(values) => {
                        let mut wires_before = 0;
                        for v in values[0..*index].iter() {
                            wires_before += v.size_in_bits_for_defs(prg, circuit.const_sizes());
                        }
                        (
                            wires_before,
                            values[*index].size_in_bits_for_defs(prg, circuit.const_sizes()),
                        )
                    }
                    _ => panic!("Expected a tuple type, but found {:?}", tuple.meta),
                };
                let tuple = tuple.compile(prg, env, circuit);
                tuple[wires_before..wires_before + wires_at_index].to_vec()
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.compile(prg, env, circuit);
                circuit.push_negation_circuit(&x)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.compile(prg, env, circuit);
                let mut flipped = vec![0; x.len()];
                for (i, x) in x.iter().enumerate() {
                    flipped[i] = circuit.push_not(*x);
                }
                flipped
            }
            ExprEnum::Op(Op::ShortCircuitAnd, x, y) => {
                let x = x.compile(prg, env, circuit);
                assert_eq!(x.len(), 1);
                let panic_before_y = circuit.peek_panic().clone();
                let y = y.compile(prg, env, circuit);
                assert_eq!(y.len(), 1);

                let panic = circuit.mux_panic(x[0], &circuit.peek_panic().clone(), &panic_before_y);
                circuit.replace_panic_with(panic);

                vec![circuit.push_and(x[0], y[0])]
            }
            ExprEnum::Op(Op::ShortCircuitOr, x, y) => {
                let x = x.compile(prg, env, circuit);
                assert_eq!(x.len(), 1);
                let panic_before_y = circuit.peek_panic().clone();
                let y = y.compile(prg, env, circuit);
                assert_eq!(y.len(), 1);

                let panic = circuit.mux_panic(x[0], &panic_before_y, &circuit.peek_panic().clone());
                circuit.replace_panic_with(panic);

                vec![circuit.push_or(x[0], y[0])]
            }
            ExprEnum::Op(op @ (Op::ShiftLeft | Op::ShiftRight), x, y) => {
                let x_is_signed = is_signed(&x.ty);
                let x = x.compile(prg, env, circuit);
                let y = y.compile(prg, env, circuit);
                assert_eq!(y.len(), 8);
                let bits = x.len();
                let bit_to_shift_in = if x_is_signed && op == &Op::ShiftRight {
                    x[0]
                } else {
                    0
                };
                let mut shift = 1;
                let mut bits_unshifted = x;
                for layer in (0..8).rev() {
                    let s = y[layer];
                    let mut bits_shifted = vec![0; bits];
                    for i in 0..bits {
                        let unshifted = bits_unshifted[i];
                        let shifted = if op == &Op::ShiftLeft {
                            if i + shift >= bits {
                                0
                            } else {
                                bits_unshifted[i + shift]
                            }
                        } else if i < shift {
                            bit_to_shift_in
                        } else {
                            bits_unshifted[i - shift]
                        };
                        bits_shifted[i] = circuit.push_mux(s, shifted, unshifted);
                    }
                    shift *= 2;
                    bits_unshifted = bits_shifted;
                }
                let max_filled_bits = match bits {
                    8 => 3,
                    16 => 4,
                    32 => 5,
                    64 => 6,
                    bits => panic!("Unexpected number of bits to be shifted: {bits}"),
                };
                let mut overflow = 0;
                for &w in y[..(8 - max_filled_bits)].iter() {
                    overflow = circuit.push_or(overflow, w);
                }
                circuit.push_panic_if(overflow, PanicReason::Overflow, meta);
                bits_unshifted
            }
            ExprEnum::Op(op, x, y) => {
                if let Op::Mul = op {
                    for (x, y) in [(x, y), (y, x)] {
                        let (n, bits, is_neg) = match x.inner {
                            ExprEnum::NumUnsigned(n, size) => (
                                n,
                                Type::Unsigned(size)
                                    .size_in_bits_for_defs(prg, circuit.const_sizes())
                                    as u64,
                                false,
                            ),
                            ExprEnum::NumSigned(n, size) => (
                                n.unsigned_abs(),
                                Type::Signed(size).size_in_bits_for_defs(prg, circuit.const_sizes())
                                    as u64,
                                n < 0,
                            ),
                            _ => continue,
                        };
                        if n == 0 {
                            continue;
                        }
                        if n < bits {
                            let mut expr = y.clone();
                            for _ in 0..n - 1 {
                                expr = Box::new(Expr {
                                    inner: ExprEnum::Op(Op::Add, expr, y.clone()),
                                    meta,
                                    ty: ty.clone(),
                                });
                            }
                            if is_neg {
                                return Expr {
                                    inner: ExprEnum::UnaryOp(UnaryOp::Neg, expr),
                                    meta,
                                    ty: ty.clone(),
                                }
                                .compile(prg, env, circuit);
                            } else {
                                return expr.compile(prg, env, circuit);
                            }
                        }
                    }
                }
                let ty_x = &x.ty;
                let ty_y = &y.ty;
                let mut x = x.compile(prg, env, circuit);
                let mut y = y.compile(prg, env, circuit);
                let bits = max(x.len(), y.len());
                extend_to_bits(&mut x, ty_x, bits);
                extend_to_bits(&mut y, ty_y, bits);
                match op {
                    Op::BitAnd => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            output_bits[i] = circuit.push_and(x[i], y[i]);
                        }
                        output_bits
                    }
                    Op::BitXor => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            output_bits[i] = circuit.push_xor(x[i], y[i]);
                        }
                        output_bits
                    }
                    Op::BitOr => {
                        let mut output_bits = vec![0; bits];
                        for i in 0..bits {
                            output_bits[i] = circuit.push_or(x[i], y[i]);
                        }
                        output_bits
                    }
                    Op::Sub => {
                        let (sum, overflow) =
                            circuit.push_subtraction_circuit(&x, &y, is_signed(ty));
                        circuit.push_panic_if(overflow, PanicReason::Overflow, meta);
                        sum
                    }
                    Op::Add => {
                        let (sum, carry, carry_prev) = circuit.push_addition_circuit(&x, &y);
                        let overflow = if is_signed(ty_x) || is_signed(ty_y) {
                            circuit.push_xor(carry, carry_prev)
                        } else {
                            carry
                        };
                        circuit.push_panic_if(overflow, PanicReason::Overflow, meta);
                        sum
                    }
                    Op::Mul => {
                        let is_result_neg = if is_signed(ty) {
                            let is_x_negative = x[0];
                            let is_y_negative = y[0];
                            let x_negated = circuit.push_negation_circuit(&x);
                            let y_negated = circuit.push_negation_circuit(&y);
                            for (i, w) in x.iter_mut().enumerate() {
                                *w = circuit.push_mux(is_x_negative, x_negated[i], *w);
                            }
                            for (i, w) in y.iter_mut().enumerate() {
                                *w = circuit.push_mux(is_y_negative, y_negated[i], *w);
                            }
                            circuit.push_xor(is_x_negative, is_y_negative)
                        } else {
                            0
                        };
                        let mut sums: Vec<Vec<GateIndex>> = vec![vec![0; bits]; bits];
                        let mut carries: Vec<Vec<GateIndex>> = vec![vec![0; bits]; bits];
                        let lsb_index = bits - 1;
                        for i in (0..bits).rev() {
                            for j in (0..bits).rev() {
                                let carry = if j == lsb_index { 0 } else { carries[i][j + 1] };
                                let z = if i == lsb_index {
                                    0
                                } else if j == 0 {
                                    carries[i + 1][j]
                                } else {
                                    sums[i + 1][j - 1]
                                };
                                let (sum, carry) = circuit.push_multiplier(x[i], y[j], z, carry);
                                sums[i][j] = sum;
                                carries[i][j] = carry;
                            }
                        }
                        let mut overflow = carries[0][0];
                        for (i, &w) in sums[0].iter().enumerate() {
                            if i != lsb_index {
                                overflow = circuit.push_or(overflow, w);
                            }
                        }
                        let mut result = vec![0; bits];
                        for (i, s) in sums.into_iter().enumerate() {
                            result[i] = s[lsb_index];
                        }
                        if is_signed(ty) {
                            let mut all_bits_except_msb_are_zero = 1;
                            for &w in result.iter().skip(1) {
                                let not_w = circuit.push_not(w);
                                all_bits_except_msb_are_zero =
                                    circuit.push_and(all_bits_except_msb_are_zero, not_w);
                            }
                            let result_is_signed = result[0];
                            let not_all_bits_except_msb_are_zero =
                                circuit.push_not(all_bits_except_msb_are_zero);
                            let too_large_for_signed_representation = circuit
                                .push_and(result_is_signed, not_all_bits_except_msb_are_zero);
                            overflow =
                                circuit.push_or(overflow, too_large_for_signed_representation);
                            let result_negated = circuit.push_negation_circuit(&result);
                            for (i, w) in result.iter_mut().enumerate() {
                                *w = circuit.push_mux(is_result_neg, result_negated[i], *w);
                            }
                        }
                        circuit.push_panic_if(overflow, PanicReason::Overflow, meta);
                        result
                    }
                    Op::Div => {
                        let mut all_zero = 1;
                        for b in y.iter() {
                            let eq = circuit.push_eq(*b, 0);
                            all_zero = circuit.push_and(all_zero, eq);
                        }
                        circuit.push_panic_if(all_zero, PanicReason::DivByZero, meta);
                        if is_signed(ty) {
                            circuit.push_signed_division_circuit(&mut x, &mut y).0
                        } else {
                            circuit.push_unsigned_division_circuit(&x, &y).0
                        }
                    }
                    Op::Mod => {
                        let mut all_zero = 1;
                        for b in y.iter() {
                            let eq = circuit.push_eq(*b, 0);
                            all_zero = circuit.push_and(all_zero, eq);
                        }
                        circuit.push_panic_if(all_zero, PanicReason::DivByZero, meta);
                        if is_signed(ty) {
                            circuit.push_signed_division_circuit(&mut x, &mut y).1
                        } else {
                            circuit.push_unsigned_division_circuit(&x, &y).1
                        }
                    }
                    Op::GreaterThan | Op::LessThan => {
                        let is_signed_x = is_signed(ty_x);
                        let is_signed_y = is_signed(ty_y);
                        let (acc_lt, acc_gt) =
                            circuit.push_comparator_circuit(bits, &x, is_signed_x, &y, is_signed_y);

                        match op {
                            Op::GreaterThan => vec![acc_gt],
                            Op::LessThan => vec![acc_lt],
                            _ => unreachable!(),
                        }
                    }
                    Op::Eq | Op::NotEq => {
                        let mut acc = 1;
                        for i in 0..bits {
                            let eq = circuit.push_eq(x[i], y[i]);
                            acc = circuit.push_and(acc, eq);
                        }
                        match op {
                            Op::Eq => vec![acc],
                            Op::NotEq => vec![circuit.push_not(acc)],
                            _ => unreachable!(),
                        }
                    }
                    Op::ShortCircuitAnd => {
                        unreachable!("handled in the match clause one level up")
                    }
                    Op::ShortCircuitOr => {
                        unreachable!("handled in the match clause one level up")
                    }
                    Op::ShiftLeft => {
                        unreachable!("handled in the match clause one level up")
                    }
                    Op::ShiftRight => {
                        unreachable!("handled in the match clause one level up")
                    }
                }
            }
            ExprEnum::Block(stmts) => compile_block(stmts, prg, env, circuit),
            ExprEnum::FnCall(identifier, args) => {
                let fn_def = prg.fn_defs.get(identifier).unwrap();
                let mut bindings = Vec::with_capacity(fn_def.params.len());
                for (param, arg) in fn_def.params.iter().zip(args) {
                    env.push();
                    let arg = arg.compile(prg, env, circuit);
                    bindings.push((param.name.clone(), arg));
                    env.pop();
                }
                env.push();
                for (var, binding) in bindings {
                    env.let_in_current_scope(var.clone(), binding);
                }
                let body = compile_block(&fn_def.body, prg, env, circuit);
                env.pop();
                body
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.compile(prg, env, circuit);
                let panic_before_branches = circuit.peek_panic().clone();

                assert_eq!(condition.len(), 1);
                let condition = condition[0];
                let mut env_if_true = env.clone();
                let mut env_if_false = env.clone();

                let case_true = case_true.compile(prg, &mut env_if_true, circuit);
                let panic_if_true = circuit.replace_panic_with(panic_before_branches.clone());

                let case_false = case_false.compile(prg, &mut env_if_false, circuit);
                let panic_if_false = circuit.replace_panic_with(panic_before_branches);

                *env = circuit.mux_envs(condition, env_if_true, env_if_false);

                let muxed_panic = circuit.mux_panic(condition, &panic_if_true, &panic_if_false);
                circuit.replace_panic_with(muxed_panic);

                assert_eq!(case_true.len(), case_false.len());
                let mut gate_indexes = Vec::with_capacity(case_true.len());
                for i in 0..case_true.len() {
                    gate_indexes.push(circuit.push_mux(condition, case_true[i], case_false[i]));
                }
                gate_indexes
            }
            ExprEnum::Cast(ty, expr) => {
                let ty_expr = &expr.ty;
                let mut expr = expr.compile(prg, env, circuit);
                let size_after_cast = ty.size_in_bits_for_defs(prg, circuit.const_sizes());

                match size_after_cast.cmp(&expr.len()) {
                    std::cmp::Ordering::Equal => expr,
                    std::cmp::Ordering::Less => expr[(expr.len() - size_after_cast)..].to_vec(),
                    std::cmp::Ordering::Greater => {
                        extend_to_bits(&mut expr, ty_expr, size_after_cast);
                        expr
                    }
                }
            }
            ExprEnum::Range(from, to, num_ty) => {
                let size = (to - from) as usize;
                let elem_bits =
                    Type::Unsigned(*num_ty).size_in_bits_for_defs(prg, circuit.const_sizes());
                let mut array = Vec::with_capacity(elem_bits * size);
                for i in *from..*to {
                    for b in (0..elem_bits).rev() {
                        array.push((i as usize >> b) & 1);
                    }
                }
                array
            }
            ExprEnum::EnumLiteral(identifier, variant_name, variant) => {
                let enum_def = prg.enum_defs.get(identifier).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let max_size = enum_max_size(enum_def, prg, circuit.const_sizes());
                let mut wires = vec![0; max_size];
                let tag_number = enum_tag_number(enum_def, variant_name);
                for (i, wire) in wires.iter_mut().enumerate().take(tag_size) {
                    *wire = (tag_number >> (tag_size - i - 1)) & 1;
                }
                let mut w = tag_size;
                match variant {
                    VariantExprEnum::Unit => {}
                    VariantExprEnum::Tuple(fields) => {
                        for f in fields {
                            let f = f.compile(prg, env, circuit);
                            wires[w..w + f.len()].copy_from_slice(&f);
                            w += f.len();
                        }
                    }
                }
                wires
            }
            ExprEnum::Match(expr, clauses) => {
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let expr = expr.compile(prg, env, circuit);
                let mut has_prev_match = 0;
                let mut muxed_ret_expr = vec![0; bits];
                let mut muxed_panic = circuit.peek_panic().clone();
                let mut muxed_env = env.clone();
                let panic_before_match = circuit.peek_panic().clone();

                for (pattern, ret_expr) in clauses {
                    let mut env = env.clone();
                    env.push();

                    circuit.replace_panic_with(panic_before_match.clone());

                    let is_match = pattern.compile(&expr, prg, &mut env, circuit);
                    let ret_expr = ret_expr.compile(prg, &mut env, circuit);

                    let no_prev_match = circuit.push_not(has_prev_match);
                    let s = circuit.push_and(no_prev_match, is_match);

                    env.pop();

                    muxed_panic = circuit.mux_panic(s, &circuit.peek_panic().clone(), &muxed_panic);
                    muxed_env = circuit.mux_envs(s, env, muxed_env);
                    for i in 0..bits {
                        let x0 = ret_expr[i];
                        let x1 = muxed_ret_expr[i];
                        muxed_ret_expr[i] = circuit.push_mux(s, x0, x1);
                    }
                    has_prev_match = circuit.push_or(has_prev_match, is_match);
                }
                *env = muxed_env;
                circuit.replace_panic_with(muxed_panic);
                muxed_ret_expr
            }
            ExprEnum::StructAccess(struct_expr, field) => {
                if let Type::Struct(name) = &struct_expr.ty {
                    let struct_expr = struct_expr.compile(prg, env, circuit);
                    let struct_def = prg.struct_defs.get(name.as_str()).unwrap();
                    let mut bits = 0;
                    for (field_name, field_ty) in struct_def.fields.iter() {
                        let bits_of_field =
                            field_ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                        if field_name == field {
                            return struct_expr[bits..bits + bits_of_field].to_vec();
                        }
                        bits += bits_of_field;
                    }
                    panic!("No field '{field}' in {struct_def:?}");
                } else {
                    panic!("Expected {struct_expr:?} to have a struct type, but found {ty:?}");
                }
            }
            ExprEnum::StructLiteral(struct_name, fields) => {
                let fields: HashMap<_, _> = fields.iter().cloned().collect();
                let struct_def = prg.struct_defs.get(struct_name.as_str()).unwrap();
                let mut wires =
                    Vec::with_capacity(ty.size_in_bits_for_defs(prg, circuit.const_sizes()));
                for (field_name, _) in struct_def.fields.iter() {
                    let value = fields.get(field_name).unwrap();
                    wires.extend(value.compile(prg, env, circuit));
                }
                wires
            }
        }
    }
}

impl TypedPattern {
    fn compile(
        &self,
        match_expr: &[GateIndex],
        prg: &TypedProgram,
        env: &mut Env<Vec<GateIndex>>,
        circuit: &mut CircuitBuilder,
    ) -> GateIndex {
        let Pattern(pattern, _, ty) = self;
        match pattern {
            PatternEnum::Identifier(s) => {
                env.let_in_current_scope(s.clone(), match_expr.to_vec());
                1
            }
            PatternEnum::True => {
                assert_eq!(match_expr.len(), 1);
                match_expr[0]
            }
            PatternEnum::False => {
                assert_eq!(match_expr.len(), 1);
                circuit.push_not(match_expr[0])
            }
            PatternEnum::NumUnsigned(n, _) => {
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let n = unsigned_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::NumSigned(n, _) => {
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let n = signed_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let min = unsigned_as_wires(*min, bits);
                let max = unsigned_as_wires(*max, bits);
                let signed = is_signed(ty);
                let (lt_min, _) =
                    circuit.push_comparator_circuit(bits, match_expr, signed, &min, signed);
                let (_, gt_max) =
                    circuit.push_comparator_circuit(bits, match_expr, signed, &max, signed);
                let not_lt_min = circuit.push_not(lt_min);
                let not_gt_max = circuit.push_not(gt_max);
                circuit.push_and(not_lt_min, not_gt_max)
            }
            PatternEnum::SignedInclusiveRange(min, max, _) => {
                let bits = ty.size_in_bits_for_defs(prg, circuit.const_sizes());
                let min = signed_as_wires(*min, bits);
                let max = signed_as_wires(*max, bits);
                let signed = is_signed(ty);
                let (lt_min, _) =
                    circuit.push_comparator_circuit(bits, match_expr, signed, &min, signed);
                let (_, gt_max) =
                    circuit.push_comparator_circuit(bits, match_expr, signed, &max, signed);
                let not_lt_min = circuit.push_not(lt_min);
                let not_gt_max = circuit.push_not(gt_max);
                circuit.push_and(not_lt_min, not_gt_max)
            }
            PatternEnum::Tuple(fields) => {
                let mut is_match = 1;
                let mut w = 0;
                for field in fields {
                    let Pattern(_, _, field_type) = field;
                    let field_bits = field_type.size_in_bits_for_defs(prg, circuit.const_sizes());
                    let match_expr = &match_expr[w..w + field_bits];
                    let is_field_match = field.compile(match_expr, prg, env, circuit);
                    is_match = circuit.push_and(is_match, is_field_match);
                    w += field_bits;
                }
                is_match
            }
            PatternEnum::Struct(struct_name, fields)
            | PatternEnum::StructIgnoreRemaining(struct_name, fields) => {
                let fields: HashMap<_, _> = fields.iter().cloned().collect();
                let struct_def = prg.struct_defs.get(struct_name.as_str()).unwrap();
                let mut is_match = 1;
                let mut w = 0;
                for (field_name, field_type) in struct_def.fields.iter() {
                    let field_bits = field_type.size_in_bits_for_defs(prg, circuit.const_sizes());
                    if let Some(field_pattern) = fields.get(field_name) {
                        let match_expr = &match_expr[w..w + field_bits];
                        let is_field_match = field_pattern.compile(match_expr, prg, env, circuit);
                        is_match = circuit.push_and(is_match, is_field_match);
                    }
                    w += field_bits;
                }
                is_match
            }
            PatternEnum::EnumUnit(enum_name, variant_name)
            | PatternEnum::EnumTuple(enum_name, variant_name, _) => {
                let enum_def = prg.enum_defs.get(enum_name).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let tag_actual = &match_expr[0..tag_size];

                let tag_expected =
                    unsigned_as_wires(enum_tag_number(enum_def, variant_name) as u64, tag_size);

                let mut is_match = 1;
                for i in 0..tag_size {
                    let eq = circuit.push_eq(tag_expected[i], tag_actual[i]);
                    is_match = circuit.push_and(is_match, eq);
                }

                match pattern {
                    PatternEnum::EnumUnit(_, _) => {}
                    PatternEnum::EnumTuple(_, _, fields) => {
                        let mut w = tag_size;
                        let field_types = enum_def
                            .get_variant(variant_name)
                            .unwrap()
                            .types()
                            .unwrap_or_default();
                        for (field, field_type) in fields.iter().zip(field_types) {
                            let field_bits =
                                field_type.size_in_bits_for_defs(prg, circuit.const_sizes());
                            let match_expr = &match_expr[w..w + field_bits];
                            let is_field_match = field.compile(match_expr, prg, env, circuit);
                            is_match = circuit.push_and(is_match, is_field_match);
                            w += field_bits;
                        }
                    }
                    _ => unreachable!(),
                }
                is_match
            }
        }
    }
}

impl Type {
    pub(crate) fn size_in_bits_for_defs(
        &self,
        prg: &TypedProgram,
        const_sizes: &HashMap<String, usize>,
    ) -> usize {
        match self {
            Type::Bool => 1,
            Type::Unsigned(UnsignedNumType::Usize) => USIZE_BITS,
            Type::Unsigned(UnsignedNumType::U8) | Type::Signed(SignedNumType::I8) => 8,
            Type::Unsigned(UnsignedNumType::U16) | Type::Signed(SignedNumType::I16) => 16,
            Type::Unsigned(UnsignedNumType::U32) | Type::Signed(SignedNumType::I32) => 32,
            Type::Unsigned(UnsignedNumType::U64) | Type::Signed(SignedNumType::I64) => 64,
            Type::Unsigned(UnsignedNumType::Unspecified)
            | Type::Signed(SignedNumType::Unspecified) => 32,
            Type::Array(elem, size) => elem.size_in_bits_for_defs(prg, const_sizes) * size,
            Type::ArrayConst(elem, size) => {
                elem.size_in_bits_for_defs(prg, const_sizes) * const_sizes.get(size).unwrap()
            }
            Type::Tuple(values) => {
                let mut size = 0;
                for v in values {
                    size += v.size_in_bits_for_defs(prg, const_sizes)
                }
                size
            }
            Type::Fn(_, _) => panic!("Fn types cannot be directly mapped to bits"),
            Type::Struct(name) => struct_size(prg.struct_defs.get(name).unwrap(), prg, const_sizes),
            Type::Enum(name) => enum_max_size(prg.enum_defs.get(name).unwrap(), prg, const_sizes),
            Type::UntypedTopLevelDefinition(_, _) => {
                unreachable!("Untyped top level types should have been typechecked at this point")
            }
        }
    }
}

pub(crate) fn struct_size(
    struct_def: &StructDef,
    prg: &TypedProgram,
    const_sizes: &HashMap<String, usize>,
) -> usize {
    let mut total_size = 0;
    for (_, field_ty) in struct_def.fields.iter() {
        total_size += field_ty.size_in_bits_for_defs(prg, const_sizes);
    }
    total_size
}

pub(crate) fn enum_tag_number(enum_def: &EnumDef, variant: &str) -> usize {
    for (i, def) in enum_def.variants.iter().enumerate() {
        if def.variant_name() == variant {
            return i;
        }
    }
    panic!("Variant {variant} not found in enum def")
}

pub(crate) fn enum_tag_size(enum_def: &EnumDef) -> usize {
    let mut bits = 0;
    while (1 << bits) < enum_def.variants.len() {
        bits += 1;
    }
    bits
}

pub(crate) fn enum_max_size(
    enum_def: &EnumDef,
    prg: &TypedProgram,
    const_sizes: &HashMap<String, usize>,
) -> usize {
    let mut max = 0;
    for variant in enum_def.variants.iter() {
        let mut sum = 0;
        for field in variant.types().unwrap_or_default() {
            sum += field.size_in_bits_for_defs(prg, const_sizes);
        }
        if sum > max {
            max = sum;
        }
    }
    max + enum_tag_size(enum_def)
}

pub(crate) fn unsigned_to_bits(n: u64, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push(((n >> (size - 1 - i)) & 1) == 1);
    }
}

pub(crate) fn signed_to_bits(n: i64, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push(((n >> (size - 1 - i)) & 1) == 1);
    }
}

pub(crate) fn unsigned_as_wires(n: u64, size: usize) -> Vec<usize> {
    let mut bits = Vec::with_capacity(size);
    unsigned_to_bits(n, size, &mut bits);
    bits.into_iter().map(|b| b as usize).collect()
}

pub(crate) fn signed_as_wires(n: i64, size: usize) -> Vec<usize> {
    let mut bits = Vec::with_capacity(size);
    signed_to_bits(n, size, &mut bits);
    bits.into_iter().map(|b| b as usize).collect()
}

pub(crate) fn wires_as_unsigned(wires: &[bool]) -> u64 {
    let mut n = 0;
    for (i, output) in wires.iter().copied().enumerate() {
        n += (output as u64) << (wires.len() - 1 - i);
    }
    n
}

fn extend_to_bits(v: &mut Vec<usize>, ty: &Type, bits: usize) {
    if v.is_empty() {
        v.resize(bits, 0);
    } else if v.len() != bits {
        let msb = v[0];
        let old_size = v.len();
        v.resize(bits, 0);
        v.copy_within(0..old_size, bits - old_size);
        if let Type::Signed(_) = ty {
            v[0..old_size].fill(msb);
        } else {
            v[0..old_size].fill(0);
        }
    }
}

fn is_signed(ty: &Type) -> bool {
    matches!(ty, Type::Signed(_))
}
