//! Compiles a [`crate::ast::Program`] to a [`crate::circuit::Circuit`].

use std::{cmp::max, collections::HashMap};

use crate::{
    ast::{
        EnumDef, ExprEnum, Op, Pattern, PatternEnum, StmtEnum, StructDef, Type, UnaryOp,
        VariantExpr, VariantExprEnum,
    },
    circuit::{Circuit, CircuitBuilder, GateIndex, PanicReason, PanicResult, USIZE_BITS},
    env::Env,
    token::{SignedNumType, UnsignedNumType},
    TypedExpr, TypedFnDef, TypedPattern, TypedProgram, TypedStmt,
};

/// An error that occurred during compilation.
#[derive(Debug, Clone)]
pub enum CompilerError {
    /// The specified function could not be compiled, as it was not found in the program.
    FnNotFound(String),
}

impl std::fmt::Display for CompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompilerError::FnNotFound(fn_name) => f.write_fmt(format_args!(
                "Could not find any function with name '{fn_name}'"
            )),
        }
    }
}

impl TypedProgram {
    /// Compiles the (type-checked) program, producing a circuit of gates.
    ///
    /// Assumes that the input program has been correctly type-checked and **panics** if
    /// incompatible types are found that should have been caught by the type-checker.
    pub fn compile(&self, fn_name: &str) -> Result<(Circuit, &TypedFnDef), CompilerError> {
        let mut env = Env::new();
        let mut input_gates = vec![];
        let mut wire = 2;
        if let Some(fn_def) = self.fn_defs.get(fn_name) {
            for param in fn_def.params.iter() {
                let type_size = param.ty.size_in_bits_for_defs(self);
                let mut wires = Vec::with_capacity(type_size);
                for _ in 0..type_size {
                    wires.push(wire);
                    wire += 1;
                }
                input_gates.push(type_size);
                env.let_in_current_scope(param.name.clone(), wires);
            }
            let mut circuit = CircuitBuilder::new(input_gates);
            let output_gates = compile_block(&fn_def.body, self, &mut env, &mut circuit);
            Ok((circuit.build(output_gates), fn_def))
        } else {
            Err(CompilerError::FnNotFound(fn_name.to_string()))
        }
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
                let elem_bits = value.ty.size_in_bits_for_defs(prg);
                let mut array = env.get(identifier).unwrap();
                let size = array.len() / elem_bits;
                let mut index = index.compile(prg, env, circuit);
                let value = value.compile(prg, env, circuit);
                let index_bits = Type::Unsigned(UnsignedNumType::Usize).size_in_bits_for_defs(prg);
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
            StmtEnum::ForEachLoop(var, array, body) => {
                let elem_in_bits = match &array.ty {
                    Type::Array(elem_ty, _size) => elem_ty.size_in_bits_for_defs(prg),
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                env.push();
                let array = array.compile(prg, env, circuit);

                let mut i = 0;
                while i < array.len() {
                    let binding = &array[i..i + elem_in_bits];
                    env.let_in_current_scope(var.clone(), binding.to_vec());

                    for stmt in body {
                        stmt.compile(prg, env, circuit);
                    }
                    i += elem_in_bits;
                }
                env.pop();
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
                let mut bits = Vec::with_capacity(ty.size_in_bits_for_defs(prg));
                unsigned_to_bits(*n, ty.size_in_bits_for_defs(prg), &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::NumSigned(n, _) => {
                let mut bits = Vec::with_capacity(ty.size_in_bits_for_defs(prg));
                signed_to_bits(*n, ty.size_in_bits_for_defs(prg), &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::Identifier(s) => env.get(s).unwrap(),
            ExprEnum::ArrayLiteral(elems) => {
                let mut wires = Vec::with_capacity(ty.size_in_bits_for_defs(prg));
                for elem in elems {
                    wires.extend(elem.compile(prg, env, circuit));
                }
                wires
            }
            ExprEnum::ArrayRepeatLiteral(elem, size) => {
                let elem_ty = elem.ty.clone();
                let mut elem = elem.compile(prg, env, circuit);
                extend_to_bits(&mut elem, &elem_ty, elem_ty.size_in_bits_for_defs(prg));
                let bits = ty.size_in_bits_for_defs(prg);
                let mut array = Vec::with_capacity(bits);
                for _ in 0..*size {
                    array.extend_from_slice(&elem);
                }
                array
            }
            ExprEnum::ArrayAccess(array, index) => {
                let num_elems = match &array.ty {
                    Type::Array(_, size) => *size,
                    _ => panic!("Found a non-array value in an array access expr"),
                };
                let elem_bits = ty.size_in_bits_for_defs(prg);
                let mut array = array.compile(prg, env, circuit);
                let mut index = index.compile(prg, env, circuit);
                let index_bits = Type::Unsigned(UnsignedNumType::Usize).size_in_bits_for_defs(prg);
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
                let mut wires = Vec::with_capacity(ty.size_in_bits_for_defs(prg));
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
                            wires_before += v.size_in_bits_for_defs(prg);
                        }
                        (wires_before, values[*index].size_in_bits_for_defs(prg))
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
                let size_after_cast = ty.size_in_bits_for_defs(prg);

                match size_after_cast.cmp(&expr.len()) {
                    std::cmp::Ordering::Equal => expr,
                    std::cmp::Ordering::Less => expr[(expr.len() - size_after_cast)..].to_vec(),
                    std::cmp::Ordering::Greater => {
                        extend_to_bits(&mut expr, ty_expr, size_after_cast);
                        expr
                    }
                }
            }
            ExprEnum::Range((from, elem_ty), (to, _)) => {
                let size = (to - from) as usize;
                let elem_bits = Type::Unsigned(*elem_ty).size_in_bits_for_defs(prg);
                let mut array = Vec::with_capacity(elem_bits * size);
                for i in *from..*to {
                    for b in (0..elem_bits).rev() {
                        array.push((i as usize >> b) & 1);
                    }
                }
                array
            }
            ExprEnum::EnumLiteral(identifier, variant) => {
                let enum_def = prg.enum_defs.get(identifier).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let max_size = enum_max_size(enum_def, prg);
                let mut wires = vec![0; max_size];
                let VariantExpr(variant_name, variant, _) = variant.as_ref();
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
                let bits = ty.size_in_bits_for_defs(prg);
                let expr = expr.compile(prg, env, circuit);
                let mut has_prev_match = 0;
                let mut muxed_ret_expr = vec![0; bits];
                let mut muxed_panic = circuit.peek_panic().clone();
                let mut muxed_env = env.clone();

                for (pattern, ret_expr) in clauses {
                    let mut env = env.clone();
                    env.push();

                    circuit.replace_panic_with(PanicResult::ok());

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
                        let bits_of_field = field_ty.size_in_bits_for_defs(prg);
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
                let mut wires = Vec::with_capacity(ty.size_in_bits_for_defs(prg));
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
                let bits = ty.size_in_bits_for_defs(prg);
                let n = unsigned_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::NumSigned(n, _) => {
                let bits = ty.size_in_bits_for_defs(prg);
                let n = signed_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::UnsignedInclusiveRange(min, max, _) => {
                let bits = ty.size_in_bits_for_defs(prg);
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
                let bits = ty.size_in_bits_for_defs(prg);
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
                    let field_bits = field_type.size_in_bits_for_defs(prg);
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
                    let field_bits = field_type.size_in_bits_for_defs(prg);
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
                            let field_bits = field_type.size_in_bits_for_defs(prg);
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
    pub(crate) fn size_in_bits_for_defs(&self, prg: &TypedProgram) -> usize {
        match self {
            Type::Bool => 1,
            Type::Unsigned(UnsignedNumType::Usize) => USIZE_BITS,
            Type::Unsigned(UnsignedNumType::U8) | Type::Signed(SignedNumType::I8) => 8,
            Type::Unsigned(UnsignedNumType::U16) | Type::Signed(SignedNumType::I16) => 16,
            Type::Unsigned(UnsignedNumType::U32) | Type::Signed(SignedNumType::I32) => 32,
            Type::Unsigned(UnsignedNumType::U64) | Type::Signed(SignedNumType::I64) => 64,
            Type::Array(elem, size) => elem.size_in_bits_for_defs(prg) * size,
            Type::Tuple(values) => {
                let mut size = 0;
                for v in values {
                    size += v.size_in_bits_for_defs(prg)
                }
                size
            }
            Type::Fn(_, _) => panic!("Fn types cannot be directly mapped to bits"),
            Type::Struct(name) => struct_size(prg.struct_defs.get(name).unwrap(), prg),
            Type::Enum(name) => enum_max_size(prg.enum_defs.get(name).unwrap(), prg),
            Type::UntypedTopLevelDefinition(_, _) => {
                unreachable!("Untyped top level types should have been typechecked at this point")
            }
        }
    }
}

pub(crate) fn struct_size(struct_def: &StructDef, prg: &TypedProgram) -> usize {
    let mut total_size = 0;
    for (_, field_ty) in struct_def.fields.iter() {
        total_size += field_ty.size_in_bits_for_defs(prg);
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

pub(crate) fn enum_max_size(enum_def: &EnumDef, prg: &TypedProgram) -> usize {
    let mut max = 0;
    for variant in enum_def.variants.iter() {
        let mut sum = 0;
        for field in variant.types().unwrap_or_default() {
            sum += field.size_in_bits_for_defs(prg);
        }
        if sum > max {
            max = sum;
        }
    }
    max + enum_tag_size(enum_def)
}

pub(crate) fn unsigned_to_bits(n: u64, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push((n >> (size - 1 - i) & 1) == 1);
    }
}

pub(crate) fn signed_to_bits(n: i64, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push((n >> (size - 1 - i) & 1) == 1);
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
