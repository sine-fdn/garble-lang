use std::{cmp::max, collections::HashMap};

use crate::{
    ast::{Op, ParamDef, Type, UnaryOp},
    circuit::{Circuit, CircuitBuilder, GateIndex, Party},
    env::Env,
    typed_ast::{
        Expr, ExprEnum, FnDef, Pattern, PatternEnum, Program, VariantExpr, VariantExprEnum,
    },
};

impl Program {
    pub fn compile(&self) -> Circuit {
        let mut fns = HashMap::new();
        for (fn_name, fn_def) in self.fn_defs.iter() {
            fns.insert(fn_name.clone(), fn_def);
        }
        let mut env = Env::new();
        let mut input_gates = vec![];
        let mut wire = 2;
        for (party, ParamDef(identifier, ty)) in self.main.params.iter() {
            let type_size = ty.size_in_bits();
            let mut wires = Vec::with_capacity(type_size);
            for _i in 0..type_size {
                input_gates.push(*party);
                wires.push(wire);
                wire += 1;
            }
            env.set(identifier.clone(), wires);
        }
        let mut enums = HashMap::new();
        for (enum_name, enum_def) in &self.enum_defs {
            let mut variants = HashMap::new();
            for variant in &enum_def.variants {
                let types = variant.types().unwrap_or_default();
                variants.insert(variant.variant_name().to_string(), types);
            }
            enums.insert(enum_name.clone(), variants);
        }
        let mut circuit = CircuitBuilder { input_gates, gates: vec![] };
        let output_gates = self
            .main
            .body
            .compile(&enums, &fns, &mut env, &mut circuit);
        circuit.build(output_gates)
    }
}

fn extend_to_bits(v: &mut Vec<usize>, ty: &Type, bits: usize) {
    if v.len() != bits {
        let msb = v[0];
        let old_size = v.len();
        v.resize(bits, 0);
        v.copy_within(0..old_size, bits - old_size);
        if let Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 = ty {
            v[0..old_size].fill(msb);
        } else {
            v[0..old_size].fill(0);
        }
    }
}

impl Expr {
    fn compile(
        &self,
        enums: &HashMap<String, HashMap<String, Vec<Type>>>,
        fns: &HashMap<String, &FnDef>,
        env: &mut Env<Vec<GateIndex>>,
        circuit: &mut CircuitBuilder,
    ) -> Vec<GateIndex> {
        let Expr(expr, ty, meta) = self;
        match expr {
            ExprEnum::True => {
                vec![1]
            }
            ExprEnum::False => {
                vec![0]
            }
            ExprEnum::NumUnsigned(n) => {
                let mut bits = Vec::with_capacity(ty.size_in_bits());
                unsigned_to_bits(*n, ty.size_in_bits(), &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::NumSigned(n) => {
                let mut bits = Vec::with_capacity(ty.size_in_bits());
                signed_to_bits(*n, ty.size_in_bits(), &mut bits);
                bits.into_iter().map(|b| b as usize).collect()
            }
            ExprEnum::Identifier(s) => env.get(s).unwrap(),
            ExprEnum::ArrayLiteral(elem, size) => {
                let elem_ty = elem.1.clone();
                let mut elem = elem.compile(enums, fns, env, circuit);
                extend_to_bits(&mut elem, &elem_ty, elem_ty.size_in_bits());
                let bits = ty.size_in_bits();
                let mut array = Vec::with_capacity(bits);
                for _ in 0..*size {
                    array.extend_from_slice(&elem);
                }
                array
            }
            ExprEnum::ArrayAccess(array, index) => {
                let elem_bits = ty.size_in_bits();
                let mut array = array.compile(enums, fns, env, circuit);
                let mut index = index.compile(enums, fns, env, circuit);
                extend_to_bits(&mut index, &Type::Usize, Type::Usize.size_in_bits());
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
                array
            }
            ExprEnum::ArrayAssignment(array, index, value) => {
                let (elem_ty, size) = match ty {
                    Type::Array(elem_ty, size) => (elem_ty, size),
                    _ => panic!(
                        "Expected array assignment to have an array type, but found {:?}",
                        ty
                    ),
                };
                let mut array = array.compile(enums, fns, env, circuit);
                let mut index = index.compile(enums, fns, env, circuit);
                let value = value.compile(enums, fns, env, circuit);
                extend_to_bits(&mut index, &Type::Usize, Type::Usize.size_in_bits());
                let elem_bits = elem_ty.size_in_bits();

                let mut index_negated = vec![0; index.len()];
                for (i, index) in index.iter().copied().enumerate() {
                    index_negated[i] = circuit.push_not(index);
                }
                // for each array element...
                for i in 0..*size {
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
                array
            }
            ExprEnum::TupleLiteral(tuple) => {
                let mut wires = Vec::with_capacity(ty.size_in_bits());
                for value in tuple {
                    wires.extend(value.compile(enums, fns, env, circuit));
                }
                wires
            }
            ExprEnum::TupleAccess(tuple, index) => {
                let (wires_before, wires_at_index) = match &tuple.1 {
                    Type::Tuple(values) => {
                        let mut wires_before = 0;
                        for v in values[0..*index].iter() {
                            wires_before += v.size_in_bits();
                        }
                        (wires_before, values[*index].size_in_bits())
                    }
                    _ => panic!("Expected a tuple type, but found {:?}", tuple.1),
                };
                let tuple = tuple.compile(enums, fns, env, circuit);
                tuple[wires_before..wires_before + wires_at_index].to_vec()
            }
            ExprEnum::UnaryOp(UnaryOp::Neg, x) => {
                let x = x.compile(enums, fns, env, circuit);
                circuit.push_negation_circuit(&x)
            }
            ExprEnum::UnaryOp(UnaryOp::Not, x) => {
                let x = x.compile(enums, fns, env, circuit);
                let mut flipped = vec![0; x.len()];
                for (i, x) in x.iter().enumerate() {
                    flipped[i] = circuit.push_not(*x);
                }
                flipped
            }
            ExprEnum::Op(op @ (Op::ShiftLeft | Op::ShiftRight), x, y) => {
                let x = x.compile(enums, fns, env, circuit);
                let y = y.compile(enums, fns, env, circuit);
                assert_eq!(y.len(), 8);
                let bits = x.len();
                let bit_to_shift_in = x[0];
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
                bits_unshifted
            }
            ExprEnum::Op(op, x, y) => {
                let ty_x = &x.1;
                let ty_y = &y.1;
                let mut x = x.compile(enums, fns, env, circuit);
                let mut y = y.compile(enums, fns, env, circuit);
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
                            let xor = circuit.push_xor(x[i], y[i]);
                            let and = circuit.push_and(x[i], y[i]);
                            let or = circuit.push_xor(xor, and);
                            output_bits[i] = or;
                        }
                        output_bits
                    }
                    Op::Sub => circuit.push_subtraction_circuit(&x, &y).0,
                    Op::Add => circuit.push_addition_circuit(&x, &y).0,
                    Op::Mul => {
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
                        let mut result = vec![0; bits];
                        for (i, s) in sums.into_iter().enumerate() {
                            result[i] = s[lsb_index];
                        }
                        result
                    }
                    Op::Div => {
                        if is_signed(ty) {
                            circuit.push_signed_division_circuit(&mut x, &mut y).0
                        } else {
                            circuit.push_unsigned_division_circuit(&x, &y).0
                        }
                    }
                    Op::Mod => {
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
                    Op::ShiftLeft => {
                        unreachable!("handled in the match clause one layer up")
                    }
                    Op::ShiftRight => {
                        unreachable!("handled in the match clause one layer up")
                    }
                }
            }
            ExprEnum::Let(var, binding, body) => {
                let binding = binding.compile(enums, fns, env, circuit);
                env.push();
                env.set(var.clone(), binding);
                let body = body.compile(enums, fns, env, circuit);
                env.pop();
                body
            }
            ExprEnum::FnCall(identifier, args) => {
                let fn_def = *fns.get(identifier).unwrap();
                let mut body = fn_def.body.clone();
                for (ParamDef(identifier, ty), arg) in fn_def.params.iter().zip(args) {
                    let let_expr =
                        ExprEnum::Let(identifier.clone(), Box::new(arg.clone()), Box::new(body));
                    body = Expr(let_expr, ty.clone(), *meta)
                }
                env.push();
                let body = body.compile(enums, fns, env, circuit);
                env.pop();
                body
            }
            ExprEnum::If(condition, case_true, case_false) => {
                let condition = condition.compile(enums, fns, env, circuit);
                let case_true = case_true.compile(enums, fns, env, circuit);
                let case_false = case_false.compile(enums, fns, env, circuit);
                assert_eq!(condition.len(), 1);
                assert_eq!(case_true.len(), case_false.len());
                let condition = condition[0];
                let not_condition = circuit.push_not(condition);
                let mut gate_indexes = Vec::with_capacity(case_true.len());
                for i in 0..case_true.len() {
                    let case_true = case_true[i];
                    let case_false = case_false[i];
                    let gate_if_true = circuit.push_and(case_true, condition);
                    let gate_if_false = circuit.push_and(case_false, not_condition);
                    gate_indexes.push(circuit.push_xor(gate_if_true, gate_if_false));
                }
                gate_indexes
            }
            ExprEnum::Cast(ty, expr) => {
                let ty_expr = &expr.1;
                let mut expr = expr.compile(enums, fns, env, circuit);
                let size_after_cast = ty.size_in_bits();

                match size_after_cast.cmp(&expr.len()) {
                    std::cmp::Ordering::Equal => expr,
                    std::cmp::Ordering::Less => expr[(expr.len() - size_after_cast)..].to_vec(),
                    std::cmp::Ordering::Greater => {
                        extend_to_bits(&mut expr, ty_expr, size_after_cast);
                        expr
                    }
                }
            }
            ExprEnum::Fold(array, init, closure) => {
                let array = array.compile(enums, fns, env, circuit);
                let mut init = init.compile(enums, fns, env, circuit);

                let ParamDef(init_identifier, init_ty) = &closure.params[0];
                let ParamDef(elem_identifier, elem_ty) = &closure.params[1];
                let elem_bits = elem_ty.size_in_bits();
                extend_to_bits(&mut init, init_ty, init_ty.size_in_bits());

                let mut acc = init;
                let mut i = 0;
                while i < array.len() {
                    let elem = &array[i..i + elem_bits];
                    env.push();
                    env.set(init_identifier.clone(), acc);
                    env.set(elem_identifier.clone(), elem.to_vec());
                    acc = closure.body.compile(enums, fns, env, circuit);
                    env.pop();
                    i += elem_bits;
                }
                acc
            }
            ExprEnum::Map(array, closure) => {
                let array = array.compile(enums, fns, env, circuit);

                let ParamDef(elem_identifier, elem_ty) = &closure.params[0];
                let elem_in_bits = elem_ty.size_in_bits();
                let elem_out_bits = closure.ty.size_in_bits();
                let size = array.len() / elem_in_bits;

                let mut i = 0;
                let mut result = Vec::with_capacity(elem_out_bits * size);
                while i < array.len() {
                    let elem_in = &array[i..i + elem_in_bits];
                    env.push();
                    env.set(elem_identifier.clone(), elem_in.to_vec());
                    let elem_out = closure.body.compile(enums, fns, env, circuit);
                    result.extend(elem_out);
                    env.pop();
                    i += elem_in_bits;
                }
                result
            }
            ExprEnum::Range(from, to) => {
                let size = to - from;
                let elem_bits = Type::Usize.size_in_bits();
                let mut array = Vec::with_capacity(elem_bits * size);
                for i in *from..*to {
                    for b in (0..elem_bits).rev() {
                        array.push((i >> b) & 1);
                    }
                }
                array
            }
            ExprEnum::EnumLiteral(identifier, variant) => {
                let enum_def = enums.get(identifier).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let max_size = enum_max_size(enum_def);
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
                            let f = f.compile(enums, fns, env, circuit);
                            wires[w..w + f.len()].copy_from_slice(&f);
                            w += f.len();
                        }
                    }
                }
                wires
            }
            ExprEnum::Match(expr, clauses) => {
                let bits = ty.size_in_bits();
                let expr = expr.compile(enums, fns, env, circuit);
                let mut has_prev_match = 0;
                let mut muxed_ret_expr = vec![0; bits];

                for (pattern, ret_expr) in clauses {
                    env.push();
                    let is_match = pattern.compile(&expr, enums, fns, env, circuit);
                    let ret_expr = ret_expr.compile(enums, fns, env, circuit);

                    let no_prev_match = circuit.push_not(has_prev_match);
                    let s = circuit.push_and(no_prev_match, is_match);
                    for i in 0..bits {
                        let x0 = ret_expr[i];
                        let x1 = muxed_ret_expr[i];
                        muxed_ret_expr[i] = circuit.push_mux(s, x0, x1);
                    }
                    has_prev_match = circuit.push_or(has_prev_match, is_match);
                    env.pop();
                }
                muxed_ret_expr
            }
        }
    }
}

impl Pattern {
    fn compile(
        &self,
        match_expr: &[GateIndex],
        enums: &HashMap<String, HashMap<String, Vec<Type>>>,
        fns: &HashMap<String, &FnDef>,
        env: &mut Env<Vec<GateIndex>>,
        circuit: &mut CircuitBuilder,
    ) -> GateIndex {
        let Pattern(pattern, ty, _) = self;
        match pattern {
            PatternEnum::Identifier(s) => {
                env.set(s.clone(), match_expr.to_vec());
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
            PatternEnum::NumUnsigned(n) => {
                let bits = ty.size_in_bits();
                let n = unsigned_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::NumSigned(n) => {
                let bits = ty.size_in_bits();
                let n = signed_as_wires(*n, bits);
                let mut acc = 1;
                for i in 0..bits {
                    let eq = circuit.push_eq(n[i], match_expr[i]);
                    acc = circuit.push_and(acc, eq);
                }
                acc
            }
            PatternEnum::UnsignedInclusiveRange(min, max) => {
                let bits = ty.size_in_bits();
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
            PatternEnum::SignedInclusiveRange(min, max) => {
                let bits = ty.size_in_bits();
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
                    let Pattern(_, field_type, _) = field;
                    let field_bits = match field_type {
                        Type::Enum(enum_name) => enum_max_size(enums.get(enum_name).unwrap()),
                        _ => field_type.size_in_bits(),
                    };
                    let match_expr = &match_expr[w..w + field_bits];
                    let is_field_match = field.compile(match_expr, enums, fns, env, circuit);
                    is_match = circuit.push_and(is_match, is_field_match);
                    w += field_bits;
                }
                is_match
            }
            PatternEnum::EnumUnit(enum_name, variant_name)
            | PatternEnum::EnumTuple(enum_name, variant_name, _) => {
                let enum_def = enums.get(enum_name).unwrap();
                let tag_size = enum_tag_size(enum_def);
                let tag_actual = &match_expr[0..tag_size];

                let tag_expected =
                    unsigned_as_wires(enum_tag_number(enum_def, variant_name) as u128, tag_size);

                let mut is_match = 1;
                for i in 0..tag_size {
                    let eq = circuit.push_eq(tag_expected[i], tag_actual[i]);
                    is_match = circuit.push_and(is_match, eq);
                }

                match pattern {
                    PatternEnum::EnumUnit(_, _) => {}
                    PatternEnum::EnumTuple(_, _, fields) => {
                        let mut w = tag_size;
                        let field_types = enum_def.get(variant_name).unwrap();
                        for (field, field_type) in fields.iter().zip(field_types) {
                            let field_bits = match field_type {
                                Type::Enum(enum_name) => {
                                    enum_max_size(enums.get(enum_name).unwrap())
                                }
                                _ => field_type.size_in_bits(),
                            };
                            let match_expr = &match_expr[w..w + field_bits];
                            let is_field_match =
                                field.compile(match_expr, enums, fns, env, circuit);
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

fn is_signed(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128
    )
}

fn enum_tag_number(enum_def: &HashMap<String, Vec<Type>>, variant: &str) -> usize {
    for (i, (name_in_def, _)) in enum_def.iter().enumerate() {
        if name_in_def.as_str() == variant {
            return i;
        }
    }
    panic!("Variant {} not found in enum def", variant)
}

fn enum_tag_size(enum_def: &HashMap<String, Vec<Type>>) -> usize {
    let mut bits = 0;
    while (1 << bits) < enum_def.values().len() {
        bits += 1;
    }
    bits
}

fn enum_max_size(enum_def: &HashMap<String, Vec<Type>>) -> usize {
    let mut max = 0;
    for variant in enum_def.values() {
        let mut sum = 0;
        for field in variant {
            sum += field.size_in_bits();
        }
        if sum > max {
            max = sum;
        }
    }
    max + enum_tag_size(enum_def)
}

impl Type {
    fn size_in_bits(&self) -> usize {
        match self {
            Type::Bool => 1,
            Type::Usize => usize::BITS as usize,
            Type::U8 | Type::I8 => 8,
            Type::U16 | Type::I16 => 16,
            Type::U32 | Type::I32 => 32,
            Type::U64 | Type::I64 => 64,
            Type::U128 | Type::I128 => 128,
            Type::Array(elem, size) => elem.size_in_bits() * size,
            Type::Tuple(values) => {
                let mut size = 0;
                for v in values {
                    size += v.size_in_bits()
                }
                size
            }
            Type::Fn(_, _) => panic!("Fn types cannot be directly mapped to bits"),
            Type::Enum(_) => panic!("Enum types need to be looked up in the enum hashmap"),
        }
    }
}

pub struct Computation {
    circuit: Circuit,
    in_a: Vec<bool>,
    in_b: Vec<bool>,
    output: Option<Vec<Option<bool>>>,
}

impl From<Circuit> for Computation {
    fn from(circuit: Circuit) -> Self {
        Self {
            circuit,
            in_a: vec![],
            in_b: vec![],
            output: None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ComputeError {
    UnexpectedNumberOfInputsFromPartyA(usize),
    UnexpectedNumberOfInputsFromPartyB(usize),
    OutputHasNotBeenComputed,
    OutputTypeMismatch { expected: Type, actual_bits: usize },
}

impl Computation {
    pub fn run(&mut self) -> Result<(), ComputeError> {
        let mut expected_in_a_len = 0;
        let mut expected_in_b_len = 0;
        for party in self.circuit.input_gates.iter() {
            match party {
                Party::A => expected_in_a_len += 1,
                Party::B => expected_in_b_len += 1,
            }
        }
        if self.in_a.len() != expected_in_a_len {
            return Err(ComputeError::UnexpectedNumberOfInputsFromPartyA(
                self.in_a.len(),
            ));
        }
        if self.in_b.len() != expected_in_b_len {
            return Err(ComputeError::UnexpectedNumberOfInputsFromPartyB(
                self.in_b.len(),
            ));
        }
        self.output = Some(self.circuit.eval(&self.in_a, &self.in_b));
        self.in_a.clear();
        self.in_b.clear();
        Ok(())
    }

    fn get_input(&mut self, p: Party) -> &mut Vec<bool> {
        match p {
            Party::A => &mut self.in_a,
            Party::B => &mut self.in_b,
        }
    }

    fn get_output(&self) -> Result<Vec<bool>, ComputeError> {
        if let Some(output) = &self.output {
            let mut output_bits = Vec::with_capacity(self.circuit.output_gates.len());
            for output_gate in &self.circuit.output_gates {
                output_bits.push(output[*output_gate].unwrap());
            }
            Ok(output_bits)
        } else {
            Err(ComputeError::OutputHasNotBeenComputed)
        }
    }

    pub fn set_bool(&mut self, p: Party, b: bool) {
        let inputs = self.get_input(p);
        inputs.push(b);
    }

    pub fn get_bool(&self) -> Result<bool, ComputeError> {
        let output = self.get_output()?;
        if output.len() == 1 {
            Ok(output[0])
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: Type::Bool,
                actual_bits: output.len(),
            })
        }
    }

    pub fn set_usize(&mut self, p: Party, n: usize) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, usize::BITS as usize, inputs);
    }

    pub fn set_u8(&mut self, p: Party, n: u8) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 8, inputs);
    }

    pub fn set_u16(&mut self, p: Party, n: u16) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 16, inputs);
    }

    pub fn set_u32(&mut self, p: Party, n: u32) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 32, inputs);
    }

    pub fn set_u64(&mut self, p: Party, n: u64) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n as u128, 64, inputs);
    }

    pub fn set_u128(&mut self, p: Party, n: u128) {
        let inputs = self.get_input(p);
        unsigned_to_bits(n, 128, inputs);
    }

    pub fn set_i8(&mut self, p: Party, n: i8) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 8, inputs);
    }

    pub fn set_i16(&mut self, p: Party, n: i16) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 16, inputs);
    }

    pub fn set_i32(&mut self, p: Party, n: i32) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 32, inputs);
    }

    pub fn set_i64(&mut self, p: Party, n: i64) {
        let inputs = self.get_input(p);
        signed_to_bits(n as i128, 64, inputs);
    }

    pub fn set_i128(&mut self, p: Party, n: i128) {
        let inputs = self.get_input(p);
        signed_to_bits(n, 128, inputs);
    }

    fn get_unsigned(&self, ty: Type) -> Result<u128, ComputeError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits();
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().take(size).enumerate() {
                n += (output as u128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    fn get_signed(&self, ty: Type) -> Result<i128, ComputeError> {
        let output = self.get_output()?;
        let size = ty.size_in_bits();
        if output.len() == size {
            let mut n = 0;
            for (i, output) in output.iter().copied().enumerate().take(size) {
                n += (output as i128) << (size - 1 - i);
            }
            Ok(n)
        } else {
            Err(ComputeError::OutputTypeMismatch {
                expected: ty,
                actual_bits: output.len(),
            })
        }
    }

    pub fn get_usize(&self) -> Result<usize, ComputeError> {
        self.get_unsigned(Type::Usize).map(|n| n as usize)
    }

    pub fn get_u8(&self) -> Result<u8, ComputeError> {
        self.get_unsigned(Type::U8).map(|n| n as u8)
    }

    pub fn get_u16(&self) -> Result<u16, ComputeError> {
        self.get_unsigned(Type::U16).map(|n| n as u16)
    }

    pub fn get_u32(&self) -> Result<u32, ComputeError> {
        self.get_unsigned(Type::U32).map(|n| n as u32)
    }

    pub fn get_u64(&self) -> Result<u64, ComputeError> {
        self.get_unsigned(Type::U64).map(|n| n as u64)
    }

    pub fn get_u128(&self) -> Result<u128, ComputeError> {
        self.get_unsigned(Type::U128)
    }

    pub fn get_i8(&self) -> Result<i8, ComputeError> {
        self.get_signed(Type::I8).map(|n| n as i8)
    }

    pub fn get_i16(&self) -> Result<i16, ComputeError> {
        self.get_signed(Type::I16).map(|n| n as i16)
    }

    pub fn get_i32(&self) -> Result<i32, ComputeError> {
        self.get_signed(Type::I32).map(|n| n as i32)
    }

    pub fn get_i64(&self) -> Result<i64, ComputeError> {
        self.get_signed(Type::I64).map(|n| n as i64)
    }

    pub fn get_i128(&self) -> Result<i128, ComputeError> {
        self.get_signed(Type::I128)
    }
}

fn unsigned_to_bits(n: u128, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push((n >> (size - 1 - i) & 1) == 1);
    }
}

fn signed_to_bits(n: i128, size: usize, bits: &mut Vec<bool>) {
    for i in 0..size {
        bits.push((n >> (size - 1 - i) & 1) == 1);
    }
}

fn unsigned_as_wires(n: u128, size: usize) -> Vec<usize> {
    let mut bits = Vec::with_capacity(size);
    unsigned_to_bits(n, size, &mut bits);
    bits.into_iter().map(|b| b as usize).collect()
}

fn signed_as_wires(n: i128, size: usize) -> Vec<usize> {
    let mut bits = Vec::with_capacity(size);
    signed_to_bits(n, size, &mut bits);
    bits.into_iter().map(|b| b as usize).collect()
}
