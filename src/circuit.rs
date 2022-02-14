/// Data type to uniquely identify gates.
pub type GateIndex = usize;

/// Description of a gate executed under S-MPC.
#[derive(Clone, Debug, PartialEq)]
pub enum Gate {
    InA,
    InB,
    Xor(GateIndex, GateIndex),
    And(GateIndex, GateIndex),
}

/// Representation of a circuit evaluated by an S-MPC engine.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub gates: Vec<Gate>,
    pub output_gates: Vec<GateIndex>,
}

impl Circuit {
    pub fn eval(&self, in_a: &[bool], in_b: &[bool]) -> Vec<Option<bool>> {
        let mut output = vec![None; self.gates.len() + 2];
        let mut in_a_iter = in_a.iter();
        let mut in_b_iter = in_b.iter();
        output[0] = Some(false);
        output[1] = Some(true);
        for (w, gate) in self.gates.iter().enumerate() {
            let w = w + 2;
            let output_bit = match gate {
                Gate::InA => *in_a_iter.next().unwrap(),
                Gate::InB => *in_b_iter.next().unwrap(),
                Gate::Xor(x, y) => output[*x].unwrap() ^ output[*y].unwrap(),
                Gate::And(x, y) => output[*x].unwrap() & output[*y].unwrap(),
            };
            output[w] = Some(output_bit);
        }
        for (w, output) in output.iter_mut().enumerate() {
            if !self.output_gates.contains(&w) {
                *output = None;
            }
        }
        output
    }

    pub fn push_gate(&mut self, gate: Gate) -> GateIndex {
        self.gates.push(gate);
        self.gates.len() + 1 // because index 0 and 1 are reserved for const true/false
    }

    pub fn push_not(&mut self, x: GateIndex) -> GateIndex {
        self.push_gate(Gate::Xor(x, 1))
    }

    pub fn push_or(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_gate(Gate::Xor(x, y));
        let and = self.push_gate(Gate::And(x, y));
        self.push_gate(Gate::Xor(xor, and))
    }

    pub fn push_eq(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_gate(Gate::Xor(x, y));
        self.push_gate(Gate::Xor(xor, 1))
    }

    pub fn push_mux(&mut self, s: GateIndex, x0: GateIndex, x1: GateIndex) -> GateIndex {
        if x0 == x1 {
            return x0;
        }
        let not_s = self.push_not(s);
        let x0_selected = self.push_gate(Gate::And(x0, s));
        let x1_selected = self.push_gate(Gate::And(x1, not_s));
        self.push_gate(Gate::Xor(x0_selected, x1_selected))
    }

    pub fn push_adder(
        &mut self,
        x: GateIndex,
        y: GateIndex,
        carry: GateIndex,
    ) -> (GateIndex, GateIndex) {
        // first half-adder:
        let wire_u = self.push_gate(Gate::Xor(x, y));
        let wire_v = self.push_gate(Gate::And(x, y));
        // second half-adder:
        let wire_s = self.push_gate(Gate::Xor(wire_u, carry));
        let wire_w = self.push_gate(Gate::And(wire_u, carry));

        let carry = self.push_or(wire_v, wire_w);
        (wire_s, carry)
    }

    pub fn push_multiplier(
        &mut self,
        x: GateIndex,
        y: GateIndex,
        z: GateIndex,
        carry: GateIndex,
    ) -> (GateIndex, GateIndex) {
        let x_and_y = self.push_gate(Gate::And(x, y));
        self.push_adder(x_and_y, z, carry)
    }

    pub fn push_addition_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, GateIndex) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let mut carry = 0;
        let mut sum = vec![0; bits];
        // sequence of full adders:
        for i in (0..bits).rev() {
            let (s, c) = self.push_adder(x[i], y[i], carry);
            sum[i] = s;
            carry = c;
        }
        (sum, carry)
    }

    pub fn push_negation_circuit(&mut self, x: &[GateIndex]) -> Vec<GateIndex> {
        // flip bits and increment to get negate:
        let mut carry = 1;
        let mut neg = vec![0; x.len()];
        for i in (0..x.len()).rev() {
            let x = self.push_not(x[i]);
            // half-adder:
            neg[i] = self.push_gate(Gate::Xor(carry, x));
            carry = self.push_gate(Gate::And(carry, x));
        }
        neg
    }

    pub fn push_subtraction_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, GateIndex) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        // flip bits of y and increment y to get negative y:
        let mut carry = 1;
        let mut x_extended = vec![0; bits + 1];
        x_extended[1..].copy_from_slice(x);
        let mut z = vec![0; bits + 1];
        for i in (0..bits + 1).rev() {
            let y = if i == 0 { 1 } else { self.push_not(y[i - 1]) };
            // half-adder:
            z[i] = self.push_gate(Gate::Xor(carry, y));
            carry = self.push_gate(Gate::And(carry, y));
        }

        let (mut sum_extended, _carry) = self.push_addition_circuit(&x_extended, &z);
        let sum = sum_extended.split_off(1);
        (sum, sum_extended[0])
    }

    pub fn push_unsigned_division_circuit(
        &mut self,
        x: &[GateIndex],
        y: &[GateIndex],
    ) -> (Vec<GateIndex>, Vec<GateIndex>) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let mut quotient = vec![0; bits];
        let mut remainder = x.to_vec();
        for shift_amount in (0..bits).rev() {
            let mut overflow = 0;
            let mut y_shifted = vec![0; bits];
            for y in y.iter().copied().take(shift_amount) {
                overflow = self.push_or(overflow, y);
            }
            y_shifted[..(bits - shift_amount)]
                .clone_from_slice(&y[shift_amount..((bits - shift_amount) + shift_amount)]);

            let (x_sub, carry) = self.push_subtraction_circuit(&remainder, &y_shifted);
            let carry_or_overflow = self.push_or(carry, overflow);
            for i in 0..bits {
                remainder[i] = self.push_mux(carry_or_overflow, remainder[i], x_sub[i]);
            }
            let quotient_bit = self.push_not(carry);
            quotient[bits - shift_amount - 1] = self.push_mux(overflow, 0, quotient_bit);
        }
        (quotient, remainder)
    }

    pub fn push_signed_division_circuit(
        &mut self,
        x: &mut Vec<GateIndex>,
        y: &mut Vec<GateIndex>,
    ) -> (Vec<GateIndex>, Vec<GateIndex>) {
        assert_eq!(x.len(), y.len());
        let bits = x.len();

        let is_result_neg = self.push_gate(Gate::Xor(x[0], y[0]));
        let x_negated = self.push_negation_circuit(x);
        let x_sign_bit = x[0];
        for i in 0..bits {
            x[i] = self.push_mux(x_sign_bit, x_negated[i], x[i]);
        }
        let y_negated = self.push_negation_circuit(y);
        let y_sign_bit = y[0];
        for i in 0..bits {
            y[i] = self.push_mux(y_sign_bit, y_negated[i], y[i]);
        }
        let (mut quotient, mut remainder) = self.push_unsigned_division_circuit(x, y);
        let quot_neg = self.push_negation_circuit(&quotient);
        for i in 0..bits {
            quotient[i] = self.push_mux(is_result_neg, quot_neg[i], quotient[i]);
        }
        let rem_neg = self.push_negation_circuit(&remainder);
        for i in 0..bits {
            remainder[i] = self.push_mux(x_sign_bit, rem_neg[i], remainder[i]);
        }
        (quotient, remainder)
    }

    pub fn push_comparator_circuit(
        &mut self,
        bits: usize,
        x: &[GateIndex],
        is_x_signed: bool,
        y: &[GateIndex],
        is_y_signed: bool,
    ) -> (GateIndex, GateIndex) {
        let mut acc_gt = 0;
        let mut acc_lt = 0;
        for i in 0..bits {
            let xor = self.push_gate(Gate::Xor(x[i], y[i]));

            let xor_and_x = self.push_gate(Gate::And(xor, x[i]));
            let xor_and_y = self.push_gate(Gate::And(xor, y[i]));
            let (gt, lt) = if i == 0 && (is_x_signed || is_y_signed) {
                (xor_and_y, xor_and_x)
            } else {
                (xor_and_x, xor_and_y)
            };

            let gt = self.push_or(gt, acc_gt);
            let lt = self.push_or(lt, acc_lt);

            let not_acc_gt = self.push_not(acc_gt);
            let not_acc_lt = self.push_not(acc_lt);

            acc_gt = self.push_gate(Gate::And(gt, not_acc_lt));
            acc_lt = self.push_gate(Gate::And(lt, not_acc_gt))
        }
        (acc_lt, acc_gt)
    }
}
