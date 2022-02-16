/// Data type to uniquely identify gates.
pub type GateIndex = usize;

/// Description of a gate executed under S-MPC.
#[derive(Clone, Debug, PartialEq)]
pub enum Gate {
    Xor(GateIndex, GateIndex),
    And(GateIndex, GateIndex),
    Not(GateIndex),
}

/// Representation of a circuit evaluated by an S-MPC engine.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub input_gates: Vec<usize>,
    pub gates: Vec<Gate>,
    pub output_gates: Vec<GateIndex>,
}

impl Circuit {
    pub fn eval(&self, inputs: &[Vec<bool>]) -> Vec<Option<bool>> {
        let mut input_len = 0;
        for p in self.input_gates.iter() {
            input_len += p;
        }
        let mut output = vec![None; input_len + self.gates.len()];
        let inputs: Vec<_> = inputs.iter().map(|inputs| inputs.iter()).collect();
        let mut i = 0;
        if self.input_gates.len() != inputs.len() {
            panic!(
                "Circuit was built for {} parties, but found {} inputs",
                self.input_gates.len(),
                inputs.len()
            );
        }
        for p in 0..self.input_gates.len() {
            if self.input_gates[p] != inputs[p].len() {
                panic!(
                    "Expected {} input bits for party {}, but found {}",
                    self.input_gates[p],
                    p,
                    inputs[p].len()
                );
            }
            for bit in inputs[p].as_slice() {
                output[i] = Some(*bit);
                i += 1;
            }
        }
        for (w, gate) in self.gates.iter().enumerate() {
            let w = w + i;
            let output_bit = match gate {
                Gate::Xor(x, y) => output[*x].unwrap() ^ output[*y].unwrap(),
                Gate::And(x, y) => output[*x].unwrap() & output[*y].unwrap(),
                Gate::Not(x) => !output[*x].unwrap(),
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
}

#[derive(Clone, Debug, PartialEq)]
pub enum BuilderGate {
    Xor(GateIndex, GateIndex),
    And(GateIndex, GateIndex),
}

#[derive(Clone, Debug)]
pub struct CircuitBuilder {
    input_gates: Vec<usize>,
    gates: Vec<BuilderGate>,
    gate_counter: usize,
}

impl CircuitBuilder {
    pub fn new(input_gates: Vec<usize>) -> Self {
        let mut gate_counter = 2; // for const true and false
        for input_gates_of_party in input_gates.iter() {
            gate_counter += input_gates_of_party;
        }
        Self {
            input_gates,
            gates: vec![],
            gate_counter,
        }
    }

    pub fn build(self, output_gates: Vec<GateIndex>) -> Circuit {
        let mut input_shift = 0;
        for p in self.input_gates.iter() {
            input_shift += p;
        }
        let shift_gate_index_if_necessary = |i: GateIndex| {
            if i <= 1 {
                i + input_shift
            } else if i < input_shift + 2 {
                i - 2
            } else {
                i
            }
        };
        let shift_gate_if_necessary = |gate: BuilderGate| match gate {
            BuilderGate::Xor(x, y) => {
                if x == 1 {
                    let y = shift_gate_index_if_necessary(y);
                    Gate::Not(y)
                } else if y == 1 {
                    let x = shift_gate_index_if_necessary(x);
                    Gate::Not(x)
                } else {
                    let x = shift_gate_index_if_necessary(x);
                    let y = shift_gate_index_if_necessary(y);
                    Gate::Xor(x, y)
                }
            }
            BuilderGate::And(x, y) => {
                let x = shift_gate_index_if_necessary(x);
                let y = shift_gate_index_if_necessary(y);
                Gate::And(x, y)
            }
        };
        let mut gates: Vec<Gate> = self
            .gates
            .into_iter()
            .map(shift_gate_if_necessary)
            .collect();
        gates.insert(0, Gate::Xor(0, 0)); // constant false
        gates.insert(1, Gate::Not(input_shift)); // constant true
        let output_gates = output_gates
            .into_iter()
            .map(shift_gate_index_if_necessary)
            .collect();
        Circuit {
            input_gates: self.input_gates,
            gates,
            output_gates,
        }
    }

    pub fn push_xor(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        self.gate_counter += 1;
        self.gates.push(BuilderGate::Xor(x, y));
        self.gate_counter - 1
    }

    pub fn push_and(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        self.gate_counter += 1;
        self.gates.push(BuilderGate::And(x, y));
        self.gate_counter - 1
    }

    pub fn push_not(&mut self, x: GateIndex) -> GateIndex {
        self.push_xor(x, 1)
    }

    pub fn push_or(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_xor(x, y);
        let and = self.push_and(x, y);
        self.push_xor(xor, and)
    }

    pub fn push_eq(&mut self, x: GateIndex, y: GateIndex) -> GateIndex {
        let xor = self.push_xor(x, y);
        self.push_xor(xor, 1)
    }

    pub fn push_mux(&mut self, s: GateIndex, x0: GateIndex, x1: GateIndex) -> GateIndex {
        if x0 == x1 {
            return x0;
        }
        let not_s = self.push_not(s);
        let x0_selected = self.push_and(x0, s);
        let x1_selected = self.push_and(x1, not_s);
        self.push_xor(x0_selected, x1_selected)
    }

    pub fn push_adder(
        &mut self,
        x: GateIndex,
        y: GateIndex,
        carry: GateIndex,
    ) -> (GateIndex, GateIndex) {
        // first half-adder:
        let wire_u = self.push_xor(x, y);
        let wire_v = self.push_and(x, y);
        // second half-adder:
        let wire_s = self.push_xor(wire_u, carry);
        let wire_w = self.push_and(wire_u, carry);

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
        let x_and_y = self.push_and(x, y);
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
            neg[i] = self.push_xor(carry, x);
            carry = self.push_and(carry, x);
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
            z[i] = self.push_xor(carry, y);
            carry = self.push_and(carry, y);
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

        let is_result_neg = self.push_xor(x[0], y[0]);
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
            let xor = self.push_xor(x[i], y[i]);

            let xor_and_x = self.push_and(xor, x[i]);
            let xor_and_y = self.push_and(xor, y[i]);
            let (gt, lt) = if i == 0 && (is_x_signed || is_y_signed) {
                (xor_and_y, xor_and_x)
            } else {
                (xor_and_x, xor_and_y)
            };

            let gt = self.push_or(gt, acc_gt);
            let lt = self.push_or(lt, acc_lt);

            let not_acc_gt = self.push_not(acc_gt);
            let not_acc_lt = self.push_not(acc_lt);

            acc_gt = self.push_and(gt, not_acc_lt);
            acc_lt = self.push_and(lt, not_acc_gt)
        }
        (acc_lt, acc_gt)
    }
}
