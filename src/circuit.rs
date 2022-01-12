use std::collections::HashSet;

/// Data type to uniquely identify gates.
pub type GateIndex = usize;

/// Description of a gate executed under S-MPC.
#[derive(Clone, Debug, PartialEq)]
pub enum Gate {
    False,
    True,
    InA,
    InB,
    Xor(GateIndex, GateIndex),
    And(GateIndex, GateIndex),
}

/// Representation of a circuit evaluated by an S-MPC engine.
#[derive(Clone, Debug)]
pub struct Circuit {
    pub gates: Vec<Gate>,
    pub output_gates: HashSet<GateIndex>,
}

impl Circuit {
    pub fn eval(&self, in_a: &[bool], in_b: &[bool]) -> Vec<Option<bool>> {
        let mut output = vec![None; self.gates.len()];
        let mut in_a_iter = in_a.iter();
        let mut in_b_iter = in_b.iter();
        for (w, gate) in self.gates.iter().enumerate() {
            let output_bit = match gate {
                Gate::False => false,
                Gate::True => true,
                Gate::InA => *in_a_iter.next().unwrap(),
                Gate::InB => *in_b_iter.next().unwrap(),
                Gate::Xor(x, y) => {
                    output[*x].unwrap() ^ output[*y].unwrap()
                }
                Gate::And(x, y) => {
                    output[*x].unwrap() & output[*y].unwrap()
                }
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
