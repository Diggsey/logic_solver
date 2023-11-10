use std::{
    collections::{hash_map::Entry, BTreeSet, HashMap},
    fmt::{Debug, Write},
};

type OutputType = u32;
const FLOAT_MASK: OutputType = (OutputType::MAX / 3) << 1;

#[repr(u8)]
#[allow(unused)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum GateKind {
    And,
    Or,
    Nand,
    Nor,
    Switch,
    Count,
}

impl From<u8> for GateKind {
    fn from(value: u8) -> Self {
        if value >= Self::Count as u8 {
            panic!("Invalid value")
        }
        unsafe { std::mem::transmute(value) }
    }
}

impl GateKind {
    fn commutes(self) -> bool {
        !matches!(self, Self::Switch)
    }
    fn floating(self) -> bool {
        matches!(self, Self::Switch)
    }
    fn eval(self, mask: OutputType, a: OutputType, b: OutputType) -> OutputType {
        let a2 = a & !FLOAT_MASK;
        let b2 = b & !FLOAT_MASK;
        (match self {
            GateKind::And => a2 & b2,
            GateKind::Or => a2 | b2,
            GateKind::Nand => (a2 & b2) ^ !FLOAT_MASK,
            GateKind::Nor => (a2 | b2) ^ !FLOAT_MASK,
            GateKind::Switch => (a2 & b2) | (FLOAT_MASK & !(b2 << 1)),
            GateKind::Count => unreachable!(),
        }) & mask
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Function {
    output: OutputType,
    delay: u8,
}

impl Debug for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:016b} (delay {})", self.output, self.delay)
    }
}

impl Function {
    fn floating(&self) -> bool {
        self.output & FLOAT_MASK != 0
    }
    fn connect(&self, other: &Function) -> Option<Self> {
        let a_or_b = self.output | other.output;
        let a_and_b = self.output & other.output;
        let a_xor_b = self.output ^ other.output;
        let has_error = (a_xor_b & !FLOAT_MASK) & !((a_or_b & FLOAT_MASK) >> 1);
        if has_error != 0 {
            return None;
        }
        let output = (a_or_b & !FLOAT_MASK) | (a_and_b & FLOAT_MASK);
        Some(Self {
            output,
            delay: self.delay.max(other.delay),
        })
    }
    fn constant(num_bits: u32, value: bool) -> Self {
        Self::build(num_bits, 0, |_| Some(value))
    }
    fn identity(num_bits: u32, bit: u32) -> Self {
        Self::build(num_bits, 0, |input| Some(((input >> bit) & 1) != 0))
    }
    fn build(num_bits: u32, delay: u8, f: impl Fn(u32) -> Option<bool>) -> Self {
        let mut output = 0;
        for i in 0..(1 << num_bits) {
            match f(i) {
                Some(true) => output |= 1 << (i * 2),
                Some(false) => {}
                None => output |= 1 << (i * 2 + 1),
            }
        }
        Self { output, delay }
    }
    fn satisfies(&self, other: &Self) -> bool {
        (self.output & !FLOAT_MASK & ((!other.output & FLOAT_MASK) >> 1)
            == other.output & !FLOAT_MASK)
            && self.delay <= other.delay
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Default)]
struct MultiFunction {
    functions: BTreeSet<Function>,
}

impl MultiFunction {
    fn setup(num_bits: u32) -> (Self, HashMap<Function, String>) {
        let mut res = Self::default();
        let mut named_functions = HashMap::new();
        let off = Function::constant(num_bits, false);
        res.functions.insert(off);
        named_functions.insert(off, "off".into());
        let on = Function::constant(num_bits, true);
        res.functions.insert(on);
        named_functions.insert(on, "on".into());
        for bit in 0..num_bits {
            let bit_f = Function::identity(num_bits, bit);
            res.functions.insert(bit_f);
            named_functions.insert(bit_f, format!("bit {bit}"));
        }
        (res, named_functions)
    }
    fn satisfies(&self, fs: &[Function]) -> bool {
        fs.iter()
            .all(|f| self.functions.iter().any(|function| function.satisfies(f)))
    }
}

struct Solution {
    gate_cost: u8,
    new_gate: GateKind,
    prev: MultiFunction,
    prev_0: Function,
    prev_1: Function,
    prev_2: Option<Function>,
    new: Function,
    disable: bool,
}

struct BestResult {
    min_gate_cost: u8,
    min_max_delay: u8,
}

#[derive(Default)]
struct State {
    num_bits: u32,
    best_functions: HashMap<MultiFunction, BestResult>,
    named_functions: HashMap<Function, String>,
    solutions: HashMap<MultiFunction, Solution>,
    debug_functions: Vec<Function>,
}

impl State {
    fn should_record(&mut self, mf: &MultiFunction, gate_cost: u8) -> bool {
        let mut simplified = MultiFunction::default();
        let mut res: bool = false;
        simplified.functions.extend(mf.functions.iter().map(|f| {
            let mut sf = f.clone();
            sf.delay = 0;
            sf
        }));
        let max_delay = mf.functions.iter().map(|f| f.delay).max().unwrap();

        match self.best_functions.entry(simplified) {
            Entry::Occupied(mut occ) => {
                let existing = occ.get_mut();
                if max_delay < existing.min_max_delay {
                    res = true;
                    existing.min_max_delay = max_delay;
                }
                if gate_cost < existing.min_gate_cost {
                    res = true;
                    existing.min_gate_cost = gate_cost;
                }
            }
            Entry::Vacant(vac) => {
                res = true;
                vac.insert(BestResult {
                    min_gate_cost: gate_cost,
                    min_max_delay: max_delay,
                });
            }
        }
        res
    }
    fn new(num_bits: u32) -> Self {
        let mut res = Self::default();
        res.num_bits = num_bits;
        let (identity, named_functions) = MultiFunction::setup(num_bits);
        res.named_functions = named_functions;
        res.solutions.insert(
            identity,
            Solution {
                gate_cost: 0,
                new_gate: GateKind::Count,
                prev_0: Function::constant(num_bits, false),
                prev_1: Function::constant(num_bits, false),
                prev_2: None,
                new: Function::constant(num_bits, false),
                prev: MultiFunction::default(),
                disable: false,
            },
        );
        res
    }
    fn solve_once(
        &mut self,
        max_gate_cost: u8,
        max_delay: u8,
        mut checker: impl FnMut(&MultiFunction, &mut Solution) -> bool,
        print: bool,
    ) {
        for gate_cost in 1..max_gate_cost {
            println!("Solving {gate_cost}");
            self.expand(gate_cost, max_delay);
        }
        println!("Solving {max_gate_cost}");
        let mut new_solutions = HashMap::<MultiFunction, Solution>::new();
        for (k, v) in &self.solutions {
            if v.disable {
                continue;
            }
            if v.gate_cost == max_gate_cost - 1 {
                self.generate(max_delay, k, v, |mf, mut solution| {
                    if checker(&mf, &mut solution) {
                        if print {
                            self.print(&mf, &solution);
                        }
                        new_solutions.entry(mf).or_insert(solution);
                    }
                });
            }
        }
        for (k, v) in new_solutions {
            if self.should_record(&k, v.gate_cost) {
                self.solutions.insert(k, v);
            }
        }
        for (k, v) in &mut self.solutions {
            if !v.disable && !checker(k, v) {
                v.disable = true;
            }
        }
    }
    fn expand(&mut self, gate_cost: u8, max_delay: u8) {
        let mut new_solutions = HashMap::<MultiFunction, Solution>::new();
        for (k, v) in &self.solutions {
            if v.disable {
                continue;
            }
            if v.gate_cost == gate_cost - 1 {
                self.generate(max_delay, k, v, |mf, solution| {
                    new_solutions.entry(mf).or_insert(solution);
                });
            }
        }
        if !self.debug_functions.is_empty() {
            for (k, v) in &new_solutions {
                if self.debug_functions.iter().all(|f| k.functions.contains(f)) {
                    self.print(k, v);
                }
            }
        }
        for (k, v) in new_solutions {
            if self.should_record(&k, v.gate_cost) {
                self.solutions.insert(k, v);
            }
        }
    }
    fn generate(
        &self,
        max_delay: u8,
        prev_mf: &MultiFunction,
        prev_s: &Solution,
        mut new_solution: impl FnMut(MultiFunction, Solution),
    ) {
        let shift = OutputType::BITS - (1 << self.num_bits) * 2;
        let mask = OutputType::MAX >> shift;
        for gate_idx in 0..(GateKind::Count as u8) {
            let new_gate = GateKind::from(gate_idx);
            let commutes = new_gate.commutes();
            let floating = new_gate.floating();
            for prev_f0 in &prev_mf.functions {
                if prev_f0.delay > max_delay {
                    continue;
                }
                for prev_f1 in &prev_mf.functions {
                    if prev_f1.delay > max_delay {
                        continue;
                    }
                    if commutes && prev_f1 < prev_f0 {
                        // Ignore duplicates if the gate is commutative
                        continue;
                    }
                    let new_output = new_gate.eval(mask, prev_f0.output, prev_f1.output);
                    if new_output == prev_f0.output || new_output == prev_f1.output {
                        continue;
                    }
                    let new_delay = prev_f0.delay.max(prev_f1.delay) + 1;
                    let new_f = Function {
                        output: new_output,
                        delay: new_delay,
                    };
                    if prev_mf.functions.contains(&new_f) {
                        continue;
                    }
                    let mut new_mf = prev_mf.clone();
                    new_mf.functions.insert(new_f);
                    if !self.solutions.contains_key(&new_mf) {
                        new_solution(
                            new_mf,
                            Solution {
                                gate_cost: prev_s.gate_cost + 1,
                                new_gate,
                                prev: prev_mf.clone(),
                                prev_0: prev_f0.clone(),
                                prev_1: prev_f1.clone(),
                                prev_2: None,
                                new: new_f,
                                disable: false,
                            },
                        );
                    }

                    // Gates that can float can output onto existing wires in some cases.
                    if floating {
                        for prev_f2 in &prev_mf.functions {
                            if prev_f0 == prev_f2 || prev_f1 == prev_f2 || !prev_f2.floating() {
                                continue;
                            }
                            if let Some(repl_f) = prev_f2.connect(&new_f) {
                                if prev_mf.functions.contains(&repl_f) {
                                    continue;
                                }
                                let mut repl_mf = prev_mf.clone();
                                repl_mf.functions.remove(prev_f2);
                                repl_mf.functions.insert(repl_f);

                                if !self.solutions.contains_key(&repl_mf) {
                                    let solution = Solution {
                                        gate_cost: prev_s.gate_cost + 1,
                                        new_gate,
                                        prev: prev_mf.clone(),
                                        prev_0: prev_f0.clone(),
                                        prev_1: prev_f1.clone(),
                                        prev_2: Some(prev_f2.clone()),
                                        new: new_f,
                                        disable: false,
                                    };
                                    new_solution(repl_mf, solution);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    fn name(&self, f: Function, extra_names: &mut HashMap<Function, String>) -> String {
        if let Some(name) = self.named_functions.get(&f) {
            return name.clone();
        } else {
            let num_names = extra_names.len();
            extra_names
                .entry(f)
                .or_insert_with(|| format!("unnamed {num_names}"))
                .clone()
        }
    }
    fn stringify_nested(
        &self,
        solution: &Solution,
        extra_names: &mut HashMap<Function, String>,
    ) -> String {
        if solution.gate_cost == 0 {
            return String::new();
        }
        let mut res = if let Some(prev_solution) = self.solutions.get(&solution.prev) {
            self.stringify_nested(prev_solution, extra_names)
        } else {
            "<truncated>".into()
        };
        let name0 = self.name(solution.prev_0, extra_names);
        let name1 = self.name(solution.prev_1, extra_names);
        if let Some(prev_2) = solution.prev_2 {
            let name2 = self.name(prev_2, extra_names);
            extra_names.insert(solution.new, name2);
        };
        let name_new = self.name(solution.new, extra_names);

        writeln!(
            res,
            "{:?} [{}, {}] => {}",
            solution.new_gate, name0, name1, name_new
        )
        .unwrap();
        res
    }
    fn print(&self, mf: &MultiFunction, solution: &Solution) {
        let max_delay = mf.functions.iter().map(|f| f.delay).max().unwrap();
        println!(
            "Gate cost: {}, Max delay: {}",
            solution.gate_cost, max_delay
        );
        let mut extra_names = HashMap::new();
        let s = self.stringify_nested(solution, &mut extra_names);
        print!("{s}");
        for f in &mf.functions {
            println!(
                "{:0width$b} (delay: {})",
                f.output,
                f.delay,
                width = ((1 << self.num_bits) * 2) as usize
            );
        }
        println!("-")
    }
    fn solve(&mut self, max_gate_costs: &[u8], desired_functions: &[Function]) {
        for (idx, (desired_function, max_gate_cost)) in
            desired_functions.iter().zip(max_gate_costs).enumerate()
        {
            println!(
                "{idx}: {}",
                self.solutions
                    .values()
                    .filter(|solution| !solution.disable)
                    .count()
            );
            self.solve_once(
                *max_gate_cost,
                desired_function.delay,
                |k, _v| {
                    let satisfies = k.satisfies(&desired_functions[0..=idx]);
                    if satisfies {
                        // println!("Found solution!");
                    }
                    satisfies
                },
                idx == desired_functions.len() - 1,
            );
        }
        // for (mf, solution) in &self.solutions {
        //     if !solution.disable {
        //         self.print(mf, solution);
        //     }
        // }
    }
}

fn main() {
    let num_bits = 3;
    let mut state = State::new(num_bits);

    let desired_functions = [
        // Function::build(num_bits, 2, |input| Some(input.count_ones() & 2 != 0)),
        // Function::build(num_bits, 6, |input| Some(input.count_ones() & 1 != 0)),
        Function::build(num_bits, 2, |input| Some(input == 0)),
        Function::build(num_bits, 2, |input| Some(input == 1)),
        Function::build(num_bits, 2, |input| Some(input == 2)),
        Function::build(num_bits, 2, |input| Some(input == 3)),
        Function::build(num_bits, 2, |input| Some(input == 4)),
        Function::build(num_bits, 2, |input| Some(input == 5)),
        Function::build(num_bits, 2, |input| Some(input == 6)),
        Function::build(num_bits, 2, |input| Some(input == 7)),
    ];
    dbg!(&desired_functions);

    // state.debug_functions = vec![Function::build(num_bits, 1, |input| {
    //     let overwrite = input & 4 != 0;
    //     Some(!overwrite)
    // })];

    state.solve(&[2, 4, 6, 7, 9, 11, 13, 14], &desired_functions);
}
