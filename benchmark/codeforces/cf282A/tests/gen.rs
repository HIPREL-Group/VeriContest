use vstd::prelude::*;

verus! {

pub fn generate_test_case(ops: Vec<i32>, mutation_kind: u8) -> (operations: Vec<i32>)
    requires
        1 <= ops.len() <= 150,
        forall|i: int|
            0 <= i < ops.len() ==> (#[trigger] ops[i] == 1 || ops[i] == -1),
    ensures
        1 <= operations.len() <= 150,
        forall|i: int|
            0 <= i < operations.len() ==> (#[trigger] operations[i] == 1 || operations[i] == -1),
{
    if mutation_kind == 0 {
        // identity
        ops
    } else if mutation_kind == 1 {
        // flip first element
        let mut d = ops;
        let val = d[0];
        if val == 1 {
            d.set(0, -1i32);
        } else {
            d.set(0, 1i32);
        }
        d
    } else if mutation_kind == 2 {
        // flip last element
        let mut d = ops;
        let last = d.len() - 1;
        let val = d[last];
        if val == 1 {
            d.set(last, -1i32);
        } else {
            d.set(last, 1i32);
        }
        d
    } else if mutation_kind == 3 {
        // set all to 1
        let mut d = ops;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == ops.len(),
                1 <= d.len() <= 150,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> (d[j] == 1 || d[j] == -1),
            decreases d.len() - i,
        {
            d.set(i, 1i32);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all to -1
        let mut d = ops;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == ops.len(),
                1 <= d.len() <= 150,
                forall|j: int| 0 <= j < i ==> d[j] == -1i32,
                forall|j: int| i <= j < d.len() ==> (d[j] == 1 || d[j] == -1),
            decreases d.len() - i,
        {
            d.set(i, -1i32);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && ops.len() < 150 {
        // grow by one element (push 1)
        let mut d = ops;
        d.push(1i32);
        d
    } else if mutation_kind == 6 && ops.len() < 150 {
        // grow by one element (push -1)
        let mut d = ops;
        d.push(-1i32);
        d
    } else if mutation_kind == 7 && ops.len() > 1 {
        // shrink by one element (pop)
        let mut d = ops;
        d.pop();
        d
    } else {
        // fallback: identity
        ops
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn mutate(ops: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    if mutation_kind == 0 {
        ops
    } else if mutation_kind == 1 {
        let mut d = ops;
        if d.len() > 0 {
            d[0] = if d[0] == 1 { -1 } else { 1 };
        }
        d
    } else if mutation_kind == 2 {
        let mut d = ops;
        if d.len() > 0 {
            let last = d.len() - 1;
            d[last] = if d[last] == 1 { -1 } else { 1 };
        }
        d
    } else if mutation_kind == 3 {
        let mut d = ops;
        for i in 0..d.len() { d[i] = 1; }
        d
    } else if mutation_kind == 4 {
        let mut d = ops;
        for i in 0..d.len() { d[i] = -1; }
        d
    } else if mutation_kind == 5 && ops.len() < 150 {
        let mut d = ops;
        d.push(1);
        d
    } else if mutation_kind == 6 && ops.len() < 150 {
        let mut d = ops;
        d.push(-1);
        d
    } else if mutation_kind == 7 && ops.len() > 1 {
        let mut d = ops;
        d.pop();
        d
    } else {
        ops
    }
}

fn random_ops(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut ops = Vec::with_capacity(len);
    for _ in 0..len {
        if rng.next_u64() % 2 == 0 { ops.push(1); } else { ops.push(-1); }
    }
    ops
}

fn build_input(ops: &[i32], rng: &mut Rng) -> String {
    let mut s = format!("{}\n", ops.len());
    for &op in ops {
        if op == 1 {
            if rng.next_u64() % 2 == 0 { s.push_str("++X\n"); } else { s.push_str("X++\n"); }
        } else {
            if rng.next_u64() % 2 == 0 { s.push_str("--X\n"); } else { s.push_str("X--\n"); }
        }
    }
    s
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |ops: Vec<i32>, rng: &mut Rng, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", ops);
        if !seen.insert(key) { return; }
        let inp = build_input(&ops, rng);
        let ans = Solution::final_x_value(ops.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, -1],
    ];
    for seed_ops in &example_seeds {
        for mk in 0..=7u8 {
            let r = mutate(seed_ops.clone(), mk);
            emit(r, &mut rng, &mut seen, &mut out, &mut count);
        }
    }

    let hand_seeds: Vec<Vec<i32>> = vec![
        vec![-1],
        vec![1, 1],
        vec![-1, -1],
        vec![1, 1, 1],
        vec![-1, -1, -1],
        vec![1, -1, 1, -1],
        vec![1; 150],
        vec![-1; 150],
    ];
    for seed_ops in &hand_seeds {
        for mk in 0..=7u8 {
            let r = mutate(seed_ops.clone(), mk);
            emit(r, &mut rng, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let len = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => rng.gen_range_usize(101, 150),
        };
        let seed_ops = random_ops(&mut rng, len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let r = mutate(seed_ops, mk);
        emit(r, &mut rng, &mut seen, &mut out, &mut count);
    }
}

