use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bits: Vec<u8>,
    mutation_kind: u8,
) -> (deltas: Vec<i32>)
    requires
        1 <= bits.len() <= 1_000_000,
        forall|j: int| 0 <= j < bits@.len() ==> (bits[j] == 0u8 || bits[j] == 1u8),
    ensures
        1 <= deltas.len() <= 1_000_000,
        forall|j: int|
            0 <= j < deltas@.len() ==> (deltas[j] == 1 || deltas[j] == -1),
{
    let n = bits.len();
    let mut deltas: Vec<i32> = Vec::new();

    if mutation_kind == 1 {
        // All +1
        let mut i: usize = 0;
        while i < n
            invariant
                n == bits.len(),
                1 <= n <= 1_000_000,
                0 <= i <= n,
                deltas.len() == i,
                forall|j: int| 0 <= j < deltas@.len() ==> deltas@[j] == 1i32,
            decreases n - i,
        {
            deltas.push(1i32);
            i = i + 1;
        }
    } else if mutation_kind == 2 {
        // All -1
        let mut i: usize = 0;
        while i < n
            invariant
                n == bits.len(),
                1 <= n <= 1_000_000,
                0 <= i <= n,
                deltas.len() == i,
                forall|j: int| 0 <= j < deltas@.len() ==> deltas@[j] == -1i32,
            decreases n - i,
        {
            deltas.push(-1i32);
            i = i + 1;
        }
    } else if mutation_kind == 3 {
        // Flipped: 0 -> +1, 1 -> -1
        let mut i: usize = 0;
        while i < n
            invariant
                n == bits.len(),
                1 <= n <= 1_000_000,
                0 <= i <= n,
                deltas.len() == i,
                forall|k: int| 0 <= k < bits@.len() ==> (bits@[k] == 0u8 || bits@[k] == 1u8),
                forall|j: int| 0 <= j < deltas@.len() ==> (deltas@[j] == 1i32 || deltas@[j] == -1i32),
            decreases n - i,
        {
            if bits[i] == 0u8 {
                deltas.push(1i32);
            } else {
                deltas.push(-1i32);
            }
            i = i + 1;
        }
    } else {
        // Default: 0 -> -1, 1 -> +1
        let mut i: usize = 0;
        while i < n
            invariant
                n == bits.len(),
                1 <= n <= 1_000_000,
                0 <= i <= n,
                deltas.len() == i,
                forall|k: int| 0 <= k < bits@.len() ==> (bits@[k] == 0u8 || bits@[k] == 1u8),
                forall|j: int| 0 <= j < deltas@.len() ==> (deltas@[j] == 1i32 || deltas@[j] == -1i32),
            decreases n - i,
        {
            if bits[i] == 1u8 {
                deltas.push(1i32);
            } else {
                deltas.push(-1i32);
            }
            i = i + 1;
        }
    }
    deltas
}

}

use std::io::Write;

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

fn random_str(rng: &mut Rng, n: usize) -> String {
    let mut s = String::with_capacity(n);
    for _ in 0..n {
        if rng.next_u64() % 2 == 0 { s.push('+'); } else { s.push('-'); }
    }
    s
}

fn build_input(strs: &[String]) -> String {
    let mut s = format!("{}\n", strs.len());
    for st in strs {
        s.push_str(st);
        s.push('\n');
    }
    s
}

fn solve(s: &str) -> i64 {
    let deltas: Vec<i32> = s.chars().map(|c| if c == '+' { 1 } else { -1 }).collect();
    Solution::pluses_minuses_total_steps(deltas)
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let strs: Vec<String> = vec!["--+-".to_string(), "---".to_string(), "++--+-".to_string()];
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // Edge singles
    let edges = vec!["+", "-", "++", "--", "+-", "-+", "++++++++++", "----------"];
    for e in edges {
        if count >= target { break; }
        let strs: Vec<String> = vec![e.to_string()];
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut strs: Vec<String> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(1, 100),
                3 => rng.gen_range_usize(50, 200),
                _ => rng.gen_range_usize(100, 500),
            };
            strs.push(random_str(&mut rng, n));
        }
        let answers: Vec<i64> = strs.iter().map(|s| solve(s)).collect();
        let inp = build_input(&strs);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

