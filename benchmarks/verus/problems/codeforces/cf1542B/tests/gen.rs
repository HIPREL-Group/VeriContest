use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_seed: i64, a_seed: i64, b_seed: i64, mutation_kind: u8) -> (result: (i64, i64, i64))
    requires
        1 <= n_seed <= 1_000_000_000,
        1 <= a_seed <= 1_000_000_000,
        1 <= b_seed <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    let n = n_seed;
    let a = a_seed;
    let b = b_seed;

    if mutation_kind == 0 {
        (n, a, b)                                             // identity
    } else if mutation_kind == 1 && n < 1_000_000_000 {
        (n + 1, a, b)                                         // nudge n up
    } else if mutation_kind == 2 && n > 1 {
        (n - 1, a, b)                                         // nudge n down
    } else if mutation_kind == 3 && a < 1_000_000_000 {
        (n, a + 1, b)                                         // nudge a up
    } else if mutation_kind == 4 && a > 1 {
        (n, a - 1, b)                                         // nudge a down
    } else if mutation_kind == 5 && b < 1_000_000_000 {
        (n, a, b + 1)                                         // nudge b up
    } else if mutation_kind == 6 && b > 1 {
        (n, a, b - 1)                                         // nudge b down
    } else if mutation_kind == 7 {
        (1, a, b)                                             // n = min
    } else if mutation_kind == 8 {
        (1_000_000_000, a, b)                                 // n = max
    } else if mutation_kind == 9 {
        (n, 1, b)                                             // a = 1 (special case in algorithm)
    } else if mutation_kind == 10 {
        (n, 1_000_000_000, b)                                 // a = max
    } else if mutation_kind == 11 {
        (n, a, 1)                                             // b = min
    } else if mutation_kind == 12 {
        (n, a, 1_000_000_000)                                 // b = max
    } else if mutation_kind == 13 {
        (1, 1, 1)                                             // all min
    } else if mutation_kind == 14 {
        (1_000_000_000, 1_000_000_000, 1_000_000_000)         // all max
    } else if mutation_kind == 15 {
        (n, 1, 1)                                             // a=1, b=1
    } else if mutation_kind == 16 {
        // swap a and b
        (n, b, a)
    } else {
        (n, a, b)                                             // fallback
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
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



fn build_input(cases: &[(i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, a, b) in cases {
        s.push_str(&format!("{} {} {}\n", n, a, b));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "Yes\n" } else { "No\n" });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    // First entry: examples from description as a single multi-test
    let examples: Vec<(i64, i64, i64)> = vec![
        (24, 3, 5),
        (10, 3, 6),
        (2345, 1, 4),
        (19260817, 394, 485),
        (19260817, 233, 264),
    ];
    let answers: Vec<bool> = examples.iter().map(|&(n, a, b)| Solution::n_in_generated_set(n, a, b)).collect();
    let inp = build_input(&examples);
    let outp = build_output(&answers);
    if seen.insert(inp.clone()) {
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    // structured seed pool
    let n_values: Vec<i64> = vec![1, 2, 3, 5, 10, 100, 1000, 1_000_000, 1_000_000_000];
    let a_values: Vec<i64> = vec![1, 2, 3, 5, 10, 100, 1000, 1_000_000_000];
    let b_values: Vec<i64> = vec![1, 2, 3, 5, 10, 100, 1000, 1_000_000_000];

    let mut buf_cases: Vec<(i64, i64, i64)> = Vec::new();
    let mut bundle_size: usize = 1;
    'outer: for &n_seed in &n_values {
        for &a_seed in &a_values {
            for &b_seed in &b_values {
                for mk in 0..=16u8 {
                    if count >= target { break 'outer; }
                    let (n, a, b) = generate_test_case(n_seed, a_seed, b_seed, mk);
                    buf_cases.push((n, a, b));
                    if buf_cases.len() >= bundle_size {
                        let answers: Vec<bool> = buf_cases.iter().map(|&(n, a, b)| Solution::n_in_generated_set(n, a, b)).collect();
                        let inp = build_input(&buf_cases);
                        let outp = build_output(&answers);
                        if seen.insert(inp.clone()) {
                            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
                            count += 1;
                        }
                        buf_cases.clear();
                        bundle_size = 1 + (rng.gen_range_usize(0, 30));
                    }
                }
            }
        }
    }

    // Random fill
    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 50) };
        let mut cases: Vec<(i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            let n_seed = match rng.gen_u8() % 5 {
                0 => rng.gen_range_i64(1, 10),
                1 => rng.gen_range_i64(1, 1000),
                2 => rng.gen_range_i64(1, 1_000_000),
                3 => rng.gen_range_i64(1_000_000, 1_000_000_000),
                _ => rng.gen_range_i64(1, 1_000_000_000),
            };
            let a_seed = match rng.gen_u8() % 4 {
                0 => 1,
                1 => rng.gen_range_i64(2, 10),
                2 => rng.gen_range_i64(2, 1000),
                _ => rng.gen_range_i64(1, 1_000_000_000),
            };
            let b_seed = match rng.gen_u8() % 3 {
                0 => rng.gen_range_i64(1, 10),
                1 => rng.gen_range_i64(1, 1000),
                _ => rng.gen_range_i64(1, 1_000_000_000),
            };
            let mk = rng.gen_u8() % 17;
            let (n, a, b) = generate_test_case(n_seed, a_seed, b_seed, mk);
            cases.push((n, a, b));
        }
        let answers: Vec<bool> = cases.iter().map(|&(n, a, b)| Solution::n_in_generated_set(n, a, b)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
}

