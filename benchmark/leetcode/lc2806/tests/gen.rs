use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 100,
    ensures
        0 <= result <= 100,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 100 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50 { seed * 2 } else { seed }      // double (clamped)
    } else if mutation_kind == 4 {
        seed / 2                                      // halve
    } else if mutation_kind == 5 {
        0                                             // zero / min boundary
    } else if mutation_kind == 6 {
        100                                           // max boundary
    } else if mutation_kind == 7 {
        100 - seed                                    // complement
    } else if mutation_kind == 8 {
        // round to nearest 10
        let r = seed % 10;
        if r < 5 { seed - r } else { seed + (10 - r) }
    } else if mutation_kind == 9 {
        // clamp to midpoint region
        if seed < 40 { 40 } else if seed > 60 { 60 } else { seed }
    } else {
        seed                                          // fallback
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Seed pool: boundary values, multiples of 10, examples from description
    let seeds: Vec<i32> = vec![
        0, 1, 5, 9, 10, 15, 20, 25, 30, 35, 40, 45, 50,
        55, 60, 65, 70, 75, 80, 85, 90, 95, 99, 100,
        2, 3, 4, 6, 7, 8, 11, 14, 16, 19, 21, 24, 26, 29,
    ];

    // Systematic: all seeds × all mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::account_balance_after_purchase(n);
                writeln!(out, "{}", json!({"input": {"purchase_amount": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s = rng.gen_range_i64(0, 100) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::account_balance_after_purchase(n);
            writeln!(out, "{}", json!({"input": {"purchase_amount": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
