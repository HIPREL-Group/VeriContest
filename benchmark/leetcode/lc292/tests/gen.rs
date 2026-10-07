use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed as int <= 2_147_483_647,
    ensures
        1 <= result as int <= 2_147_483_647,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed >= -1_073_741_823 && seed <= 1_073_741_823 {
            let doubled = seed * 2;
            if doubled >= 1 { doubled } else { seed }
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let halved = seed / 2;
        if halved >= 1 { halved } else { seed }       // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        i32::MAX                                      // max boundary
    } else if mutation_kind == 7 {
        if seed >= 1 {
            seed
        } else {
            let neg = -seed;
            if neg >= 1 { neg } else { 1 }            // absolute value
        }
    } else if mutation_kind == 8 {
        4                                             // known losing position
    } else if mutation_kind == 9 {
        3                                             // known winning position
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
        assert!(lo <= hi);
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let example_inputs: Vec<i32> = vec![4, 1, 2];

    for &n in &example_inputs {
        if generated >= count { break; }
        if seen.insert(n) {
            let output = Solution::can_win_nim(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: multiples of 4, near-multiples, boundary values
    let seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8,
        12, 16, 20, 100, 400, 1000, 4000,
        i32::MAX, i32::MAX - 1, i32::MAX - 2, i32::MAX - 3,
        i32::MAX / 2, i32::MAX / 4,
    ];

    for &s in &seeds {
        for mk in 0..=9u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::can_win_nim(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds and mutations
    while generated < count {
        let s = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::can_win_nim(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
