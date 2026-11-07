use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 500,
    ensures
        2 <= result <= 1000,
        result % 2 == 0,
{
    if mutation_kind == 0 {
        // identity
        seed * 2
    } else if mutation_kind == 1 && seed < 500 {
        // nudge up
        (seed + 1) * 2
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        (seed - 1) * 2
    } else if mutation_kind == 3 {
        // min boundary
        2
    } else if mutation_kind == 4 {
        // max boundary
        1000
    } else if mutation_kind == 5 {
        // halve (clamp to min 1)
        let h = seed / 2;
        if h >= 1 { h * 2 } else { 2 }
    } else if mutation_kind == 6 && seed <= 250 {
        // double
        seed * 4
    } else if mutation_kind == 7 {
        // mid value
        500
    } else if mutation_kind == 8 {
        // near-min
        4
    } else if mutation_kind == 9 {
        // near-max
        998
    } else {
        // fallback
        seed * 2
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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
    let examples: Vec<i32> = vec![2, 4, 6];
    for n in examples {
        if seen.insert(n) {
            let output = Solution::reinitialize_permutation(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: interesting even values in [2, 1000]
    let interesting_seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 25, 50, 100, 125, 250, 499, 500,
    ];

    for &s in &interesting_seeds {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::reinitialize_permutation(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds and mutations
    while generated < count {
        let s = rng.gen_range_i64(1, 500) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::reinitialize_permutation(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
