use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 1000i32,
    ensures
        0 <= result <= 1000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 1000 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500 {
            (seed * 2) as i32                         // double (clamped)
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        (seed / 2) as i32                             // halve
    } else if mutation_kind == 5 {
        0i32                                          // zero / min boundary
    } else if mutation_kind == 6 {
        1000i32                                       // max boundary
    } else if mutation_kind == 7 {
        1i32                                          // one
    } else if mutation_kind == 8 {
        if seed >= 500 {
            (1000 - seed) as i32                      // mirror around 500
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        500i32                                        // midpoint
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Seed pool: examples from description.md and interesting values
    let seeds: Vec<i32> = vec![
        1, 4,                                   // examples from description
        0, 2, 3, 5, 6, 7, 8, 15, 16, 31, 32,   // around monobit boundaries
        63, 64, 127, 128, 255, 256, 511, 512,
        999, 1000,                               // near max
        100, 200, 333, 500, 750, 42,
    ];

    // Iterate seed pool × all mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::count_monobit(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s = rng.gen_range_i64(0, 1000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::count_monobit(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
