use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= i32::MAX,
    ensures
        0 <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed >= 0 && seed <= 1_073_741_823 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                          // halve
    } else if mutation_kind == 5 {
        0                                                 // min boundary
    } else if mutation_kind == 6 {
        i32::MAX                                          // max boundary
    } else if mutation_kind == 7 {
        1                                                 // near-zero
    } else if mutation_kind == 8 {
        seed % (i32::MAX / 2 + 1)                        // modulo shrink
    } else {
        seed
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
    let rng_seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(rng_seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description + interesting boundary values
    let seeds: Vec<i32> = vec![
        4, 8,                                             // examples
        0, 1, 2, 3, 9, 10, 15, 16, 25, 36, 49, 64, 100, // small values & perfect squares
        i32::MAX, i32::MAX - 1,                           // max boundary
        2_147_395_600,                                    // 46340^2 (largest perfect square in range)
        46340, 46341,                                     // sqrt(MAX) neighborhood
        1000, 10000, 100000, 1000000,                     // size classes
    ];

    // Deterministic seeds with all mutation kinds
    for &seed in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let x = generate_test_case(seed, mk);
            if seen.insert(x) {
                let output = Solution::my_sqrt(x);
                writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Random seeds across size classes
    let mut _attempts_0 = 0usize;
    while count < goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let seed = match count % 5 {
            0 => rng.gen_range_i64(0, 10) as i32,                     // tiny
            1 => rng.gen_range_i64(0, 1000) as i32,                   // small
            2 => rng.gen_range_i64(1000, 100_000) as i32,             // medium
            3 => rng.gen_range_i64(100_000, 1_000_000_000) as i32,    // large
            _ => rng.gen_range_i64(0, i32::MAX as i64) as i32,        // full range
        };
        let mk = rng.gen_u8() % 10;
        let x = generate_test_case(seed, mk);
        if seen.insert(x) {
            let output = Solution::my_sqrt(x);
            writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
            count += 1;
        }
    }
}
