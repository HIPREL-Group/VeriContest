use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 100000,
    ensures
        1 <= result <= 100000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 100000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50000 {
            seed * 2                                  // double (clamped)
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2                                  // halve (stays >= 1)
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        100000                                        // max boundary
    } else if mutation_kind == 7 {
        if seed <= 99999 {
            (seed + 100000) / 2                       // midpoint toward max
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        (seed + 1) / 2                                // midpoint toward min
    } else if mutation_kind == 9 {
        if seed <= 99900 {
            seed + 100                                // large nudge up
        } else {
            seed
        }
    } else if mutation_kind == 10 && seed > 100 {
        seed - 100                                    // large nudge down
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

    // Seed pool: examples from description + boundary and interesting values
    let seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 50, 100, 500, 1000, 5000,
        10000, 50000, 99999, 100000,
        2, 7, 13, 42, 256, 1024, 9999, 33333, 66666,
    ];

    for &s in &seeds {
        for mk in 0..=11u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::colored_cells(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Sample across size classes for diversity
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,         // tiny
            1 => rng.gen_range_i64(1, 100) as i32,       // small
            2 => rng.gen_range_i64(100, 10000) as i32,   // medium
            3 => rng.gen_range_i64(10000, 50000) as i32, // large
            _ => rng.gen_range_i64(50000, 100000) as i32, // max range
        };
        let mk = rng.gen_u8() % 12;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::colored_cells(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
