use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 10_000i32,
    ensures
        1 <= result <= 10_000,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 10_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 5_000 {
            seed + seed                                   // double (stays in range)
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                      // halve (min 1)
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        10_000                                            // max boundary
    } else if mutation_kind == 7 {
        // map to small prime squares (numbers with exactly 3 divisors)
        if seed % 5 == 0 {
            4       // 2^2
        } else if seed % 5 == 1 {
            9       // 3^2
        } else if seed % 5 == 2 {
            25      // 5^2
        } else if seed % 5 == 3 {
            49      // 7^2
        } else {
            121     // 11^2
        }
    } else if mutation_kind == 8 {
        // clamp to middle range
        if seed < 50 {
            50
        } else if seed > 9950 {
            9950
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        // map to powers of 2 in range
        if seed % 4 == 0 {
            2
        } else if seed % 4 == 1 {
            16
        } else if seed % 4 == 2 {
            256
        } else {
            8192
        }
    } else {
        seed                                              // fallback
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

    // Seed pool: interesting values for "three divisors" problem
    // Numbers with exactly 3 divisors are squares of primes: 4,9,25,49,121,...
    let seeds: Vec<i32> = vec![
        // Example inputs from description.md
        2, 4,
        // Small values
        1, 3, 5, 6, 7, 8, 9, 10,
        // Prime squares (exactly 3 divisors)
        25, 49, 121, 169, 289, 361, 529, 625, 841,
        961, 1369, 1681, 1849, 2209, 2809, 3481, 3721, 4489, 5041,
        5329, 6241, 6889, 7921, 8281, 9409,
        // Perfect squares of composites (not 3 divisors)
        16, 36, 64, 81, 100, 144, 256, 400, 900, 1024, 2500,
        // Primes (exactly 2 divisors)
        11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 97,
        // Boundaries
        10_000, 9999, 9998, 5000,
    ];

    for &s in &seeds {
        if s < 1 || s > 10_000 { continue; }
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::is_three(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Sample from diverse size classes
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,        // tiny
            1 => rng.gen_range_i64(1, 100) as i32,       // small
            2 => rng.gen_range_i64(100, 1000) as i32,    // medium
            3 => rng.gen_range_i64(1000, 5000) as i32,   // large
            _ => rng.gen_range_i64(5000, 10000) as i32,  // max
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::is_three(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
