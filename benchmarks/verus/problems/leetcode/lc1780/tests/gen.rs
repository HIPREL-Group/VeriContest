use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 10_000_000i32,
    ensures
        1i32 <= result <= 10_000_000i32,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 10_000_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed >= 1 && seed <= 5_000_000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed / 2 >= 1 {
            seed / 2                                      // halve
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        10_000_000                                        // max boundary
    } else if mutation_kind == 7 {
        if seed >= 1 && seed <= 9_999_999 {
            seed + 1                                      // nudge up (alt)
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        // clamp to middle range
        if seed >= 1000 && seed <= 9_999_000 {
            seed
        } else if seed < 1000 {
            1000
        } else {
            9_999_000
        }
    } else if mutation_kind == 9 {
        // mod into valid range: seed % 9_999_999 + 1 is always in [1, 9_999_999]
        // but seed is already in [1, 10_000_000] so just return seed
        seed
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

    // Seed pool: powers of 3, near-powers, examples, boundaries
    let mut seeds: Vec<i32> = vec![
        // Examples from description
        12, 91, 21,
        // Boundaries
        1, 2, 10_000_000,
        // Powers of 3: 1, 3, 9, 27, ..., 3^14 = 4782969
        1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683,
        59049, 177147, 531441, 1594323, 4782969,
        // Sums of distinct powers of 3
        4,    // 3^0 + 3^1
        10,   // 3^0 + 3^2
        13,   // 3^0 + 3^1 + 3^2
        28,   // 3^0 + 3^3
        30,   // 3^1 + 3^3
        40,   // 3^0 + 3^1 + 3^2 + 3^3
        // Near-powers (likely not sums of distinct pow3)
        2, 5, 6, 7, 8, 14, 15, 20, 50, 100,
        // Larger interesting values
        999_999, 1_000_000, 5_000_000, 9_999_999,
    ];
    // Near powers of 3
    let mut p: i64 = 3;
    while p <= 10_000_000 {
        if p - 1 >= 1 { seeds.push((p - 1) as i32); }
        if p + 1 <= 10_000_000 { seeds.push((p + 1) as i32); }
        p *= 3;
    }

    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            if s < 1 || s > 10_000_000 { continue; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::check_powers_of_three(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Diverse size classes
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,              // tiny
            1 => rng.gen_range_i64(1, 100) as i32,             // small
            2 => rng.gen_range_i64(100, 10_000) as i32,        // medium
            3 => rng.gen_range_i64(10_000, 1_000_000) as i32,  // large
            _ => rng.gen_range_i64(1_000_000, 10_000_000) as i32, // max
        };
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::check_powers_of_three(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
