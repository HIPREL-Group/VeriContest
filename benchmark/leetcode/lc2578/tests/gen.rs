use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        10i32 <= seed <= 1_000_000_000i32,
    ensures
        10i32 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 10 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (if in range)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (if result stays >= 10)
        if seed >= 20 {
            seed / 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        // min boundary
        10
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // clamp to hundreds
        if seed >= 100 {
            (seed / 100) * 100
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        // set to a mid-range value
        500_000_000
    } else if mutation_kind == 9 {
        // round down to nearest power-of-10-ish: keep top digit
        if seed >= 100 {
            let d = seed / 100;
            if d <= 10_000_000 {
                d * 100
            } else {
                seed
            }
        } else {
            seed
        }
    } else {
        // fallback: identity
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

    // Seed pool: example inputs and interesting values
    let seeds: Vec<i32> = vec![
        // Examples from description.md
        4325, 687,
        // Boundary values
        10, 11, 99, 100, 999, 1000,
        1_000_000_000, 999_999_999,
        // Repeated digits
        1111, 2222, 9999, 1000000,
        // Small multi-digit
        12, 21, 13, 31, 19, 91, 50, 55,
        // Various magnitudes
        123, 456, 789, 1234, 56789, 123456, 1234567, 12345678, 123456789,
        // All same digit
        11, 22, 33, 44, 55, 66, 77, 88, 99,
        // Powers of 10
        100, 1000, 10000, 100000, 1000000, 10000000, 100000000,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::split_num(n);
                writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Sample across size classes
        let s = match rng.gen_u8() % 5 {
            0 => rng.gen_range_i64(10, 99),                    // 2-digit
            1 => rng.gen_range_i64(100, 9999),                 // 3-4 digit
            2 => rng.gen_range_i64(10000, 999999),             // 5-6 digit
            3 => rng.gen_range_i64(1000000, 99999999),         // 7-8 digit
            _ => rng.gen_range_i64(100000000, 1000000000),     // 9-10 digit
        } as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::split_num(n);
            writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases", count);
}
