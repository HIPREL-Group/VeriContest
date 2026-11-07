use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000_000i32,
    ensures
        1 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1_000_000_000
    } else if mutation_kind == 7 {
        if seed <= 999_999_999 {
            seed + 1
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        // Clamp to a power-of-10-like region
        if seed >= 100 {
            seed / 100 * 100
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        // Map to small value range
        (seed % 9) + 1
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
        // Examples from description
        537, 102, 6,
        // Boundaries
        1, 1_000_000_000,
        // Powers of 10
        10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000,
        // Near powers of 10
        9, 11, 99, 101, 999, 1001, 9999, 10001,
        // All same digit
        111_111_111, 999_999_999, 222_222_222,
        // Single digits
        1, 2, 3, 4, 5, 6, 7, 8, 9,
        // Values with zeros
        100_000, 10_010, 200_300, 400_050_006,
        // Large values
        999_999_999, 123_456_789, 987_654_321,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::decimal_representation(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::decimal_representation(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
