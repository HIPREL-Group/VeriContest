use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        10i32 <= seed <= 1_000_000_000i32,
    ensures
        10i32 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1
    } else if mutation_kind == 2 && seed > 10 {
        seed - 1
    } else if mutation_kind == 3 {
        let h = seed / 2;
        if h >= 10 {
            h
        } else {
            10
        }
    } else if mutation_kind == 4 {
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        10
    } else if mutation_kind == 6 {
        1_000_000_000
    } else if mutation_kind == 7 {
        11
    } else if mutation_kind == 8 {
        999_999_999
    } else if mutation_kind == 9 {
        let m = seed % 1000;
        if m >= 10 {
            m
        } else {
            10
        }
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

    // Seed pool: examples from description + interesting values
    let seeds: Vec<i32> = vec![
        // Examples from description.md
        31, 22, 124,
        // Boundary values
        10, 11, 99, 100, 999, 1000,
        999_999_999, 1_000_000_000,
        // Same-digit numbers
        33, 44, 55, 66, 77, 88,
        // All 9s
        9999, 99999, 999999, 9999999, 99999999,
        // Numbers with specific digit patterns
        19, 91, 90, 12, 21, 98, 89,
        // Powers of 10
        10000, 100000, 1000000, 10000000, 100000000,
        // Repeated large digits
        888_888_888, 777_777_777,
        // Mixed digits
        123456789, 987654321, 192837465,
    ];

    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::max_product(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let n_val = match count % 5 {
            0 => rng.gen_range_i64(10, 99),
            1 => rng.gen_range_i64(100, 999),
            2 => rng.gen_range_i64(1000, 99999),
            3 => rng.gen_range_i64(100000, 9999999),
            _ => rng.gen_range_i64(10000000, 1000000000),
        } as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(n_val, mk);
        if seen.insert(n) {
            let output = Solution::max_product(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
