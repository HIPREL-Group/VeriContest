use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1 <= seed <= 1_000_000_000_000_000i64,
    ensures
        1 <= result <= 1_000_000_000_000_000i64,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000_000_000i64 {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 500_000_000_000_000i64 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1_000_000_000_000_000i64
    } else if mutation_kind == 7 {
        10
    } else if mutation_kind == 8 {
        let d = seed % 10;
        if d >= 1 { d } else { 1 }
    } else if mutation_kind == 9 {
        let r = seed % 1000;
        if r >= 1 { r } else { 1 }
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Interesting seed pool: examples, boundaries, zero patterns
    let seeds: Vec<i64> = vec![
        1020030, 1,                                    // examples from description
        10, 20, 100, 200, 1000, 10000,                // powers of 10
        1_000_000_000_000_000, 999_999_999_999_999,    // max boundary
        2, 9, 11, 99, 101, 999,                        // near powers of 10
        1010101010, 9090909090, 10203040,              // zero patterns
        505050505050505, 111111111111111,               // large patterns
        900000000000000, 100000000000000,               // leading digit + zeros
        123456789, 987654321,                           // no zeros
        1000000, 1000000000, 1000000000000,            // exact powers of 10
        30, 50, 70, 300, 500, 700,                     // multiples
        1000001, 10000001, 100000001,                  // sandwiched zeros
    ];

    // Phase 1: seed pool x mutations
    for &s in &seeds {
        if s < 1 || s > 1_000_000_000_000_000 {
            continue;
        }
        for mk in 0u8..=10 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::remove_zeros(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Phase 2: random seeds across size classes + random mutations
    while generated < count {
        let s = match generated % 6 {
            0 => rng.gen_range_i64(1, 9),
            1 => rng.gen_range_i64(10, 999),
            2 => rng.gen_range_i64(1000, 999_999),
            3 => rng.gen_range_i64(1_000_000, 999_999_999),
            4 => rng.gen_range_i64(1_000_000_000, 999_999_999_999),
            _ => rng.gen_range_i64(1_000_000_000_000, 1_000_000_000_000_000),
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::remove_zeros(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
