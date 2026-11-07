use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 50_000i32,
    ensures
        1 <= result <= 50_000i32,
{
    if mutation_kind == 0 {
        // Identity
        seed
    } else if mutation_kind == 1 && seed < 50_000 {
        // Nudge +1
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // Nudge -1
        seed - 1
    } else if mutation_kind == 3 {
        // Double (clamped)
        if seed <= 25_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // Halve (clamped to at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // Min boundary
        1
    } else if mutation_kind == 6 {
        // Max boundary
        50_000
    } else if mutation_kind == 7 {
        // Near-min boundary
        if seed <= 10 { seed } else { 10 }
    } else if mutation_kind == 8 {
        // Near-max boundary
        if seed >= 49_990 { seed } else { 49_990 }
    } else if mutation_kind == 9 {
        // Square root region
        // Map to sqrt-ish value: seed mod 223 + 1 gives 1..223
        let v = (seed % 223) + 1;
        if v >= 1 && v <= 50_000 { v } else { seed }
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
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

    // Example inputs from description
    let example_seeds: Vec<i32> = vec![13, 2];
    for &n in &example_seeds {
        if generated >= count { break; }
        if seen.insert(n) {
            let output = Solution::lexical_order(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Interesting seed values covering boundaries and size classes
    let interesting: Vec<i32> = vec![
        1, 2, 3, 5, 9, 10, 11, 13, 20, 50, 99, 100, 101,
        500, 999, 1000, 1001, 5000, 9999, 10000, 10001,
        25000, 49999, 50000,
    ];

    for &s in &interesting {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::lexical_order(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Random sampling with size classes
    let mut _attempts_0 = 0usize;
    while generated < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s: i32 = match generated % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,         // tiny
            1 => rng.gen_range_i64(1, 100) as i32,       // small
            2 => rng.gen_range_i64(100, 1000) as i32,    // medium
            3 => rng.gen_range_i64(1000, 10000) as i32,  // large
            _ => rng.gen_range_i64(10000, 50000) as i32, // max
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::lexical_order(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
