use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 100000i32,
    ensures
        1 <= result <= 100000,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 100000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (clamped)
        if seed <= 50000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (clamped to min 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        100000
    } else if mutation_kind == 7 {
        // mid value
        50000
    } else if mutation_kind == 8 {
        // quarter
        if seed <= 25000 {
            seed * 4
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        // complement: max - seed + 1
        100000 - seed + 1
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

    // Example inputs from the problem description
    let examples: Vec<i32> = vec![2, 1, 10101];

    for &n in &examples {
        if count >= goal { break; }
        if seen.insert(n) {
            let output = Solution::check_record(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Interesting seed pool: boundaries, powers of 2, round numbers
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 50, 100, 500, 1000, 5000,
        10000, 50000, 99999, 100000,
    ];
    // Powers of 2 within range
    let mut p: i64 = 1;
    while p <= 100000 {
        seeds.push(p as i32);
        if p > 1 { seeds.push((p - 1) as i32); }
        if p + 1 <= 100000 { seeds.push((p + 1) as i32); }
        p *= 2;
    }
    seeds.sort();
    seeds.dedup();

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::check_record(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        // Size classes for diverse coverage
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 5),        // tiny
            1 => rng.gen_range_i64(1, 100),      // small
            2 => rng.gen_range_i64(100, 1000),   // medium
            3 => rng.gen_range_i64(1000, 10000), // large
            _ => rng.gen_range_i64(10000, 100000), // max
        } as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::check_record(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
