use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        seed != 0i32,
        -1_000_000_000i32 <= seed <= 1_000_000_000i32,
    ensures
        -1_000_000_000 <= result <= 1_000_000_000,
        result != 0,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000i32 {
        // nudge up (skip 0)
        if seed == -1 { 1i32 } else { seed + 1 }
    } else if mutation_kind == 2 && seed > -1_000_000_000i32 {
        // nudge down (skip 0)
        if seed == 1 { -1i32 } else { seed - 1 }
    } else if mutation_kind == 3 {
        // negate
        -seed
    } else if mutation_kind == 4 {
        // double (stay in range, skip 0)
        if seed >= -500_000_000 && seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        // halve (skip 0)
        let h = seed / 2;
        if h != 0 { h } else { seed }
    } else if mutation_kind == 6 {
        // min boundary
        -1_000_000_000i32
    } else if mutation_kind == 7 {
        // max boundary
        1_000_000_000i32
    } else if mutation_kind == 8 {
        1i32
    } else if mutation_kind == 9 {
        -1i32
    } else if mutation_kind == 10 {
        // absolute value
        if seed > 0 { seed } else { -seed }
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

    // Example inputs from description.md
    let examples: Vec<i32> = vec![2, 3];

    // Seed pool: interesting values for reach_number
    let mut seeds: Vec<i32> = vec![
        1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 10, -10,
        100, -100, 1000, -1000, 10000, -10000,
        1_000_000_000, -1_000_000_000,
        999_999_999, -999_999_999,
        999_999_998, -999_999_998,
    ];
    // Triangular numbers: tri(n) = n*(n+1)/2
    let mut n: i64 = 1;
    while n * (n + 1) / 2 <= 1_000_000_000 {
        let tri = (n * (n + 1) / 2) as i32;
        seeds.push(tri);
        if tri > 1 { seeds.push(tri - 1); }
        if tri < 1_000_000_000 { seeds.push(tri + 1); }
        seeds.push(-(tri));
        n += 1;
    }

    // First emit example inputs
    for &target in &examples {
        if count >= goal { break; }
        if seen.insert(target) {
            let output = Solution::reach_number(target);
            writeln!(out, "{}", json!({"input": {"target": target}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool × mutations
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let target = generate_test_case(s, mk);
            if seen.insert(target) {
                let output = Solution::reach_number(target);
                writeln!(out, "{}", json!({"input": {"target": target}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds
    while count < goal {
        let s = loop {
            let v = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
            if v != 0 { break v as i32; }
        };
        let mk = rng.gen_u8() % 11;
        let target = generate_test_case(s, mk);
        if seen.insert(target) {
            let output = Solution::reach_number(target);
            writeln!(out, "{}", json!({"input": {"target": target}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
