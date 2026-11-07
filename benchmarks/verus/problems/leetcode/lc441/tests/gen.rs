use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= i32::MAX,
    ensures
        1 <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 1_073_741_823 {                        // i32::MAX / 2
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let half = seed / 2;
        if half >= 1 { half } else { 1 }                  // halve (clamped)
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        i32::MAX                                          // max boundary
    } else if mutation_kind == 7 {
        let third = seed / 3;
        if third >= 1 { third } else { 1 }                // third (clamped)
    } else if mutation_kind == 8 {
        if seed <= 2_147_483_637 {                        // i32::MAX - 10
            seed + 10                                     // jump up
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        if seed >= 11 {
            seed - 10                                     // jump down
        } else {
            seed
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
    let examples: Vec<i32> = vec![5, 8];

    for &n in &examples {
        if count >= goal { break; }
        if seen.insert(n) {
            let output = Solution::arrange_coins(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary values, triangular numbers, powers of 2
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 10, 15, 21, 28, 36, 45, 55, 100,
        1000, 10_000, 100_000, 1_000_000, 10_000_000,
        100_000_000, 1_000_000_000, i32::MAX,
        i32::MAX - 1, i32::MAX / 2,
    ];
    // Triangular numbers k*(k+1)/2
    let mut k: i64 = 1;
    while k * (k + 1) / 2 <= i32::MAX as i64 {
        let tri = (k * (k + 1) / 2) as i32;
        seeds.push(tri);
        if tri > 1 { seeds.push(tri - 1); }
        if tri < i32::MAX { seeds.push(tri + 1); }
        k *= 2;
    }
    // Powers of 2
    let mut p: i64 = 1;
    while p <= i32::MAX as i64 {
        seeds.push(p as i32);
        if p > 1 { seeds.push((p - 1) as i32); }
        if p + 1 <= i32::MAX as i64 { seeds.push((p + 1) as i32); }
        p *= 2;
    }

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::arrange_coins(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random values
    while count < goal {
        let s = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::arrange_coins(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
