use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        2i32 <= seed <= 10000i32,
    ensures
        2 <= result <= 10000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 10000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 2 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed >= 2 && seed <= 5000 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 2 { h } else { 2 }                   // halve (clamp to min)
    } else if mutation_kind == 5 {
        2                                             // min boundary
    } else if mutation_kind == 6 {
        10000                                         // max boundary
    } else if mutation_kind == 7 {
        5000                                          // midpoint
    } else if mutation_kind == 8 {
        if seed <= 9998 {
            seed + 2                                  // nudge up by 2
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        if seed >= 4 {
            seed - 2                                  // nudge down by 2
        } else {
            seed
        }
    } else {
        seed                                          // fallback
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
    let mut done = 0usize;

    // Seed pool: examples from description + interesting values
    let seeds: Vec<i32> = vec![
        2, 11,                                     // examples from description
        3, 4, 5, 10, 100, 1000, 9999, 10000,      // boundaries / round numbers
        99, 101, 999, 1001, 5000, 7777,            // interesting values
        20, 200, 2000, 111, 1111,                  // no-zero-heavy values
    ];

    // Phase 1: seed pool × all mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if done >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::get_no_zero_integers(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                done += 1;
            }
        }
        if done >= count { break; }
    }

    // Phase 2: random seeds + random mutations
    while done < count {
        let s = rng.gen_range_i64(2, 10000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::get_no_zero_integers(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            done += 1;
        }
    }
}
