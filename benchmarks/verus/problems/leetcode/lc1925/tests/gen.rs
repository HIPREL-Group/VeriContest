use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 250,
    ensures
        1 <= result <= 250,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 250 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 {
        if seed * 2 <= 250 {
            (seed * 2) as i32                         // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed / 2 >= 1 {
            (seed / 2) as i32                         // halve
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        250                                           // max boundary
    } else if mutation_kind == 7 {
        125                                           // midpoint
    } else if mutation_kind == 8 {
        if 251 - seed >= 1 {
            (251 - seed) as i32                       // mirror
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Seed pool: example inputs and interesting boundary values
    let seeds: Vec<i32> = vec![
        5, 10,                                       // examples from description
        1, 2, 3, 4,                                  // tiny
        125, 126,                                    // midpoint
        248, 249, 250,                               // near max
        50, 100, 150, 200,                           // round values
    ];

    // Iterate seed pool × all mutation kinds
    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::count_triples(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds and mutations
    while count < goal {
        let s = rng.gen_range_i64(1, 250) as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::count_triples(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
