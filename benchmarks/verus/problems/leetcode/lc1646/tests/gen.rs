use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 100,
    ensures
        0 <= result <= 100,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 100 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 && seed <= 50 {
        (seed * 2) as i32                             // double
    } else if mutation_kind == 4 {
        (seed / 2) as i32                             // halve
    } else if mutation_kind == 5 {
        0i32                                          // zero (min boundary)
    } else if mutation_kind == 6 {
        100i32                                        // max boundary
    } else if mutation_kind == 7 {
        1i32                                          // near-min boundary
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 8;

    // Example inputs from the problem description
    let examples: Vec<i32> = vec![7, 2, 3];
    for n in &examples {
        if count >= count_target { break; }
        if seen.insert(*n) {
            let result = Solution::get_maximum_generated(*n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary values and interesting points
    let seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 20, 25, 30, 40, 50, 60, 70, 80, 90,
        95, 96, 97, 98, 99, 100,
    ];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::get_maximum_generated(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let s = rng.gen_range_i64(0, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::get_maximum_generated(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }
}
