use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 33i32,
    ensures
        0 <= result <= 33,
{
    if mutation_kind == 0 {
        seed                                        // identity
    } else if mutation_kind == 1 && seed < 33 {
        seed + 1                                    // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                    // nudge down
    } else if mutation_kind == 3 && seed <= 16 {
        seed * 2                                    // double
    } else if mutation_kind == 4 {
        seed / 2                                    // halve
    } else if mutation_kind == 5 {
        0                                           // zero / min boundary
    } else if mutation_kind == 6 {
        33                                          // max boundary
    } else if mutation_kind == 7 {
        16                                          // middle
    } else if mutation_kind == 8 {
        33 - seed                                   // mirror
    } else {
        seed                                        // fallback
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;
    // Only 34 unique values (0..=33) exist, so cap count
    let count = count.min(34);

    // Example inputs from description.md
    let examples: Vec<i32> = vec![3, 0, 1];

    // Seed pool: all boundary and interesting values
    let seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 5, 10, 15, 16, 17, 20, 25, 30, 31, 32, 33,
    ];

    // First, emit example inputs
    for &row_index in &examples {
        if total >= count { break; }
        if seen.insert(row_index) {
            let output = Solution::get_row(row_index);
            writeln!(out, "{}", json!({"input": {"row_index": row_index}, "output": output})).unwrap();
            total += 1;
        }
    }

    // Then, iterate seed pool × mutation kinds
    for &s in &seeds {
        for mk in 0..=9u8 {
            if total >= count { break; }
            let row_index = generate_test_case(s, mk);
            if seen.insert(row_index) {
                let output = Solution::get_row(row_index);
                writeln!(out, "{}", json!({"input": {"row_index": row_index}, "output": output})).unwrap();
                total += 1;
            }
        }
        if total >= count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while total < count {
        let s = rng.gen_range_i64(0, 33) as i32;
        let mk = rng.gen_u8() % 10;
        let row_index = generate_test_case(s, mk);
        if seen.insert(row_index) {
            let output = Solution::get_row(row_index);
            writeln!(out, "{}", json!({"input": {"row_index": row_index}, "output": output})).unwrap();
            total += 1;
        }
    }
}
