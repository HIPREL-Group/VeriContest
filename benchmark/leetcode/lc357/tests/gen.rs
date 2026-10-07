use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 8,
    ensures
        0 <= result <= 8,
{
    if mutation_kind == 0 {
        // Identity
        seed
    } else if mutation_kind == 1 && seed < 8 {
        // Nudge +1
        seed + 1
    } else if mutation_kind == 2 && seed > 0 {
        // Nudge -1
        seed - 1
    } else if mutation_kind == 3 {
        // Replace with 0 (min boundary)
        0
    } else if mutation_kind == 4 {
        // Replace with 8 (max boundary)
        8
    } else if mutation_kind == 5 {
        // Halve
        seed / 2
    } else if mutation_kind == 6 && seed <= 4 {
        // Double (clamped to valid range)
        seed * 2
    } else if mutation_kind == 7 {
        // Middle value
        4
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 8;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![2, 0];
    for n in &examples {
        if count >= goal { break; }
        if seen.insert(*n) {
            let result = Solution::count_numbers_with_unique_digits(*n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: all valid values and boundary cases
    let seeds: Vec<i32> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::count_numbers_with_unique_digits(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts_0 = 0usize;
    while count < goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s = rng.gen_range_i64(0, 8) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::count_numbers_with_unique_digits(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }
}
