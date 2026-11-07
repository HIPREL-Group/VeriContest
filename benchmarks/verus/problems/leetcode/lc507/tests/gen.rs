use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 100_000_000i32,
    ensures
        1 <= result <= 100_000_000i32,
{
    if mutation_kind == 0 {
        seed  // identity
    } else if mutation_kind == 1 && seed < 100_000_000 {
        seed + 1  // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1  // nudge down
    } else if mutation_kind == 3 && seed <= 50_000_000 {
        seed * 2  // double
    } else if mutation_kind == 4 {
        // halve, clamp to >= 1
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        1  // minimum
    } else if mutation_kind == 6 {
        100_000_000  // maximum
    } else if mutation_kind == 7 && seed <= 99_999_999 {
        seed + 1  // another nudge variant
    } else if mutation_kind == 8 {
        // square root region: interesting for divisor patterns
        let s = seed / 1000;
        if s >= 1 { s } else { 1 }
    } else {
        seed  // fallback
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
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let target = 100;
    let num_mutations: u8 = 9;

    let seeds: Vec<i32> = vec![
        // Known perfect numbers
        6, 28, 496, 8128, 33550336,
        // Near perfect numbers
        5, 7, 27, 29, 495, 497, 8127, 8129,
        // Powers of 2 (Mersenne prime related)
        1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024,
        // Primes (no proper divisors sum to them)
        3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
        // Highly composite numbers (many divisors)
        12, 24, 36, 48, 60, 120, 180, 240, 360, 720,
        // Boundaries
        1, 100_000_000, 99_999_999,
        // Round numbers
        10, 100, 1000, 10000, 100000, 1000000, 10000000,
    ];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let output = Solution::check_perfect_number(num);
                writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let s = if rng.next_u64() % 5 == 0 {
            rng.gen_range_i64(1, 10_000_000) as i32
        } else {
            rng.gen_range_i64(1, 1_000_000) as i32
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let output = Solution::check_perfect_number(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
            count += 1;
        }
    }
}
