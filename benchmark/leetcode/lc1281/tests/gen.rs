use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 100000,
    ensures
        1 <= result <= 100000,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 100000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50000 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                  // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        100000                                        // max boundary
    } else if mutation_kind == 7 {
        // map to range [1, 9] (single digit)
        (seed - 1) % 9 + 1
    } else if mutation_kind == 8 {
        // map to range [10, 99] (two digits)
        (seed - 1) % 90 + 10
    } else if mutation_kind == 9 {
        // map to range [100, 999] (three digits)
        (seed - 1) % 900 + 100
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, seen: &mut HashSet<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_goal || !seen.insert(n) {
            return;
        }
        let output = Solution::subtract_product_and_sum(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<i32> = vec![234, 4421];
    for &n in &examples {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Interesting seed pool
    let seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9,            // single digits
        10, 11, 19, 20, 50, 99,                 // two digits
        100, 111, 199, 500, 999,                // three digits
        1000, 1111, 5000, 9999,                 // four digits
        10000, 11111, 50000, 99999, 100000,     // five-six digits
        12345, 54321, 10001, 99990,             // patterns
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            emit(n, &mut seen, &mut out, &mut count);
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_goal {
        let s = rng.gen_range_i64(1, 100000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        emit(n, &mut seen, &mut out, &mut count);
    }
}
