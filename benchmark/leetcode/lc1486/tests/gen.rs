use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_start: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        0 <= seed_start <= 1000,
    ensures
        1 <= res.0 <= 1000,
        0 <= res.1 <= 1000,
{
    let n = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1                                    // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                    // nudge down
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 500 {
        seed_n * 2                                    // double
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h >= 1 { h } else { 1 }                   // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        1000                                          // max boundary
    } else {
        seed_n                                        // fallback
    };

    let start = if mutation_kind == 7 && seed_start < 1000 {
        seed_start + 1                                // nudge up
    } else if mutation_kind == 8 && seed_start > 0 {
        seed_start - 1                                // nudge down
    } else if mutation_kind == 9 {
        0                                             // zero
    } else if mutation_kind == 10 {
        1000                                          // max boundary
    } else if mutation_kind == 11 && seed_start >= 0 && seed_start <= 500 {
        seed_start * 2                                // double
    } else if mutation_kind == 12 {
        seed_start / 2                                // halve
    } else {
        seed_start                                    // identity / fallback
    };

    (n, start)
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 13;

    // Example inputs from description + boundary seeds
    let seeds: Vec<(i32, i32)> = vec![
        (5, 0), (4, 3),                              // examples from description
        (1, 0), (1, 1000), (1000, 0), (1000, 1000),  // boundary combos
        (1, 1), (2, 0), (2, 1), (10, 0), (10, 10),
        (100, 0), (100, 500), (500, 500),
        (1000, 500), (1, 500), (500, 0), (500, 1000),
        (3, 7), (7, 3), (8, 4), (16, 0), (32, 1),
        (100, 100), (200, 200), (999, 999),
    ];

    // Seed pool × mutation_kind
    for &(sn, ss) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (n, start) = generate_test_case(sn, ss, mk);
            if seen.insert((n as i64, start as i64)) {
                let result = Solution::xor_operation(n, start);
                writeln!(out, "{}", json!({"input": {"n": n, "start": start}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let ss = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, start) = generate_test_case(sn, ss, mk);
        if seen.insert((n as i64, start as i64)) {
            let result = Solution::xor_operation(n, start);
            writeln!(out, "{}", json!({"input": {"n": n, "start": start}, "output": result})).unwrap();
            count += 1;
        }
    }
}
