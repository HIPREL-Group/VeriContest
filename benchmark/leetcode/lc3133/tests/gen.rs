use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_x: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 100_000_000,
        1 <= seed_x <= 100_000_000,
    ensures
        1 <= res.0 <= 100_000_000,
        1 <= res.1 <= 100_000_000,
{
    let n = if mutation_kind == 0 {
        seed_n                                            // identity
    } else if mutation_kind == 1 && seed_n < 100_000_000 {
        seed_n + 1                                        // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                        // nudge down
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 50_000_000 {
        seed_n * 2                                        // double
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h >= 1 { h } else { 1 }                       // halve
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        100_000_000                                       // max boundary
    } else {
        seed_n                                            // fallback
    };

    let x = if mutation_kind == 7 && seed_x < 100_000_000 {
        seed_x + 1                                        // nudge up
    } else if mutation_kind == 8 && seed_x > 1 {
        seed_x - 1                                        // nudge down
    } else if mutation_kind == 9 {
        1                                                 // min boundary
    } else if mutation_kind == 10 {
        100_000_000                                       // max boundary
    } else if mutation_kind == 11 && seed_x >= 1 && seed_x <= 50_000_000 {
        seed_x * 2                                        // double
    } else if mutation_kind == 12 {
        let h = seed_x / 2;
        if h >= 1 { h } else { 1 }                       // halve
    } else {
        seed_x                                            // identity / fallback
    };

    (n, x)
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
        (3, 4), (2, 7),                                   // examples from description
        (1, 1), (1, 100_000_000), (100_000_000, 1),        // boundary combos
        (100_000_000, 100_000_000),
        (1, 2), (2, 1), (2, 2),
        (10, 10), (10, 1), (1, 10),
        (100, 100), (1000, 1000),
        (50_000_000, 50_000_000),
        (99_999_999, 99_999_999),
        (5, 3), (8, 15), (16, 255), (32, 1024),
        (7, 7), (4, 8), (3, 12), (6, 5),
        (1, 3), (2, 4), (3, 1),
    ];

    // Seed pool × mutation_kind
    for &(sn, sx) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (n, x) = generate_test_case(sn, sx, mk);
            if seen.insert((n as i64, x as i64)) {
                let result = Solution::min_end(n, x);
                writeln!(out, "{}", json!({"input": {"n": n, "x": x}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sn = rng.gen_range_i64(1, 100_000_000) as i32;
        let sx = rng.gen_range_i64(1, 100_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, x) = generate_test_case(sn, sx, mk);
        if seen.insert((n as i64, x as i64)) {
            let result = Solution::min_end(n, x);
            writeln!(out, "{}", json!({"input": {"n": n, "x": x}, "output": result})).unwrap();
            count += 1;
        }
    }
}
