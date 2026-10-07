use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_target: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1_000_000_000,
        1 <= seed_target <= 1_000_000_000,
    ensures
        1 <= res.0 <= 1000000000,
        1 <= res.1 <= 1000000000,
{
    let n = if mutation_kind == 0 {
        seed_n                                          // identity
    } else if mutation_kind == 1 && seed_n < 1_000_000_000 {
        seed_n + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 500_000_000 {
        seed_n * 2                                      // double
    } else if mutation_kind == 4 && seed_n >= 2 {
        seed_n / 2                                      // halve (seed_n >= 2 => seed_n/2 >= 1)
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000                                   // max boundary
    } else {
        seed_n                                          // fallback
    };

    let target = if mutation_kind == 7 && seed_target < 1_000_000_000 {
        seed_target + 1                                 // nudge up
    } else if mutation_kind == 8 && seed_target > 1 {
        seed_target - 1                                 // nudge down
    } else if mutation_kind == 9 {
        seed_n                                          // target = n
    } else if mutation_kind == 10 && seed_target >= 1 && seed_target <= 500_000_000 {
        seed_target * 2                                 // double target
    } else if mutation_kind == 11 && seed_target >= 2 {
        seed_target / 2                                 // halve target
    } else if mutation_kind == 12 {
        1                                               // min boundary
    } else if mutation_kind == 13 {
        1_000_000_000                                   // max boundary
    } else {
        seed_target                                     // fallback
    };

    (n, target)
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
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 14;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (2, 3),
        (3, 3),
        (1, 1),
    ];
    for (n, t) in &examples {
        if count >= target_count { break; }
        if seen.insert((*n as i64, *t as i64)) {
            let result = Solution::minimum_possible_sum(*n, *t);
            writeln!(out, "{}", json!({"input": {"n": n, "target": t}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 2), (2, 2), (1, 1_000_000_000), (1_000_000_000, 1),
        (1_000_000_000, 1_000_000_000), (2, 4), (3, 5), (4, 6),
        (5, 10), (10, 5), (100, 100), (1000, 1000),
        (500_000_000, 500_000_000), (999_999_999, 2),
        (10, 1), (10, 20), (100, 3), (50, 100),
        (1, 999_999_999), (999_999_999, 999_999_999),
    ];

    // Seed pool × mutation_kind
    for &(sn, st) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, t) = generate_test_case(sn, st, mk);
            if seen.insert((n as i64, t as i64)) {
                let result = Solution::minimum_possible_sum(n, t);
                writeln!(out, "{}", json!({"input": {"n": n, "target": t}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations across size classes
    while count < target_count {
        let sn = match count % 5 {
            0 => rng.gen_range_i64(1, 10),                        // tiny
            1 => rng.gen_range_i64(1, 1000),                      // small
            2 => rng.gen_range_i64(1000, 1_000_000),              // medium
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000),     // large
            _ => rng.gen_range_i64(999_999_000, 1_000_000_000),   // near-max
        } as i32;
        let st = match count % 5 {
            0 => rng.gen_range_i64(1, 10),
            1 => rng.gen_range_i64(1, 1000),
            2 => rng.gen_range_i64(1000, 1_000_000),
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000),
            _ => rng.gen_range_i64(999_999_000, 1_000_000_000),
        } as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, t) = generate_test_case(sn, st, mk);
        if seen.insert((n as i64, t as i64)) {
            let result = Solution::minimum_possible_sum(n, t);
            writeln!(out, "{}", json!({"input": {"n": n, "target": t}, "output": result})).unwrap();
            count += 1;
        }
    }
}
