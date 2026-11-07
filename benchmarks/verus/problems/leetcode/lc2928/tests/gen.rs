use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_limit: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 50,
        1 <= seed_limit <= 50,
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 50,
{
    let n = if mutation_kind == 0 {
        seed_n                                        // identity
    } else if mutation_kind == 1 && seed_n < 50 {
        seed_n + 1                                    // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                    // nudge down
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 25 {
        seed_n * 2                                    // double
    } else if mutation_kind == 4 {
        if seed_n / 2 >= 1 { seed_n / 2 } else { 1 } // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        50                                            // max boundary
    } else if mutation_kind == 7 {
        25                                            // midpoint
    } else {
        seed_n                                        // fallback
    };

    let limit = if mutation_kind == 8 && seed_limit < 50 {
        seed_limit + 1                                // nudge up
    } else if mutation_kind == 9 && seed_limit > 1 {
        seed_limit - 1                                // nudge down
    } else if mutation_kind == 10 {
        1                                             // min boundary
    } else if mutation_kind == 11 {
        50                                            // max boundary
    } else if mutation_kind == 12 {
        seed_n                                        // limit == n
    } else if mutation_kind == 13 {
        if seed_n / 3 >= 1 { seed_n / 3 } else { 1 } // limit = n/3
    } else if mutation_kind == 14 {
        if seed_n / 2 >= 1 { seed_n / 2 } else { 1 } // limit = n/2
    } else {
        seed_limit                                    // identity
    };

    (n, limit)
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
    let num_mutations: u8 = 15;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (5, 2),
        (3, 3),
    ];

    for &(n, limit) in &examples {
        if count >= count_target { break; }
        if seen.insert((n, limit)) {
            let result = Solution::distribute_candies(n, limit);
            writeln!(out, "{}", json!({"input": {"n": n, "limit": limit}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with diverse values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 50), (50, 1), (50, 50),
        (1, 25), (25, 1), (25, 25), (50, 25),
        (2, 1), (3, 1), (10, 5), (10, 3),
        (15, 5), (20, 10), (30, 10), (30, 15),
        (40, 20), (45, 15), (48, 16), (50, 17),
        (6, 2), (9, 3), (12, 4), (33, 11),
    ];

    // Seed pool × mutation_kind
    for &(sn, sl) in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let (n, limit) = generate_test_case(sn, sl, mk);
            if seen.insert((n, limit)) {
                let result = Solution::distribute_candies(n, limit);
                writeln!(out, "{}", json!({"input": {"n": n, "limit": limit}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= count_target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let sn = rng.gen_range_i64(1, 50) as i32;
        let sl = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, limit) = generate_test_case(sn, sl, mk);
        if seen.insert((n, limit)) {
            let result = Solution::distribute_candies(n, limit);
            writeln!(out, "{}", json!({"input": {"n": n, "limit": limit}, "output": result})).unwrap();
            count += 1;
        }
    }
}
