use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 50,
{
    let seed_n = if seed_n < 1 { 1 } else if seed_n > 50 { 50 } else { seed_n };
    let seed_k = if seed_k < 1 { 1 } else if seed_k > 50 { 50 } else { seed_k };
    let n = if mutation_kind == 0 {
        seed_n                                          // identity
    } else if mutation_kind == 1 && seed_n < 50 {
        seed_n + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_n <= 25 {
        seed_n * 2                                      // double
    } else if mutation_kind == 4 {
        (seed_n - 1) / 2 + 1                            // halve (clamped to 1)
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        50                                              // max boundary
    } else if mutation_kind == 7 {
        25                                              // midpoint
    } else {
        seed_n                                          // fallback
    };

    let k = if mutation_kind == 8 && seed_k < 50 {
        seed_k + 1                                      // nudge up
    } else if mutation_kind == 9 && seed_k > 1 {
        seed_k - 1                                      // nudge down
    } else if mutation_kind == 10 {
        1                                               // min boundary
    } else if mutation_kind == 11 {
        50                                              // max boundary
    } else if mutation_kind == 12 {
        seed_n                                          // k = n
    } else if mutation_kind == 13 && seed_n <= 25 {
        seed_n * 2                                      // k = 2*n
    } else if mutation_kind == 14 {
        (seed_n - 1) / 2 + 1                            // k = n/2 (clamped)
    } else {
        seed_k                                          // identity / fallback
    };

    (n, k)
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
    let num_mutations: u8 = 15;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![(5, 4), (2, 6)];
    for (n, k) in &examples {
        if count >= target { break; }
        if seen.insert((*n, *k)) {
            let result = Solution::minimum_sum(*n, *k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 50), (50, 1), (50, 50),
        (1, 2), (2, 1), (25, 25), (25, 50),
        (10, 10), (10, 20), (20, 10), (30, 15),
        (1, 25), (50, 25), (49, 49), (2, 2),
        (3, 5), (5, 3), (10, 1), (1, 10),
        (40, 40), (48, 3), (3, 48), (50, 2),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::minimum_sum(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sn = rng.gen_range_i64(1, 50) as i32;
        let sk = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::minimum_sum(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
