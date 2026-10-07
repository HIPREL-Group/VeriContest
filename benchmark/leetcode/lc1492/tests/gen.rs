use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        1 <= seed_k <= 1000,
    ensures
        1 <= res.1 <= res.0 <= 1000,
{
    // Build n from seed_n with mutations
    let n: i32 = if mutation_kind == 0 {
        seed_n                                          // identity
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed_n <= 500 { seed_n * 2 } else { seed_n } // double
    } else if mutation_kind == 4 {
        seed_n / 2 + 1                                  // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        1000                                            // max boundary
    } else if mutation_kind == 7 {
        // mirror around 500
        1001 - seed_n
    } else if mutation_kind == 8 {
        // clamp to middle range
        if seed_n < 100 { 100 } else if seed_n > 900 { 900 } else { seed_n }
    } else {
        seed_n                                          // fallback
    };

    // Build k: clamp seed_k to be <= n so that 1 <= k <= n
    let k: i32 = if mutation_kind == 9 {
        1                                               // k = 1 (always valid)
    } else if mutation_kind == 10 {
        n                                               // k = n (max valid k)
    } else if seed_k <= n {
        seed_k                                          // identity (already valid)
    } else {
        n                                               // clamp to n
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
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
    let num_mutations: u8 = 11;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (12, 3),    // output 3
        (7, 2),     // output 7
        (4, 4),     // output -1
    ];

    for &(n, k) in &examples {
        if count >= count_goal { break; }
        if seen.insert((n, k)) {
            let output = Solution::kth_factor(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundaries, interesting values
    let seed_ns: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,                // small
        12, 16, 24, 30, 36, 48, 60, 100,               // highly composite
        997, 991, 983, 977, 971,                        // primes near 1000
        500, 501, 999, 1000,                            // near boundaries
        100, 200, 300, 400, 600, 700, 800, 900,         // round values
        64, 128, 256, 512,                              // powers of 2
    ];

    let seed_ks: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 20, 50, 100, 500, 1000,
    ];

    // Seed pool × mutation_kind
    for &sn in &seed_ns {
        for &sk in &seed_ks {
            for mk in 0..num_mutations {
                if count >= count_goal { break; }
                let (n, k) = generate_test_case(sn, sk, mk);
                if seen.insert((n, k)) {
                    let output = Solution::kth_factor(n, k);
                    writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
                    count += 1;
                }
            }
            if count >= count_goal { break; }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_goal {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sk = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let output = Solution::kth_factor(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
            count += 1;
        }
    }
}
