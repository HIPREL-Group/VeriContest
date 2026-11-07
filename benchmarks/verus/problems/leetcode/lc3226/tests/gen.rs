use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1_000_000,
        1 <= seed_k <= 1_000_000,
    ensures
        1 <= res.0 <= 1_000_000,
        1 <= res.1 <= 1_000_000,
{
    let n = if mutation_kind == 0 {
        seed_n                                              // identity
    } else if mutation_kind == 1 && seed_n < 1_000_000 {
        seed_n + 1                                          // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                          // nudge down
    } else if mutation_kind == 3 && seed_n <= 500_000 {
        seed_n * 2                                          // double
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h < 1 { 1 } else { h }                          // halve
    } else if mutation_kind == 5 {
        1                                                   // min boundary
    } else if mutation_kind == 6 {
        1_000_000                                           // max boundary
    } else {
        seed_n                                              // fallback
    };

    let k = if mutation_kind == 7 && seed_k < 1_000_000 {
        seed_k + 1                                          // nudge k up
    } else if mutation_kind == 8 && seed_k > 1 {
        seed_k - 1                                          // nudge k down
    } else if mutation_kind == 9 {
        seed_n                                              // k = n (zero changes)
    } else if mutation_kind == 10 && seed_k <= 500_000 {
        seed_k * 2                                          // double k
    } else if mutation_kind == 11 {
        let h = seed_k / 2;
        if h < 1 { 1 } else { h }                          // halve k
    } else if mutation_kind == 12 {
        1                                                   // k min boundary
    } else if mutation_kind == 13 {
        1_000_000                                           // k max boundary
    } else {
        seed_k                                              // fallback
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
        (13, 4),
        (21, 21),
        (14, 13),
    ];

    for &(n, k) in &examples {
        if count >= target_count { break; }
        if seen.insert((n, k)) {
            let result = Solution::min_changes(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: powers of 2, near-powers, boundary values, interesting bit patterns
    let seed_pool: Vec<(i32, i32)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2),
        (1, 1_000_000), (1_000_000, 1), (1_000_000, 1_000_000),
        (7, 3), (15, 7), (31, 15), (63, 31),
        (1023, 511), (4095, 2047), (65535, 32767),
        (524288, 262144), (999999, 999999),
        (128, 64), (256, 128), (512, 256),
        (1048575, 524287), (999999, 1),
        (1, 999999), (500000, 500000),
        (7, 7), (255, 255), (1023, 1023),
        (8, 4), (16, 8), (32, 16),
        (100, 50), (1000, 500), (10000, 5000),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seed_pool {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::min_changes(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(1, 1_000_000) as i32;
        let sk = rng.gen_range_i64(1, 1_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::min_changes(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
