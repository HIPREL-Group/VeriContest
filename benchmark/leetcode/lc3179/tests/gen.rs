use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        1 <= seed_k <= 1000,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
{
    let n = if mutation_kind == 0 {
        seed_n                                         // identity
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1                                     // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                     // nudge down
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 500 {
        seed_n * 2                                     // double
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h < 1 { 1 } else { h }                     // halve (clamped)
    } else if mutation_kind == 5 {
        1                                              // min boundary
    } else if mutation_kind == 6 {
        1000                                           // max boundary
    } else {
        seed_n                                         // fallback
    };

    let k = if mutation_kind == 7 && seed_k < 1000 {
        seed_k + 1                                     // nudge up
    } else if mutation_kind == 8 && seed_k > 1 {
        seed_k - 1                                     // nudge down
    } else if mutation_kind == 9 {
        seed_n                                         // set k = n
    } else if mutation_kind == 10 {
        1                                              // min boundary
    } else if mutation_kind == 11 {
        1000                                           // max boundary
    } else {
        seed_k                                         // default
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 12;

    // Example inputs from description
    let examples: Vec<(i32, i32)> = vec![(4, 5), (5, 3)];
    for (n, k) in &examples {
        if count >= target { break; }
        if seen.insert((*n as i64, *k as i64)) {
            let result = Solution::value_after_k_seconds(*n, *k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary values and interesting pairs
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 1000), (1000, 1), (1000, 1000),
        (2, 1), (1, 2), (2, 2), (3, 3), (5, 5),
        (10, 10), (50, 50), (100, 100), (500, 500),
        (2, 1000), (1000, 2), (100, 1000), (1000, 100),
        (1, 500), (500, 1), (250, 750), (750, 250),
        (10, 1), (1, 10), (100, 1), (1, 100),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n as i64, k as i64)) {
                let result = Solution::value_after_k_seconds(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sk = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n as i64, k as i64)) {
            let result = Solution::value_after_k_seconds(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
