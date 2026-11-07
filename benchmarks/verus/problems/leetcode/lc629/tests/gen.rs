use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        0 <= seed_k <= 1000,
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
    } else if mutation_kind == 3 {
        if seed_n >= 1 && seed_n <= 500 {
            seed_n * 2                                // double
        } else { seed_n }
    } else if mutation_kind == 4 {
        if seed_n / 2 >= 1 { seed_n / 2 } else { 1 } // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        1000                                          // max boundary
    } else {
        seed_n
    };

    let k = if mutation_kind == 7 {
        0                                             // k = 0 boundary
    } else if mutation_kind == 8 {
        1000                                          // k = max boundary
    } else if mutation_kind == 9 && seed_k < 1000 {
        seed_k + 1                                    // nudge k up
    } else if mutation_kind == 10 && seed_k > 0 {
        seed_k - 1                                    // nudge k down
    } else if mutation_kind == 11 {
        if seed_k >= 0 && seed_k <= 500 {
            seed_k * 2                                // double k
        } else { seed_k }
    } else if mutation_kind == 12 {
        seed_k / 2                                    // halve k
    } else {
        seed_k
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
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (3, 0),
        (3, 1),
    ];
    for &(n, k) in &examples {
        if count >= target_count { break; }
        if seen.insert((n, k)) {
            let result = Solution::k_inverse_pairs(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Diverse seed pool
    let seeds: Vec<(i32, i32)> = vec![
        (1, 0), (1, 1), (1, 1000),
        (2, 0), (2, 1), (2, 2),
        (3, 0), (3, 1), (3, 3),
        (5, 0), (5, 5), (5, 10),
        (10, 0), (10, 10), (10, 45),
        (100, 0), (100, 100), (100, 500), (100, 1000),
        (500, 0), (500, 250), (500, 500), (500, 1000),
        (1000, 0), (1000, 1), (1000, 500), (1000, 999), (1000, 1000),
        (1, 0), (2, 0), (3, 0), (4, 0), (5, 0),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::k_inverse_pairs(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sk = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::k_inverse_pairs(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
