use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        1 <= seed_k <= seed_n,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= res.0,
{
    let n = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 3 && seed_n >= 2 && seed_n <= 500 {
        seed_n * 2
    } else if mutation_kind == 4 {
        seed_n / 2 + 1
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1000
    } else {
        seed_n
    };

    // Clamp k to be valid for the chosen n
    let k = if mutation_kind == 7 {
        1 // min boundary
    } else if mutation_kind == 8 {
        n // max boundary (k == n)
    } else if mutation_kind == 9 {
        (n + 1) / 2 // middle value
    } else if mutation_kind == 10 && seed_k < n {
        seed_k + 1
    } else if mutation_kind == 11 && seed_k > 1 {
        seed_k - 1
    } else if seed_k <= n {
        seed_k
    } else {
        n // clamp to n if seed_k > n after n mutation
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 12;

    // Example inputs from problem description + boundary values
    let seeds: Vec<(i32, i32)> = vec![
        (3, 2),     // example 1
        (5, 5),     // example 2
        (20, 11),   // example 3
        (1, 1),     // minimum
        (1000, 1),  // max n, min k
        (1000, 1000), // max n, max k
        (1000, 500),  // max n, mid k
        (2, 1), (2, 2),
        (10, 1), (10, 5), (10, 10),
        (100, 1), (100, 50), (100, 100),
        (500, 1), (500, 250), (500, 500),
        (999, 1), (999, 500), (999, 999),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::rearrange_sticks(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sk = rng.gen_range_i64(1, sn as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::rearrange_sticks(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
