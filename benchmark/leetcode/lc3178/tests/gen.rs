use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        2 <= seed_n <= 50,
        1 <= seed_k <= 50,
    ensures
        2 <= res.0 <= 50,
        1 <= res.1 <= 50,
{
    let n = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 50 {
        seed_n + 1                                  // nudge up
    } else if mutation_kind == 2 && seed_n > 2 {
        seed_n - 1                                  // nudge down
    } else if mutation_kind == 3 {
        if seed_n >= 2 && seed_n <= 25 {
            seed_n * 2                              // double
        } else { seed_n }
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h >= 2 { h } else { 2 }                 // halve (clamped)
    } else if mutation_kind == 5 {
        2                                           // min boundary
    } else if mutation_kind == 6 {
        50                                          // max boundary
    } else {
        seed_n                                      // fallback
    };

    let k = if mutation_kind == 7 && seed_k < 50 {
        seed_k + 1                                  // nudge up
    } else if mutation_kind == 8 && seed_k > 1 {
        seed_k - 1                                  // nudge down
    } else if mutation_kind == 9 {
        1                                           // min boundary
    } else if mutation_kind == 10 {
        50                                          // max boundary
    } else if mutation_kind == 11 {
        if seed_k >= 1 && seed_k <= 25 {
            seed_k * 2                              // double
        } else { seed_k }
    } else if mutation_kind == 12 {
        let h = seed_k / 2;
        if h >= 1 { h } else { 1 }                 // halve (clamped)
    } else if mutation_kind == 13 {
        // set k = 2*(n-1) so ball completes full cycle
        let cyc = 2 * (n - 1);
        if cyc >= 1 && cyc <= 50 { cyc } else { seed_k }
    } else {
        seed_k                                      // fallback
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
        (3, 5),
        (5, 6),
        (4, 2),
    ];
    for &(n, k) in &examples {
        if seen.insert((n, k)) {
            let result = Solution::number_of_child(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (2, 1), (2, 2), (2, 50),
        (50, 1), (50, 50), (50, 49),
        (3, 1), (3, 2), (3, 3), (3, 4),
        (10, 1), (10, 10), (10, 18), (10, 19), (10, 20),
        (25, 25), (25, 48), (25, 50),
        (2, 25), (49, 49), (50, 48),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::number_of_child(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= target_count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(2, 50) as i32;
        let sk = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::number_of_child(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
