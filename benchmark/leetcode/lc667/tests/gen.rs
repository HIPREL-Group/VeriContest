use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        2 <= seed_n <= 10_000,
        1 <= seed_k < seed_n,
    ensures
        1 <= res.1 < res.0 <= 10_000,
{
    let n = seed_n;
    let k = seed_k;

    if mutation_kind == 0 {
        // identity
        (n, k)
    } else if mutation_kind == 1 && n < 10_000 {
        // nudge n up
        (n + 1, k)
    } else if mutation_kind == 2 && n > 2 && k < n - 1 {
        // nudge n down (keep k < n-1 so k < new n)
        (n - 1, k)
    } else if mutation_kind == 3 && k > 1 {
        // nudge k down
        (n, k - 1)
    } else if mutation_kind == 4 && k + 1 < n {
        // nudge k up
        (n, k + 1)
    } else if mutation_kind == 5 {
        // k = 1 (minimum distinct diffs)
        (n, 1)
    } else if mutation_kind == 6 {
        // k = n - 1 (maximum distinct diffs)
        (n, n - 1)
    } else if mutation_kind == 7 {
        // n at minimum with valid k
        (2, 1)
    } else if mutation_kind == 8 {
        // n at maximum, keep k valid
        if k < 10_000 {
            (10_000, k)
        } else {
            (n, k)
        }
    } else if mutation_kind == 9 {
        // n at maximum, k at maximum
        (10_000, 9_999)
    } else if mutation_kind == 10 && n < 10_000 {
        // both nudge up
        (n + 1, k)
    } else if mutation_kind == 11 {
        // k = n / 2 (midpoint)
        let mid = n / 2;
        if mid >= 1 {
            (n, mid)
        } else {
            (n, k)
        }
    } else {
        // fallback: identity
        (n, k)
    }
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;
    let num_mutations: u8 = 12;

    // Seed pool: interesting (n, k) pairs
    let seeds: Vec<(i32, i32)> = vec![
        // Examples from description
        (3, 1),
        (3, 2),
        // Boundary cases
        (2, 1),
        (10_000, 9_999),
        (10_000, 1),
        (10_000, 5_000),
        // Small values
        (4, 1),
        (4, 2),
        (4, 3),
        (5, 1),
        (5, 2),
        (5, 3),
        (5, 4),
        (10, 1),
        (10, 5),
        (10, 9),
        // Medium values
        (100, 1),
        (100, 50),
        (100, 99),
        (500, 1),
        (500, 250),
        (500, 499),
        // Larger
        (1000, 1),
        (1000, 500),
        (1000, 999),
    ];

    // Generate from seed pool × mutations
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            let key = (n, k);
            if seen.insert(key) {
                let result = Solution::construct_array(n, k);
                writeln!(out, "{}", json!({
                    "input": {"n": n, "k": k},
                    "output": result
                })).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random pairs
    while generated < count {
        let n = rng.gen_range_i64(2, 10_000) as i32;
        let k = rng.gen_range_i64(1, (n - 1) as i64) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let (n2, k2) = generate_test_case(n, k, mk);
        let key = (n2, k2);
        if seen.insert(key) {
            let result = Solution::construct_array(n2, k2);
            writeln!(out, "{}", json!({
                "input": {"n": n2, "k": k2},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }
}
