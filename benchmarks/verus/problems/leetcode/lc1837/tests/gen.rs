use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_n <= 100,
        2 <= seed_k <= 10,
    ensures
        1 <= result.0 <= 100,
        2 <= result.1 <= 10,
{
    let n: i32;
    let k: i32;

    if mutation_kind == 0 {
        // identity
        n = seed_n;
        k = seed_k;
    } else if mutation_kind == 1 {
        // nudge n up
        n = if seed_n < 100 { seed_n + 1 } else { seed_n };
        k = seed_k;
    } else if mutation_kind == 2 {
        // nudge n down
        n = if seed_n > 1 { seed_n - 1 } else { seed_n };
        k = seed_k;
    } else if mutation_kind == 3 {
        // nudge k up
        n = seed_n;
        k = if seed_k < 10 { seed_k + 1 } else { seed_k };
    } else if mutation_kind == 4 {
        // nudge k down
        n = seed_n;
        k = if seed_k > 2 { seed_k - 1 } else { seed_k };
    } else if mutation_kind == 5 {
        // n = min boundary
        n = 1;
        k = seed_k;
    } else if mutation_kind == 6 {
        // n = max boundary
        n = 100;
        k = seed_k;
    } else if mutation_kind == 7 {
        // k = min boundary
        n = seed_n;
        k = 2;
    } else if mutation_kind == 8 {
        // k = max boundary
        n = seed_n;
        k = 10;
    } else if mutation_kind == 9 {
        // halve n (clamp to 1)
        n = if seed_n / 2 >= 1 { seed_n / 2 } else { 1 };
        k = seed_k;
    } else if mutation_kind == 10 {
        // double n (clamp to 100)
        n = if seed_n * 2 <= 100 { seed_n * 2 } else { 100 };
        k = seed_k;
    } else if mutation_kind == 11 {
        // both boundaries: min n, min k
        n = 1;
        k = 2;
    } else if mutation_kind == 12 {
        // both boundaries: max n, max k
        n = 100;
        k = 10;
    } else if mutation_kind == 13 {
        // both boundaries: min n, max k
        n = 1;
        k = 10;
    } else if mutation_kind == 14 {
        // both boundaries: max n, min k
        n = 100;
        k = 2;
    } else {
        // fallback: identity
        n = seed_n;
        k = seed_k;
    }

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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (34, 6),
        (10, 10),
    ];
    for (n, k) in &examples {
        if generated >= count { break; }
        if seen.insert((*n, *k)) {
            let output = Solution::sum_base(*n, *k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: interesting n values × interesting k values × all mutations
    let n_seeds: Vec<i32> = vec![1, 2, 3, 5, 10, 25, 50, 75, 99, 100];
    let k_seeds: Vec<i32> = vec![2, 3, 5, 7, 8, 10];

    for &sn in &n_seeds {
        for &sk in &k_seeds {
            for mk in 0..=15u8 {
                if generated >= count { break; }
                let (n, k) = generate_test_case(sn, sk, mk);
                if seen.insert((n, k)) {
                    let output = Solution::sum_base(n, k);
                    writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
                    generated += 1;
                }
            }
            if generated >= count { break; }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random inputs
    while generated < count {
        let sn = rng.gen_range_i64(1, 100) as i32;
        let sk = rng.gen_range_i64(2, 10) as i32;
        let mk = rng.gen_u8() % 16;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let output = Solution::sum_base(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
