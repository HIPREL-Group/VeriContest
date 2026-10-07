use vstd::prelude::*;

verus! {

/// Generates a valid input `k` for the min_operations problem.
/// spec.rs requires: 1 <= k <= 100000
pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 100000i32,
    ensures
        1i32 <= result <= 100000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 100000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (clamped)
        if seed <= 50000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (clamped to at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1i32 }
    } else if mutation_kind == 5 {
        // min boundary
        1i32
    } else if mutation_kind == 6 {
        // max boundary
        100000i32
    } else if mutation_kind == 7 {
        // near-middle value
        50000i32
    } else if mutation_kind == 8 {
        // square root region (interesting for this problem)
        if seed <= 316 {
            seed
        } else {
            316i32
        }
    } else if mutation_kind == 9 {
        // small value
        if seed <= 10 {
            seed
        } else {
            10i32
        }
    } else {
        // fallback: identity
        seed
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
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![11, 1];
    for &k in &examples {
        let output = Solution::min_operations(k);
        writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
        generated += 1;
    }

    // Interesting seed pool: powers of 2, boundaries, small values, sqrt-region
    let seed_pool: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        16, 32, 64, 100, 128, 256, 316, 317, 512, 1000,
        1024, 2048, 4096, 8192, 10000, 16384, 32768, 50000, 65536, 99999, 100000,
    ];
    let num_mutations: u8 = 10;

    for &s in &seed_pool {
        for mk in 0..num_mutations {
            if generated >= count {
                break;
            }
            let k = generate_test_case(s, mk);
            let output = Solution::min_operations(k);
            writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
            generated += 1;
        }
        if generated >= count {
            break;
        }
    }

    // Fill remaining with random seeds × random mutations
    while generated < count {
        let s = rng.gen_range_i64(1, 100000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let k = generate_test_case(s, mk);
        let output = Solution::min_operations(k);
        writeln!(out, "{}", json!({"input": {"k": k}, "output": output})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
