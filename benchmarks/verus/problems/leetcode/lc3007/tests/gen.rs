use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_k: i64, seed_x: i32, mutation_kind: u8) -> (result: (i64, i32))
    requires
        1 <= seed_k <= 1_000_000_000_000_000i64,
        1 <= seed_x <= 8i32,
    ensures
        1 <= result.0 <= 1_000_000_000_000_000i64,
        1 <= result.1 <= 8i32,
{
    let k: i64;
    let x: i32;

    if mutation_kind == 0 {
        // identity
        k = seed_k;
        x = seed_x;
    } else if mutation_kind == 1 && seed_k < 1_000_000_000_000_000i64 {
        // nudge k up
        k = seed_k + 1;
        x = seed_x;
    } else if mutation_kind == 2 && seed_k > 1 {
        // nudge k down
        k = seed_k - 1;
        x = seed_x;
    } else if mutation_kind == 3 {
        // halve k
        let half = seed_k / 2;
        k = if half >= 1 { half } else { 1 };
        x = seed_x;
    } else if mutation_kind == 4 {
        // double k (clamped)
        if seed_k <= 500_000_000_000_000i64 {
            k = seed_k * 2;
        } else {
            k = 1_000_000_000_000_000i64;
        }
        x = seed_x;
    } else if mutation_kind == 5 {
        // k = 1 (min boundary)
        k = 1;
        x = seed_x;
    } else if mutation_kind == 6 {
        // k = max boundary
        k = 1_000_000_000_000_000i64;
        x = seed_x;
    } else if mutation_kind == 7 && seed_x < 8 {
        // nudge x up
        k = seed_k;
        x = seed_x + 1;
    } else if mutation_kind == 8 && seed_x > 1 {
        // nudge x down
        k = seed_k;
        x = seed_x - 1;
    } else if mutation_kind == 9 {
        // x = 1 (min boundary)
        k = seed_k;
        x = 1;
    } else if mutation_kind == 10 {
        // x = 8 (max boundary)
        k = seed_k;
        x = 8;
    } else if mutation_kind == 11 {
        // both boundaries: k min, x min
        k = 1;
        x = 1;
    } else if mutation_kind == 12 {
        // both boundaries: k max, x max
        k = 1_000_000_000_000_000i64;
        x = 8;
    } else if mutation_kind == 13 {
        // k min, x max
        k = 1;
        x = 8;
    } else if mutation_kind == 14 {
        // k max, x min
        k = 1_000_000_000_000_000i64;
        x = 1;
    } else {
        // fallback: identity
        k = seed_k;
        x = seed_x;
    }

    (k, x)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_range_i64(lo as i64, hi as i64) as i32
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

    // Example inputs from description.md
    let examples: Vec<(i64, i32)> = vec![
        (9, 1),
        (7, 2),
    ];

    for &(k, x) in &examples {
        if count >= count_goal { break; }
        let output = Solution::find_maximum_number(k, x);
        if seen.insert((k, x)) {
            writeln!(out, "{}", json!({"input": {"k": k, "x": x}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pools for k and x
    let k_seeds: Vec<i64> = vec![
        1, 2, 3, 4, 5, 10, 100, 1000,
        1_000_000, 1_000_000_000, 1_000_000_000_000,
        500_000_000_000_000, 999_999_999_999_999, 1_000_000_000_000_000,
    ];
    let x_seeds: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8];

    // Iterate seed pools with all mutations
    for &sk in &k_seeds {
        for &sx in &x_seeds {
            for mk in 0..=15u8 {
                if count >= count_goal { break; }
                let (k, x) = generate_test_case(sk, sx, mk);
                if seen.insert((k, x)) {
                    let output = Solution::find_maximum_number(k, x);
                    writeln!(out, "{}", json!({"input": {"k": k, "x": x}, "output": output})).unwrap();
                    count += 1;
                }
            }
            if count >= count_goal { break; }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random inputs
    while count < count_goal {
        // Size classes for k
        let sk: i64 = match count % 5 {
            0 => rng.gen_range_i64(1, 10),                            // tiny
            1 => rng.gen_range_i64(1, 1_000),                         // small
            2 => rng.gen_range_i64(1_000, 1_000_000),                 // medium
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000_000),     // large
            _ => rng.gen_range_i64(1_000_000_000_000, 1_000_000_000_000_000), // max
        };
        let sx: i32 = rng.gen_range_i32(1, 8);
        let mk = rng.gen_u8() % 16;
        let (k, x) = generate_test_case(sk, sx, mk);
        if seen.insert((k, x)) {
            let output = Solution::find_maximum_number(k, x);
            writeln!(out, "{}", json!({"input": {"k": k, "x": x}, "output": output})).unwrap();
            count += 1;
        }
    }
}
