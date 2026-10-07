use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 1_000_000_000i32,
    ensures
        0 <= result <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // Identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // Nudge +1
        seed + 1
    } else if mutation_kind == 2 && seed > 0 {
        // Nudge -1
        seed - 1
    } else if mutation_kind == 3 && seed <= 500_000_000 {
        // Double
        seed * 2
    } else if mutation_kind == 4 {
        // Halve
        seed / 2
    } else if mutation_kind == 5 {
        // Zero
        0
    } else if mutation_kind == 6 {
        // Max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // Min boundary
        0
    } else if mutation_kind == 8 {
        // 1
        1
    } else if mutation_kind == 9 {
        // Near-boundary value
        999_999_999
    } else {
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
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

    // Example inputs from description.md
    let examples: Vec<i32> = vec![3, 0, 1];

    // Interesting seed values: boundaries, perfect squares, near-squares
    let mut seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17,
        24, 25, 26, 35, 36, 37, 99, 100, 101,
        999, 1000, 1001, 9999, 10000, 10001,
        999_999_999, 1_000_000_000,
        // Perfect squares
        49, 64, 81, 121, 144, 169, 196, 225, 256, 289, 324, 361, 400,
        625, 900, 2500, 10000, 40000, 250000, 1000000,
        // Near max perfect square: 31622^2 = 999_950_884
        999_950_884, 999_950_883, 999_950_885,
    ];

    // Add example inputs first
    for &n in &examples {
        if seen.insert(n) {
            let output = Solution::bulb_switch(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Generate from interesting seeds with mutations
    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::bulb_switch(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random values across size classes
    while count < count_goal {
        let s = match count % 5 {
            0 => rng.gen_range_i64(0, 10) as i32,           // tiny
            1 => rng.gen_range_i64(0, 100) as i32,          // small
            2 => rng.gen_range_i64(100, 10000) as i32,      // medium
            3 => rng.gen_range_i64(10000, 1_000_000) as i32, // large
            _ => rng.gen_range_i64(1_000_000, 1_000_000_000) as i32, // max
        };
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::bulb_switch(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
