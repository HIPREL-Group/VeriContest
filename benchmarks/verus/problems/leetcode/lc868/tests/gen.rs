use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000_000i32,
    ensures
        1 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 && seed <= 500_000_000 {
        // double
        seed * 2
    } else if mutation_kind == 4 {
        // halve (min 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000
    } else if mutation_kind == 7 && seed <= 999_999_999 {
        // add small offset
        seed + 1
    } else if mutation_kind == 8 {
        // clamp to middle of range
        500_000_000
    } else if mutation_kind == 9 && seed >= 3 {
        // integer square root approximation: seed / 3
        seed / 3
    } else {
        // fallback
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![22, 8, 5];

    // Seed pool: powers of 2, interesting bit patterns, boundaries
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        22,   // example: binary gap 2
        15,   // 1111: gap 1
        21,   // 10101: gap 2
        85,   // 1010101: gap 2
        170,  // 10101010: gap 2
        100, 255, 256, 512, 1000,
        1_000_000_000, 999_999_999,
        // single bit (gap = 0)
        1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096,
        // two adjacent bits (gap = 1)
        3, 6, 12, 24, 48, 96, 192,
        // two bits far apart
        // 1...1 patterns
        5,      // 101
        9,      // 1001
        17,     // 10001
        33,     // 100001
        65,     // 1000001
        129,    // 10000001
        257,    // 100000001
        513,    // 1000000001
    ];

    // Powers of 2 up to 10^9
    let mut p: i64 = 1;
    while p <= 1_000_000_000 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
            if p + 1 <= 1_000_000_000 {
                seeds.push((p + 1) as i32);
            }
        }
        p *= 2;
    }

    // Add examples first
    for &n in &examples {
        if seen.insert(n) && count < goal {
            let output = Solution::binary_gap(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool × mutations
    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::binary_gap(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + mutations
    while count < goal {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::binary_gap(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
