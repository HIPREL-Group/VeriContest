use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= i32::MAX,
    ensures
        1i32 <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed                                            // identity
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1                                        // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                        // nudge down
    } else if mutation_kind == 3 {
        if seed >= -1_073_741_823 && seed <= 1_073_741_823 {
            let doubled = seed * 2;
            if doubled >= 1 { doubled } else { seed }
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let halved = seed / 2;
        if halved >= 1 { halved } else { seed }         // halve
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        i32::MAX                                        // max boundary
    } else if mutation_kind == 7 {
        if seed <= i32::MAX / 2 {
            seed * 2                                    // double (safe range)
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        if seed > 1 && seed <= i32::MAX / 2 {
            seed * 2 - 1                                // double minus 1
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        if seed < i32::MAX {
            seed + 1                                    // nudge up (alt)
        } else {
            seed
        }
    } else {
        seed                                            // fallback
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
    let examples: Vec<i32> = vec![5, 1];

    // Seed pool: powers of 2, near-powers, and boundary values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 7, 8, 9, 10, 15, 16, 17, 31, 32, 33,
        63, 64, 65, 100, 127, 128, 255, 256, 511, 512, 1000,
        1023, 1024, 2047, 2048, 4095, 4096,
        i32::MAX, i32::MAX - 1, i32::MAX / 2, i32::MAX / 2 + 1,
    ];
    // Powers of 2: 1, 2, 4, ..., 2^30
    let mut p: i64 = 1;
    while p <= i32::MAX as i64 {
        let v = p as i32;
        if v >= 1 {
            seeds.push(v);
            if v > 1 { seeds.push(v - 1); }
            if v < i32::MAX { seeds.push(v + 1); }
        }
        p *= 2;
    }

    // First emit example inputs
    for &num in &examples {
        if seen.insert(num) {
            let output = Solution::find_complement(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Then iterate seed pool × mutation_kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let output = Solution::find_complement(num);
                writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_goal {
        let s = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 11;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let output = Solution::find_complement(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
            count += 1;
        }
    }
}
