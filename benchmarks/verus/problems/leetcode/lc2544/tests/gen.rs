use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // Identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // Nudge +1
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // Nudge -1
        seed - 1
    } else if mutation_kind == 3 {
        // Double (if in range)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // Halve (at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // Min boundary
        1
    } else if mutation_kind == 6 {
        // Max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // Replace with 1-digit value
        if seed % 9 >= 1 {
            seed % 9
        } else {
            1
        }
    } else if mutation_kind == 8 {
        // Replace with a power-of-10 if possible
        if seed <= 100 {
            10
        } else if seed <= 1_000 {
            100
        } else if seed <= 10_000 {
            1_000
        } else if seed <= 100_000 {
            10_000
        } else if seed <= 1_000_000 {
            100_000
        } else if seed <= 10_000_000 {
            1_000_000
        } else if seed <= 100_000_000 {
            10_000_000
        } else {
            100_000_000
        }
    } else if mutation_kind == 9 {
        // All-same-digit number: 111...1 with same digit count as seed
        if seed >= 1_000_000_000 {
            1_000_000_000
        } else if seed >= 100_000_000 {
            111_111_111
        } else if seed >= 10_000_000 {
            11_111_111
        } else if seed >= 1_000_000 {
            1_111_111
        } else if seed >= 100_000 {
            111_111
        } else if seed >= 10_000 {
            11_111
        } else if seed >= 1_000 {
            1_111
        } else if seed >= 100 {
            111
        } else if seed >= 10 {
            11
        } else {
            1
        }
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from the problem description
    let examples: Vec<i32> = vec![521, 111, 886996];

    // Interesting seed pool
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9,
        10, 11, 99, 100, 101, 999,
        1000, 9999, 10000, 99999,
        100000, 999999, 1000000, 9999999,
        10000000, 99999999, 100000000, 999999999,
        1000000000,
        123456789, 987654321, 111111111, 999999999,
        521, 111, 886996,
    ];

    // Powers of 10
    let mut p: i64 = 1;
    while p <= 1_000_000_000 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
            seeds.push(((p + 1).min(1_000_000_000)) as i32);
        }
        p *= 10;
    }

    // Emit example test cases first
    for &n in &examples {
        if seen.insert(n) && generated < count {
            let output = Solution::alternate_digit_sum(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Emit from seed pool with mutations
    for &s in &seeds {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::alternate_digit_sum(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random inputs
    while generated < count {
        // Size classes for diverse digit counts
        let (lo, hi): (i64, i64) = match generated % 5 {
            0 => (1, 9),                          // 1 digit
            1 => (10, 999),                       // 2-3 digits
            2 => (1_000, 999_999),                // 4-6 digits
            3 => (1_000_000, 999_999_999),        // 7-9 digits
            _ => (1_000_000_000, 1_000_000_000),  // 10 digits
        };
        let s = rng.gen_range_i64(lo, hi) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::alternate_digit_sum(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
