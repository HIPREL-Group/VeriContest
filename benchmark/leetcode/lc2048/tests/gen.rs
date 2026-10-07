use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 1000000i32,
    ensures
        0 <= result <= 1000000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 1000000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500000 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                      // halve
    } else if mutation_kind == 5 {
        0                                             // zero (min boundary)
    } else if mutation_kind == 6 {
        1000000                                       // max boundary
    } else if mutation_kind == 7 {
        1                                             // small value
    } else if mutation_kind == 8 {
        if seed >= 0 && seed <= 999999 {
            seed + (1000000 - seed) / 2               // midpoint to max
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        seed / 10                                     // order of magnitude down
    } else {
        seed                                          // fallback
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

    // Seed pool: problem examples and interesting boundary values
    let seeds: Vec<i32> = vec![
        // Examples from LeetCode
        3011, 1,
        // Boundaries
        0, 1000000,
        // Near beautiful number boundaries
        21, 22, 23,
        121, 122, 123,
        211, 212, 213,
        220, 221, 222,
        332, 333, 334,
        1332, 1333, 1334,
        3132, 3133, 3134,
        3312, 3313, 3314,
        3330, 3331, 3332,
        4443, 4444, 4445,
        14443, 14444, 14445,
        55554, 55555, 55556,
        666665, 666666, 666667,
        // Round numbers
        10, 100, 1000, 10000, 100000,
        // Misc values
        5, 50, 500, 5000, 50000, 500000,
        999999,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::next_beautiful_number(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = rng.gen_range_i64(0, 1000000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::next_beautiful_number(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
