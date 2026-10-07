use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 1_000_000i32,
    ensures
        0i32 <= result <= 1_000_000i32,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 1_000_000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500_000 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                      // halve
    } else if mutation_kind == 5 {
        0                                             // zero (boundary)
    } else if mutation_kind == 6 {
        1_000_000                                     // max boundary
    } else if mutation_kind == 7 {
        seed / 10                                     // drop last digit
    } else if mutation_kind == 8 {
        if seed <= 100_000 {
            seed * 10                                 // append zero (trailing zero case)
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        seed % 10                                     // keep last digit only
    } else if mutation_kind == 10 {
        1                                             // boundary: single digit nonzero
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Seed pool: examples from description + interesting values
    let seeds: Vec<i32> = vec![
        // Examples from description.md
        526, 1800, 0,
        // Boundary values
        1, 1_000_000,
        // Numbers with trailing zeros (double reversal changes them)
        10, 100, 1000, 10000, 100000,
        20, 300, 4500, 67000, 890000,
        // Numbers without trailing zeros (double reversal preserves them)
        7, 12, 123, 1234, 12345, 123456,
        // Round numbers
        50, 500, 5000, 50000, 500000,
        // Single digit
        2, 3, 4, 5, 6, 7, 8, 9,
        // Palindromes
        11, 22, 121, 1221, 12321,
        // Near boundaries
        999999, 999998,
    ];

    for &s in &seeds {
        for mk in 0..=11u8 {
            if count >= goal { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let output = Solution::is_same_after_reversals(num);
                writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = rng.gen_range_i64(0, 1_000_000) as i32;
        let mk = rng.gen_u8() % 12;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let output = Solution::is_same_after_reversals(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
            count += 1;
        }
    }
}
