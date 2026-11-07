use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 19,
    ensures
        1 <= result <= 19,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 19 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        1                                             // min boundary
    } else if mutation_kind == 4 {
        19                                            // max boundary
    } else if mutation_kind == 5 {
        10                                            // midpoint
    } else if mutation_kind == 6 && seed >= 1 && seed <= 9 {
        seed * 2 + 1                                  // double + 1 (stays in range for seed <= 9)
    } else if mutation_kind == 7 {
        (seed - 1) / 2 + 1                            // halve toward 1
    } else if mutation_kind == 8 {
        20 - seed                                     // mirror around 10
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![3, 1];

    for &n in &examples {
        if count >= count_goal { break; }
        if seen.insert(n) {
            let output = Solution::num_trees(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: all valid values 1..=19 with all mutations
    let seeds: Vec<i32> = (1..=19).collect();
    for &s in &seeds {
        for mk in 0..=9u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::num_trees(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts_0 = 0usize;
    while count < count_goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s = rng.gen_range_i64(1, 19) as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::num_trees(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
