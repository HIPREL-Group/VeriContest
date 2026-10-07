use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 500,
    ensures
        1 <= result <= 500,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 500 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 250 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                  // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        500                                           // max boundary
    } else if mutation_kind == 7 {
        // mirror around 250
        501 - seed
    } else if mutation_kind == 8 {
        // clamp to middle range
        if seed < 50 { 50 } else if seed > 450 { 450 } else { seed }
    } else if mutation_kind == 9 {
        // quarter region
        if seed <= 125 {
            assert(seed * 4 <= 500) by(nonlinear_arith)
                requires 1 <= seed <= 125;
            seed * 4
        } else {
            seed
        }
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

    // Seed pool: examples, boundaries, interesting values
    let seeds: Vec<i32> = vec![
        1, 2, 3,                                    // examples from description
        1, 500,                                     // boundaries
        2, 4, 6, 8, 10,                             // small evens
        3, 5, 7, 9, 11,                             // small odds
        250, 251, 499, 498,                         // near midpoint and upper boundary
        100, 200, 300, 400,                         // round values
        16, 32, 64, 128, 256,                       // powers of 2
        15, 31, 63, 127, 255,                       // powers of 2 minus 1
        50, 75, 150, 333, 444,                      // miscellaneous
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::count_orders(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    while count < count_goal {
        let s = rng.gen_range_i64(1, 500) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::count_orders(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
