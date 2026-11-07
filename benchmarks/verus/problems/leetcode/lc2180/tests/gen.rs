use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1000,
    ensures
        1 <= result <= 1000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 1000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2 + 1                              // halve (stay >= 1)
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        1000                                          // max boundary
    } else if mutation_kind == 7 {
        500                                           // midpoint
    } else if mutation_kind == 8 {
        if seed <= 999 {
            1000 - seed + 1                           // mirror
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        if seed <= 990 {
            seed + 10                                 // nudge +10
        } else {
            seed
        }
    } else if mutation_kind == 10 {
        if seed >= 11 {
            seed - 10                                 // nudge -10
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

    // Seed pool: example inputs and interesting boundary values
    let seeds: Vec<i32> = vec![
        4, 30,                                        // examples from description
        1, 2, 3, 5, 9, 10, 11, 19, 20, 21,           // small values
        99, 100, 101,                                  // around 100
        500, 501,                                      // midpoint
        999, 1000,                                     // near max
        111, 222, 333, 444, 555, 666, 777, 888,        // repdigits
        123, 456, 789,                                 // ascending digits
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::count_even(n);
                writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        // Size classes for diverse coverage
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,       // tiny
            1 => rng.gen_range_i64(1, 50) as i32,       // small
            2 => rng.gen_range_i64(51, 200) as i32,     // medium
            3 => rng.gen_range_i64(201, 700) as i32,    // large
            _ => rng.gen_range_i64(701, 1000) as i32,   // max range
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::count_even(n);
            writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
