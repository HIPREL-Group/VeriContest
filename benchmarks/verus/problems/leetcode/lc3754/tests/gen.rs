use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0i32 <= seed <= 1_000_000_000i32,
    ensures
        0 <= result <= 1_000_000_000,
{
    if mutation_kind == 0 {
        seed                                           // identity
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1                                       // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                       // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500_000_000 {
            seed * 2                                   // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                       // halve
    } else if mutation_kind == 5 {
        0                                              // zero
    } else if mutation_kind == 6 {
        1_000_000_000                                  // max boundary
    } else if mutation_kind == 7 {
        seed / 10                                      // remove last digit
    } else if mutation_kind == 8 {
        if seed <= 100_000_000 {
            seed * 10                                  // shift left (append 0)
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        seed % 10                                      // keep only last digit
    } else {
        seed                                           // fallback
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Seed pool: interesting values for this problem
    let seeds: Vec<i32> = vec![
        // Examples from description.md
        10203004,
        1000,
        // Boundary values
        0,
        1,
        1_000_000_000,
        999_999_999,
        // Values with all non-zero digits
        123456789,
        // Values with many zeros
        100000000,
        10000,
        10,
        // Single digits
        2, 3, 4, 5, 6, 7, 8, 9,
        // Repeating digits
        111111111,
        999999999,
        // Mixed patterns
        101010101,
        505050505,
        900000009,
        12345,
        54321,
        100,
        1001,
        10001,
    ];

    let num_mutations: u8 = 10;

    // First: iterate seed pool × all mutations
    for &s in &seeds {
        for mk in 0..num_mutations {
            if generated >= count {
                break;
            }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::sum_and_multiply(n);
                writeln!(out, "{}", json!({
                    "input": {"n": n},
                    "output": output
                })).unwrap();
                generated += 1;
            }
        }
        if generated >= count {
            break;
        }
    }

    // Fill remaining with random seeds × random mutations
    while generated < count {
        let n_raw = rng.gen_range_i64(0, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let n = generate_test_case(n_raw, mk);
        if seen.insert(n) {
            let output = Solution::sum_and_multiply(n);
            writeln!(out, "{}", json!({
                "input": {"n": n},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
