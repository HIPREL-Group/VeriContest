use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        100i32 <= seed <= 999i32,
    ensures
        100 <= result <= 999,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 999 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 100 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 {
        // mirror within range: 100 + (999 - seed)
        (1099 - seed) as i32
    } else if mutation_kind == 4 {
        // halve into range: map to [100, 999]
        let half = seed / 2;
        if half >= 100 {
            half
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        100                                           // min boundary
    } else if mutation_kind == 6 {
        999                                           // max boundary
    } else if mutation_kind == 7 {
        550                                           // midpoint
    } else if mutation_kind == 8 {
        // swap hundreds and units digits
        let h = seed / 100;
        let t = (seed / 10) % 10;
        let u = seed % 10;
        let swapped = u * 100 + t * 10 + h;
        if swapped >= 100 && swapped <= 999 {
            swapped
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        // clamp to lower third [100, 399]
        if seed <= 399 {
            seed
        } else {
            ((seed - 100) % 300 + 100) as i32
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    // Seed pool: example inputs and interesting values
    let seeds: Vec<i32> = vec![
        192, 100, 999,                          // examples + boundaries
        200, 300, 400, 500, 600, 700, 800, 900, // round hundreds
        111, 222, 333, 444, 555, 666, 777, 888, // repdigits
        123, 321, 456, 654, 789, 987,           // ascending/descending
        101, 110, 199, 901, 910, 991,           // near boundaries
        250, 375, 500, 625, 750,                // quarters
    ];

    // First pass: seed pool × all mutation kinds
    for &s in &seeds {
        for mk in 0u8..10 {
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::is_fascinating(n);
                writeln!(out, "{}", json!({
                    "input": {"n": n},
                    "output": result
                })).unwrap();
                total += 1;
            }
        }
    }

    // Fill remaining with random seeds × random mutations
    while total < count {
        let s = rng.gen_range_i64(100, 999) as i32;
        let mk = rng.gen_u8() % 10;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::is_fascinating(n);
            writeln!(out, "{}", json!({
                "input": {"n": n},
                "output": result
            })).unwrap();
            total += 1;
        }
    }

    eprintln!("Generated {} test cases", total);
}
