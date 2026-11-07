use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_t: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 100,
        1 <= seed_t <= 10,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 10,
{
    let n: i32 = if mutation_kind == 0 {
        seed_n                                          // identity
    } else if mutation_kind == 1 && seed_n < 100 {
        seed_n + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed_n <= 50 {
            seed_n * 2                                  // double (clamped)
        } else {
            100
        }
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h < 1 { 1 } else { h }                      // halve (min 1)
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        100                                             // max boundary
    } else if mutation_kind == 7 {
        50                                              // midpoint
    } else {
        seed_n                                          // fallback
    };

    let t: i32 = if mutation_kind == 8 && seed_t < 10 {
        seed_t + 1                                      // nudge up
    } else if mutation_kind == 9 && seed_t > 1 {
        seed_t - 1                                      // nudge down
    } else if mutation_kind == 10 {
        1                                               // min boundary
    } else if mutation_kind == 11 {
        10                                              // max boundary
    } else if mutation_kind == 12 {
        5                                               // midpoint
    } else {
        seed_t                                          // identity / fallback
    };

    (n, t)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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
    let mut generated = 0;
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (10, 2),
        (15, 3),
    ];

    // Seed pool: boundary and interesting values
    let seed_pool: Vec<(i32, i32)> = vec![
        (1, 1), (1, 10), (100, 1), (100, 10),
        (1, 5), (50, 5), (10, 2), (15, 3),
        (99, 9), (11, 7), (9, 1), (10, 10),
    ];

    // First emit example inputs
    for &(n, t) in &examples {
        let output = Solution::smallest_number(n, t);
        let key = (n, t);
        if seen.insert(key) {
            writeln!(out, "{}", json!({
                "input": {"n": n, "t": t},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }

    // Emit seed pool × all mutations
    for &(sn, st) in &seed_pool {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (n, t) = generate_test_case(sn, st, mk);
            let key = (n, t);
            if seen.insert(key) {
                let output = Solution::smallest_number(n, t);
                writeln!(out, "{}", json!({
                    "input": {"n": n, "t": t},
                    "output": output
                })).unwrap();
                generated += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while generated < count {
        let sn = rng.gen_range_i64(1, 100) as i32;
        let st = rng.gen_range_i64(1, 10) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, t) = generate_test_case(sn, st, mk);
        let key = (n, t);
        if seen.insert(key) {
            let output = Solution::smallest_number(n, t);
            writeln!(out, "{}", json!({
                "input": {"n": n, "t": t},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases", generated);
}
