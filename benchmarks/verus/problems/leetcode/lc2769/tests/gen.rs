use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_num: i32, seed_t: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_num <= 50,
        1 <= seed_t <= 50,
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 50,
{
    let num = if mutation_kind == 0 {
        seed_num                                        // identity
    } else if mutation_kind == 1 && seed_num < 50 {
        seed_num + 1                                    // nudge up
    } else if mutation_kind == 2 && seed_num > 1 {
        seed_num - 1                                    // nudge down
    } else if mutation_kind == 3 && seed_num >= 1 && seed_num <= 25 {
        seed_num * 2                                    // double
    } else if mutation_kind == 4 {
        let h = seed_num / 2;
        if h < 1 { 1 } else { h }                      // halve (clamped)
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        50                                              // max boundary
    } else if mutation_kind == 7 {
        25                                              // midpoint
    } else {
        seed_num                                        // fallback
    };

    let t = if mutation_kind == 8 && seed_t < 50 {
        seed_t + 1                                      // nudge t up
    } else if mutation_kind == 9 && seed_t > 1 {
        seed_t - 1                                      // nudge t down
    } else if mutation_kind == 10 {
        1                                               // min boundary
    } else if mutation_kind == 11 {
        50                                              // max boundary
    } else if mutation_kind == 12 && seed_t >= 1 && seed_t <= 25 {
        seed_t * 2                                      // double t
    } else if mutation_kind == 13 {
        let h = seed_t / 2;
        if h < 1 { 1 } else { h }                      // halve t (clamped)
    } else if mutation_kind == 14 {
        seed_num                                        // t = num
    } else {
        seed_t                                          // fallback
    };

    (num, t)
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
    let num_mutations: u8 = 15;

    // Seed pool: examples from description + boundary/interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (4, 1),   // example 1
        (3, 2),   // example 2
        (1, 1),   // min, min
        (50, 50), // max, max
        (1, 50),  // min num, max t
        (50, 1),  // max num, min t
        (25, 25), // midpoint
        (10, 10),
        (1, 25),
        (25, 1),
    ];

    // First pass: iterate seed pool × all mutations
    for &(sn, st) in &seeds {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (num, t) = generate_test_case(sn, st, mk);
            let key = (num, t);
            if seen.insert(key) {
                let result = Solution::the_maximum_achievable_x(num, t);
                writeln!(out, "{}", json!({
                    "input": {"num": num, "t": t},
                    "output": result
                })).unwrap();
                generated += 1;
            }
        }
    }

    // Second pass: random seeds + random mutations
    while generated < count {
        let sn = rng.gen_range_i64(1, 50) as i32;
        let st = rng.gen_range_i64(1, 50) as i32;
        // Mix in boundary values ~20% of the time
        let sn = if generated % 5 == 0 {
            *[1i32, 50, 25, 2, 49].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            sn
        };
        let st = if generated % 5 == 1 {
            *[1i32, 50, 25, 2, 49].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            st
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (num, t) = generate_test_case(sn, st, mk);
        let key = (num, t);
        if seen.insert(key) {
            let result = Solution::the_maximum_achievable_x(num, t);
            writeln!(out, "{}", json!({
                "input": {"num": num, "t": t},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
