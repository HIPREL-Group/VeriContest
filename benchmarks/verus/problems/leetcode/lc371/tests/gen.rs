use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        -1000 <= seed_a <= 1000,
        -1000 <= seed_b <= 1000,
    ensures
        -1000 <= res.0 <= 1000,
        -1000 <= res.1 <= 1000,
{
    let a = if mutation_kind == 0 {
        seed_a                                          // identity
    } else if mutation_kind == 1 && seed_a < 1000 {
        seed_a + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_a > -1000 {
        seed_a - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_a >= -1000 && seed_a <= 1000 {
        -seed_a                                         // negate
    } else if mutation_kind == 4 {
        if seed_a >= -500 && seed_a <= 500 {
            seed_a * 2                                  // double
        } else { seed_a }
    } else if mutation_kind == 5 {
        seed_a / 2                                      // halve
    } else if mutation_kind == 6 {
        0                                               // zero
    } else if mutation_kind == 7 {
        -1000                                           // min boundary
    } else if mutation_kind == 8 {
        1000                                            // max boundary
    } else {
        seed_a                                          // fallback
    };

    let b = if mutation_kind == 9 && seed_b < 1000 {
        seed_b + 1                                      // nudge up
    } else if mutation_kind == 10 && seed_b > -1000 {
        seed_b - 1                                      // nudge down
    } else if mutation_kind == 11 && seed_b >= -1000 && seed_b <= 1000 {
        -seed_b                                         // negate
    } else if mutation_kind == 12 {
        if seed_b >= -500 && seed_b <= 500 {
            seed_b * 2                                  // double
        } else { seed_b }
    } else if mutation_kind == 13 {
        seed_b / 2                                      // halve
    } else if mutation_kind == 14 {
        0                                               // zero b
    } else if mutation_kind == 15 {
        seed_a                                          // b = a
    } else {
        seed_b                                          // identity
    };

    (a, b)
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
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 16;

    // Example inputs from description.md + boundary/interesting seeds
    let seeds: Vec<(i32, i32)> = vec![
        (1, 2),                 // example 1
        (2, 3),                 // example 2
        (0, 0),
        (0, 1), (1, 0),
        (-1, 0), (0, -1),
        (-1, 1), (1, -1),
        (-1000, -1000),
        (-1000, 1000),
        (1000, -1000),
        (1000, 1000),
        (-1000, 0), (0, -1000),
        (1000, 0), (0, 1000),
        (500, 500), (-500, -500),
        (999, 1), (1, 999),
        (-999, -1), (-1, -999),
        (42, -42), (-42, 42),
        (100, 200), (-100, -200),
        (333, -333), (777, 223),
    ];

    // Seed pool × mutation_kind
    for &(sa, sb) in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let (a, b) = generate_test_case(sa, sb, mk);
            if seen.insert((a, b)) {
                let result = Solution::get_sum(a, b);
                writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= count_target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let sa = rng.gen_range_i64(-1000, 1000) as i32;
        let sb = rng.gen_range_i64(-1000, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (a, b) = generate_test_case(sa, sb, mk);
        if seen.insert((a, b)) {
            let result = Solution::get_sum(a, b);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": result})).unwrap();
            count += 1;
        }
    }
}
