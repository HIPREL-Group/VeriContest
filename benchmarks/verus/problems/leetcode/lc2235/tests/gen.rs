use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_num1: i32, seed_num2: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        -100 <= seed_num1 <= 100,
        -100 <= seed_num2 <= 100,
    ensures
        -100 <= res.0 <= 100,
        -100 <= res.1 <= 100,
{
    let num1 = if mutation_kind == 0 {
        seed_num1                                           // identity
    } else if mutation_kind == 1 && seed_num1 < 100 {
        seed_num1 + 1                                       // nudge up
    } else if mutation_kind == 2 && seed_num1 > -100 {
        seed_num1 - 1                                       // nudge down
    } else if mutation_kind == 3 && seed_num1 >= -100 && seed_num1 <= 100 {
        -seed_num1                                          // negate
    } else if mutation_kind == 4 {
        seed_num1 / 2                                       // halve
    } else if mutation_kind == 5 {
        0                                                   // zero
    } else if mutation_kind == 6 {
        -100                                                // min boundary
    } else if mutation_kind == 7 {
        100                                                 // max boundary
    } else if mutation_kind == 8 {
        if seed_num1 >= 0 { seed_num1 } else { -seed_num1 } // absolute value
    } else {
        seed_num1                                           // fallback
    };

    let num2 = if mutation_kind == 9 && seed_num2 < 100 {
        seed_num2 + 1                                       // nudge up
    } else if mutation_kind == 10 && seed_num2 > -100 {
        seed_num2 - 1                                       // nudge down
    } else if mutation_kind == 11 && seed_num2 >= -100 && seed_num2 <= 100 {
        -seed_num2                                          // negate
    } else if mutation_kind == 12 {
        seed_num2 / 2                                       // halve
    } else if mutation_kind == 13 {
        0                                                   // zero
    } else if mutation_kind == 14 {
        -100                                                // min boundary
    } else if mutation_kind == 15 {
        100                                                 // max boundary
    } else if mutation_kind == 16 {
        seed_num1                                           // y = x
    } else {
        seed_num2                                           // identity
    };

    (num1, num2)
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
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 17;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (12, 5),
        (-10, 4),
    ];
    for (n1, n2) in &examples {
        if count >= target_count { break; }
        if seen.insert((*n1, *n2)) {
            let result = Solution::sum(*n1, *n2);
            writeln!(out, "{}", json!({"input": {"num1": n1, "num2": n2}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seed_values: Vec<i32> = vec![
        -100, -99, -50, -10, -1, 0, 1, 10, 50, 99, 100,
    ];

    // Seed pool × mutation_kind
    for &s1 in &seed_values {
        for &s2 in &seed_values {
            for mk in 0..num_mutations {
                if count >= target_count { break; }
                let (num1, num2) = generate_test_case(s1, s2, mk);
                if seen.insert((num1, num2)) {
                    let result = Solution::sum(num1, num2);
                    writeln!(out, "{}", json!({"input": {"num1": num1, "num2": num2}, "output": result})).unwrap();
                    count += 1;
                }
            }
            if count >= target_count { break; }
        }
        if count >= target_count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let s1 = rng.gen_range_i64(-100, 100) as i32;
        let s2 = rng.gen_range_i64(-100, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (num1, num2) = generate_test_case(s1, s2, mk);
        if seen.insert((num1, num2)) {
            let result = Solution::sum(num1, num2);
            writeln!(out, "{}", json!({"input": {"num1": num1, "num2": num2}, "output": result})).unwrap();
            count += 1;
        }
    }
}
