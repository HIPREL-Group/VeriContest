use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed1: i32, seed2: i32, seed3: i32, mutation_kind: u8,
) -> (res: (i32, i32, i32))
    requires
        1 <= seed1 <= 9999,
        1 <= seed2 <= 9999,
        1 <= seed3 <= 9999,
    ensures
        1 <= res.0 <= 9999,
        1 <= res.1 <= 9999,
        1 <= res.2 <= 9999,
{
    let num1 = if mutation_kind == 0 {
        seed1                                           // identity
    } else if mutation_kind == 1 && seed1 < 9999 {
        seed1 + 1                                       // nudge up
    } else if mutation_kind == 2 && seed1 > 1 {
        seed1 - 1                                       // nudge down
    } else if mutation_kind == 3 && seed1 <= 4999 {
        seed1 * 2                                       // double
    } else if mutation_kind == 4 {
        let h = seed1 / 2;
        if h >= 1 { h } else { 1 }                     // halve
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        9999                                            // max boundary
    } else if mutation_kind == 7 {
        1000                                            // round value
    } else {
        seed1                                           // fallback
    };

    let num2 = if mutation_kind == 8 && seed2 < 9999 {
        seed2 + 1                                       // nudge up
    } else if mutation_kind == 9 && seed2 > 1 {
        seed2 - 1                                       // nudge down
    } else if mutation_kind == 10 {
        seed1                                           // copy from seed1
    } else if mutation_kind == 11 {
        1                                               // min boundary
    } else if mutation_kind == 12 {
        9999                                            // max boundary
    } else {
        seed2                                           // identity / fallback
    };

    let num3 = if mutation_kind == 13 && seed3 < 9999 {
        seed3 + 1                                       // nudge up
    } else if mutation_kind == 14 && seed3 > 1 {
        seed3 - 1                                       // nudge down
    } else if mutation_kind == 15 {
        seed1                                           // all equal
    } else if mutation_kind == 16 {
        1                                               // min boundary
    } else if mutation_kind == 17 {
        9999                                            // max boundary
    } else {
        seed3                                           // identity / fallback
    };

    (num1, num2, num3)
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 18;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (1, 10, 1000),
        (987, 879, 798),
        (1, 2, 3),
    ];

    for &(n1, n2, n3) in &examples {
        if count >= goal { break; }
        if seen.insert((n1, n2, n3)) {
            let output = Solution::generate_key(n1, n2, n3);
            writeln!(out, "{}", json!({"input": {"num1": n1, "num2": n2, "num3": n3}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seeds: Vec<(i32, i32, i32)> = vec![
        (1, 1, 1),
        (9999, 9999, 9999),
        (1, 9999, 5000),
        (9999, 1, 5000),
        (5000, 5000, 1),
        (1111, 1111, 1111),
        (1234, 5678, 9012),
        (9999, 1, 1),
        (1, 1, 9999),
        (1000, 2000, 3000),
        (100, 200, 300),
        (10, 20, 30),
        (4321, 8765, 2109),
        (5555, 5555, 5555),
        (1001, 1010, 1100),
        (9090, 909, 9009),
    ];

    // Seed pool × mutation_kind
    for &(s1, s2, s3) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (n1, n2, n3) = generate_test_case(s1, s2, s3, mk);
            if seen.insert((n1, n2, n3)) {
                let output = Solution::generate_key(n1, n2, n3);
                writeln!(out, "{}", json!({"input": {"num1": n1, "num2": n2, "num3": n3}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s1 = rng.gen_range_i64(1, 9999) as i32;
        let s2 = rng.gen_range_i64(1, 9999) as i32;
        let s3 = rng.gen_range_i64(1, 9999) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n1, n2, n3) = generate_test_case(s1, s2, s3, mk);
        if seen.insert((n1, n2, n3)) {
            let output = Solution::generate_key(n1, n2, n3);
            writeln!(out, "{}", json!({"input": {"num1": n1, "num2": n2, "num3": n3}, "output": output})).unwrap();
            count += 1;
        }
    }
}
