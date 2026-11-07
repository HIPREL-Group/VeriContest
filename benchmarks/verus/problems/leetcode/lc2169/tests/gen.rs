use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, mutation_kind: u8) -> (res: (i32, i32))
    ensures
        0 <= res.0 <= 100000,
        0 <= res.1 <= 100000,
{
    let seed_a = if seed_a < 0 { 0 } else if seed_a > 100000 { 100000 } else { seed_a };
    let seed_b = if seed_b < 0 { 0 } else if seed_b > 100000 { 100000 } else { seed_b };
    let (a, b) = if mutation_kind == 0 {
        (seed_a, seed_b)
    } else if mutation_kind == 1 && seed_a > 0 {
        (seed_a - 1, seed_b)
    } else if mutation_kind == 2 && seed_b > 0 {
        (seed_a, seed_b - 1)
    } else if mutation_kind == 3 && seed_a + seed_b < 200000 {
        (seed_a + 1, seed_b)
    } else if mutation_kind == 4 && seed_a + seed_b < 200000 {
        (seed_a, seed_b + 1)
    } else if mutation_kind == 5 {
        (0i32, seed_b)
    } else if mutation_kind == 6 {
        (seed_a, 0i32)
    } else if mutation_kind == 7 {
        (0i32, 0i32)
    } else if mutation_kind == 8 {
        (seed_b, seed_a)
    } else if mutation_kind == 9 {
        (seed_a / 2, seed_b)
    } else if mutation_kind == 10 {
        (seed_a, seed_b / 2)
    } else if mutation_kind == 11 && seed_a <= 100000 {
        (seed_a, seed_a)
    } else if mutation_kind == 12 && seed_a + seed_a + seed_b <= 200000 {
        (seed_a * 2, seed_b)
    } else if mutation_kind == 13 {
        let total = seed_a + seed_b;
        (total, 0i32)
    } else if mutation_kind == 14 {
        let total = seed_a + seed_b;
        (0i32, total)
    } else {
        (seed_a, seed_b)
    };
    (if a > 100000 { 100000 } else { a }, if b > 100000 { 100000 } else { b })
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 15;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (2, 3),   // Example 1: output 3
        (10, 10), // Example 2: output 1
    ];
    for &(a, b) in &examples {
        if count >= goal { break; }
        if seen.insert((a, b)) {
            let output = Solution::count_operations(a, b);
            writeln!(out, "{}", json!({"input": {"num1": a, "num2": b}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (0, 0), (0, 1), (1, 0), (1, 1),
        (0, 100000), (100000, 0), (100000, 100000),
        (1, 100000), (100000, 1),
        (3, 2), (5, 7), (7, 5),
        (100, 100), (1000, 1000),
        (1, 2), (2, 1), (1, 3), (3, 1),
        (99999, 1), (1, 99999),
        (50000, 50000), (50000, 100000), (100000, 50000),
        (12345, 67890), (67890, 12345),
        (0, 200000), (200000, 0),
        (1, 199999), (199999, 1),
    ];

    for &(sa, sb) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (a, b) = generate_test_case(sa, sb, mk);
            if seen.insert((a, b)) {
                let output = Solution::count_operations(a, b);
                writeln!(out, "{}", json!({"input": {"num1": a, "num2": b}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let total = rng.gen_range_i64(0, 200000);
        let a = rng.gen_range_i64(0, total);
        let b = total - a;
        let sa = a as i32;
        let sb = b as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (num1, num2) = generate_test_case(sa, sb, mk);
        if seen.insert((num1, num2)) {
            let output = Solution::count_operations(num1, num2);
            writeln!(out, "{}", json!({"input": {"num1": num1, "num2": num2}, "output": output})).unwrap();
            count += 1;
        }
    }
}
