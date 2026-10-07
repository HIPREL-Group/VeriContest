use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_presses: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        0 <= seed_presses <= 1000,
    ensures
        1 <= res.0 <= 1000,
        0 <= res.1 <= 1000,
{
    let n = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 3 && seed_n >= 1 && seed_n <= 500 {
        seed_n * 2
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h < 1 { 1i32 } else { h }
    } else if mutation_kind == 5 {
        1 // min boundary
    } else if mutation_kind == 6 {
        1000 // max boundary
    } else if mutation_kind == 7 {
        3 // interesting boundary (>= 3 is the "general" case)
    } else {
        seed_n
    };

    let presses = if mutation_kind == 8 {
        0 // zero presses
    } else if mutation_kind == 9 && seed_presses < 1000 {
        seed_presses + 1
    } else if mutation_kind == 10 && seed_presses > 0 {
        seed_presses - 1
    } else if mutation_kind == 11 {
        1 // exactly 1 press
    } else if mutation_kind == 12 {
        2 // exactly 2 presses
    } else if mutation_kind == 13 {
        1000 // max boundary
    } else if mutation_kind == 14 && seed_presses >= 0 && seed_presses <= 500 {
        seed_presses * 2
    } else if mutation_kind == 15 {
        seed_presses / 2
    } else {
        seed_presses
    };

    (n, presses)
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

    // Example inputs from description + interesting boundary seeds
    let seeds: Vec<(i32, i32)> = vec![
        // Examples from problem description
        (1, 1), (2, 1), (3, 1),
        // Boundary values for n and presses
        (1, 0), (2, 0), (3, 0),
        (1, 2), (2, 2), (3, 2),
        (1, 3), (2, 3), (3, 3),
        // Edge cases
        (1, 1000), (2, 1000), (3, 1000), (1000, 1000),
        (1000, 0), (1000, 1), (1000, 2), (1000, 3),
        // Interesting n values near boundaries
        (4, 1), (4, 2), (4, 3), (5, 1), (10, 5),
        (100, 100), (500, 500),
    ];

    // Seed pool × mutation_kind
    for &(sn, sp) in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let (n, presses) = generate_test_case(sn, sp, mk);
            if seen.insert((n, presses)) {
                let result = Solution::flip_lights(n, presses);
                writeln!(out, "{}", json!({"input": {"n": n, "presses": presses}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sp = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, presses) = generate_test_case(sn, sp, mk);
        if seen.insert((n, presses)) {
            let result = Solution::flip_lights(n, presses);
            writeln!(out, "{}", json!({"input": {"n": n, "presses": presses}, "output": result})).unwrap();
            count += 1;
        }
    }
}
