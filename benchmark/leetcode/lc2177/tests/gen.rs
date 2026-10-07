use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        0i64 <= seed <= 1000000000000000i64,
    ensures
        0 <= result <= 1000000000000000,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1000000000000000i64 {
        seed + 1
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1
    } else if mutation_kind == 3 {
        // Round down to nearest multiple of 3
        seed - seed % 3
    } else if mutation_kind == 4 {
        // Round up to nearest multiple of 3 (if in range)
        let rem = seed % 3;
        if rem == 0 {
            seed
        } else {
            let candidate = seed + (3 - rem);
            if candidate <= 1000000000000000i64 {
                candidate
            } else {
                seed - rem
            }
        }
    } else if mutation_kind == 5 {
        // Ensure not divisible by 3: add 1 to nearest multiple of 3
        let base = seed - seed % 3;
        if base + 1 <= 1000000000000000i64 {
            base + 1
        } else {
            seed
        }
    } else if mutation_kind == 6 {
        seed / 2
    } else if mutation_kind == 7 {
        0
    } else if mutation_kind == 8 {
        1000000000000000i64
    } else if mutation_kind == 9 {
        // Halve and make divisible by 3
        let half = seed / 2;
        half - half % 3
    } else {
        seed
    }
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
    let mut emitted = 0usize;

    // Example inputs from description.md
    let examples: Vec<i64> = vec![33, 4];

    // Seed pool: interesting values for this problem
    let mut seeds: Vec<i64> = vec![
        0, 1, 2, 3, 4, 5, 6, 9, 10, 33,
        99, 100, 999999999999999, 1000000000000000,
        999999999999998, 999999999999997,
        // Multiples of 3
        3, 6, 12, 21, 42, 99, 300, 999, 3000, 999999,
        333333333333333, 666666666666666,
        // Non-multiples of 3
        1, 2, 4, 5, 7, 8, 10, 11, 100, 101,
    ];

    // Emit example inputs first
    for &num in &examples {
        if seen.insert(num) {
            let result = Solution::sum_of_three(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": result})).unwrap();
            emitted += 1;
        }
    }

    // Emit seed pool × mutation kinds
    for &s in &seeds.clone() {
        for mk in 0u8..10 {
            if emitted >= count { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let result = Solution::sum_of_three(num);
                writeln!(out, "{}", json!({"input": {"num": num}, "output": result})).unwrap();
                emitted += 1;
            }
        }
        if emitted >= count { break; }
    }

    // Fill remaining with random values
    while emitted < count {
        let s = rng.gen_range_i64(0, 1000000000000000);
        let mk = rng.gen_u8() % 10;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let result = Solution::sum_of_three(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": result})).unwrap();
            emitted += 1;
        }
    }
}
