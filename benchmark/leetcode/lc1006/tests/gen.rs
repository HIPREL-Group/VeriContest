use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 10000,
    ensures
        1 <= result <= 10000,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 10000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (clamped)
        if seed <= 5000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        10000
    } else if mutation_kind == 7 {
        // mid value
        5000
    } else if mutation_kind == 8 {
        // quarter
        let q = seed / 4;
        if q >= 1 { q } else { 1 }
    } else if mutation_kind == 9 {
        // complement: 10001 - seed
        10001 - seed
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
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, seen: &mut HashSet<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target || !seen.insert(n) {
            return;
        }
        let output = Solution::clumsy(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    emit(4, &mut seen, &mut out, &mut count);   // Output: 7
    emit(10, &mut seen, &mut out, &mut count);  // Output: 12

    // Seed pool: boundary values and interesting points
    let seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        100, 500, 1000, 2500, 5000, 7500, 9999, 10000,
        11, 12, 13, 14, 15, 16, 20, 50,
    ];

    // Apply every mutation to every seed
    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_target { break; }
            let n = generate_test_case(s, mk);
            emit(n, &mut seen, &mut out, &mut count);
        }
        if count >= count_target { break; }
    }

    // Random seeds with random mutations
    while count < count_target {
        let s = rng.gen_range_i64(1, 10000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        emit(n, &mut seen, &mut out, &mut count);
    }
}
