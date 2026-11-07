use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000_000i32,
    ensures
        1 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 && seed >= 2 {
        seed / 2
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1_000_000_000
    } else if mutation_kind == 7 {
        2
    } else if mutation_kind == 8 && seed > 1 {
        (seed % 256) + 1
    } else if mutation_kind == 9 && seed > 1 {
        (seed % 1000) + 1
    } else if mutation_kind == 10 && seed >= 3 {
        // odd-only seed (often more representations as consecutive sums)
        if seed % 2 == 0 { seed - 1 } else { seed }
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, seen: &mut HashSet<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal || !seen.insert(n) {
            return;
        }
        if n < 1 || n > 1_000_000_000 { return; }
        let output = Solution::consecutive_numbers_sum(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
        *count += 1;
    };

    // Examples from description
    for &n in &[5i32, 9, 15] {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Seed pool: boundaries, triangular numbers, primes, powers of 2
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 21, 28, 36, 45, 55, 66,
        100, 120, 1000, 1024, 999_983, 999_999_937, 1_000_000_000, 999_999_999,
        500_000_000, 250_000_000, 100_000_000, 10_000_000, 1_000_000,
    ];
    // powers of 2
    let mut p: i64 = 1;
    while p <= 1_000_000_000 {
        seeds.push(p as i32);
        p *= 2;
    }
    // triangular numbers k*(k+1)/2 up to 10^9
    let mut k: i64 = 1;
    while k * (k + 1) / 2 <= 1_000_000_000 {
        seeds.push((k * (k + 1) / 2) as i32);
        k += 1;
        if k > 50000 { break; }
    }

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            emit(n, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        emit(n, &mut seen, &mut out, &mut count);
    }
}
