use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    ensures
        1 <= result <= 999999999,
{
    let seed = if seed < 1 { 1 } else if seed > 999999999 { 999999999 } else { seed };
    let candidate = if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 999_999_999 {
        seed + 1
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 499_999_999 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2
    } else if mutation_kind == 5 {
        0
    } else if mutation_kind == 6 {
        999_999_999
    } else if mutation_kind == 7 {
        1
    } else if mutation_kind == 8 {
        seed % 256
    } else if mutation_kind == 9 {
        seed % 1000
    } else {
        seed
    };
    if candidate < 1 { 1 } else { candidate }
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
        let output = Solution::bitwise_complement(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    for &n in &[5, 7, 10] {
        emit(generate_test_case(n, 0), &mut seen, &mut out, &mut count);
    }

    // Seed pool: boundary values, powers of 2, interesting values
    let mut seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256,
        511, 512, 1023, 1024, 999_999_999, 999_999_998, 500_000_000,
        100, 1000, 10000, 100000, 1000000, 10000000, 100000000,
    ];
    let mut p: i64 = 1;
    while p < 1_000_000_000 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
        }
        p *= 2;
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
        let s = rng.gen_range_i64(0, 999_999_998) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        emit(n, &mut seen, &mut out, &mut count);
    }
}
