use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1000000000,
    ensures
        1 <= result <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1000000000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (clamped)
        if seed <= 500000000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (clamped to >= 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1000000000
    } else if mutation_kind == 7 {
        // quarter
        let q = seed / 4;
        if q >= 1 { q } else { 1 }
    } else if mutation_kind == 8 {
        // complement within range
        1000000001 - seed
    } else if mutation_kind == 9 {
        // clamp to middle range
        if seed < 1000 {
            1000
        } else if seed > 999000 {
            999000
        } else {
            seed
        }
    } else {
        // fallback: identity
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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

    // Example inputs from description.md
    let examples: Vec<i32> = vec![5, 1, 2];

    // Seed pool: examples, boundaries, powers of 2, interesting values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        1000000000, 999_999_999, 999_999_998,
        500000000, 100, 1000, 10_000, 100_000,
        1_000_000, 10_000_000, 100_000_000,
    ];
    for &e in &examples {
        if !seeds.contains(&e) {
            seeds.push(e);
        }
    }
    // Powers of 2
    let mut p: i64 = 1;
    while p <= 1000000000 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
        }
        if p + 1 <= 1000000000 {
            seeds.push((p + 1) as i32);
        }
        p *= 2;
    }
    // Numbers with no consecutive ones in binary (Fibonacci-related)
    for &v in &[1, 2, 4, 5, 8, 9, 10, 16, 17, 18, 20, 21, 32, 33, 34, 36, 37, 40, 41, 42] {
        if !seeds.contains(&v) {
            seeds.push(v);
        }
    }
    // Numbers with consecutive ones
    for &v in &[3, 6, 7, 11, 12, 13, 14, 15, 24, 25, 27, 28, 30, 31, 48, 63, 127, 255] {
        if !seeds.contains(&v) {
            seeds.push(v);
        }
    }

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::find_integers(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = rng.gen_range_i64(1, 1000000000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::find_integers(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
