use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= 1_000_000i32,
    ensures
        1 <= result <= 1_000_000,
{
    if mutation_kind == 0 {
        // Identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000 {
        // Nudge +1
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // Nudge -1
        seed - 1
    } else if mutation_kind == 3 {
        // Double (clamped)
        if seed <= 500_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // Halve (at least 1)
        let h = seed / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        // Min boundary
        1
    } else if mutation_kind == 6 {
        // Max boundary
        1_000_000
    } else if mutation_kind == 7 {
        // Round down to nearest multiple of 10, clamped to [1, 1_000_000]
        let r = seed / 10 * 10;
        if r >= 1 { r } else { 1 }
    } else if mutation_kind == 8 {
        // Swap to "mirror" within range: max + min - seed
        1_000_001 - seed
    } else if mutation_kind == 9 {
        // Modular squeeze into lower range [1, 1000]
        let r = (seed - 1) % 1000 + 1;
        r
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
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let goal = 100usize;

    // Interesting seed values: boundaries, powers of 10, small values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9,
        10, 11, 23, 99, 100, 123, 256, 512, 999,
        1000, 9999, 10000, 99999, 100000, 500000,
        999999, 1_000_000,
    ];
    // Powers of 10
    let mut p: i64 = 1;
    while p <= 1_000_000 {
        seeds.push(p as i32);
        if p > 1 { seeds.push((p - 1) as i32); }
        if p < 1_000_000 { seeds.push((p + 1) as i32); }
        p *= 10;
    }
    seeds.sort();
    seeds.dedup();

    for &seed in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(seed, mk);
            if seen.insert(n) {
                let output = Solution::check_divisibility(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let seed = rng.gen_range_i64(1, 1_000_000) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(seed, mk);
        if seen.insert(n) {
            let output = Solution::check_divisibility(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
