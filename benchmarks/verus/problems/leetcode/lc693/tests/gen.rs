use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed < i32::MAX,
    ensures
        1 <= result < i32::MAX,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < i32::MAX - 1 {
        (seed + 1) as i32
    } else if mutation_kind == 2 && seed > 1 {
        (seed - 1) as i32
    } else if mutation_kind == 3 && seed <= 1_073_741_823 {
        (seed * 2) as i32
    } else if mutation_kind == 4 {
        let h: i32 = seed / 2;
        if h >= 1 { h } else { 1i32 }
    } else if mutation_kind == 5 {
        1i32
    } else if mutation_kind == 6 {
        (i32::MAX - 1) as i32
    } else if mutation_kind == 7 && seed >= 2 && seed <= 1_073_741_823 {
        (seed * 2 - 1) as i32
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![5, 7, 11];
    for &n in &examples {
        if count >= count_goal { break; }
        if seen.insert(n) {
            let output = Solution::has_alternating_bits(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: alternating-bit numbers, powers of 2, boundary values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
        // Alternating bit patterns
        0b101, 0b1010, 0b10101, 0b101010, 0b1010101, 0b10101010,
        0b101010101, 0b1010101010, 0b10101010101, 0b101010101010,
        0b1010101010101, 0b10101010101010, 0b101010101010101,
        // Near-boundary values
        i32::MAX - 1, i32::MAX - 2,
        100, 1000, 10000, 100000, 1000000,
    ];
    // Powers of 2 and neighbors
    let mut p: i64 = 1;
    while p < i32::MAX as i64 {
        let v = p as i32;
        if v >= 1 && v < i32::MAX { seeds.push(v); }
        if v > 1 { seeds.push(v - 1); }
        if v + 1 < i32::MAX { seeds.push(v + 1); }
        p *= 2;
    }

    for s in &seeds {
        for mk in 0..=8u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(*s, mk);
            if seen.insert(n) {
                let output = Solution::has_alternating_bits(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    while count < count_goal {
        let s = rng.gen_range_i64(1, (i32::MAX - 1) as i64) as i32;
        let mk = rng.gen_u8() % 9;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::has_alternating_bits(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
