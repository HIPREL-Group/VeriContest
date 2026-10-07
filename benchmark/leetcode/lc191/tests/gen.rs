use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed <= i32::MAX,
    ensures
        1 <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 && seed >= 1 && seed <= 1_073_741_823 {
        seed * 2
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 1 { h } else { seed }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        i32::MAX
    } else if mutation_kind == 7 {
        if seed >= 0 { seed } else { seed }
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
    let mut count = 0;
    let target = 100;
    let num_mutations: u8 = 8;

    let seeds: Vec<i32> = vec![
        1, 2, 3, 7, 11, 13, 15, 100, 255, 256, 1000, 10000, 100000, 1000000,
        1 << 1, 1 << 2, 1 << 4, 1 << 8, 1 << 15, 1 << 20, 1 << 29, 1 << 30,
        0b11, 0b111, 0b1111, 0b11111, 0b111111, 0b1111111, 0b11111111,
        0x7FFF, 0x7FFFFFFF,
        0b10101010, 0b01010101, 0x55555555, 0x2AAAAAAB,
        0x10000, 0x100, 0x10,
        i32::MAX, i32::MAX - 1,
    ];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::hamming_weight(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let s = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::hamming_weight(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }
}
