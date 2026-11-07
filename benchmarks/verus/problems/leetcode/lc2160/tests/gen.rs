use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1000i32 <= seed <= 9999i32,
    ensures
        1000i32 <= result <= 9999i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 9999 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1000 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // min boundary
        1000
    } else if mutation_kind == 4 {
        // max boundary
        9999
    } else if mutation_kind == 5 {
        // midpoint
        5500
    } else if mutation_kind == 6 && seed <= 4999 {
        // double (clamped to range)
        seed * 2
    } else if mutation_kind == 7 {
        // halve within range: seed/2 may be < 1000, clamp
        let h = seed / 2;
        if h >= 1000 { h } else { 1000 }
    } else if mutation_kind == 8 {
        // mirror around midpoint 5500
        let m = 10999 - seed;
        if m >= 1000 && m <= 9999 { m } else { seed }
    } else if mutation_kind == 9 {
        // swap outer digits: digit0 <-> digit3
        let d0 = seed / 1000;
        let d1 = (seed / 100) % 10;
        let d2 = (seed / 10) % 10;
        let d3 = seed % 10;
        let swapped = d3 * 1000 + d1 * 100 + d2 * 10 + d0;
        if swapped >= 1000 { swapped } else { seed }
    } else {
        // fallback
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

    // Seed pool: example inputs and interesting boundary values
    let seeds: Vec<i32> = vec![
        2932, 4009,                             // examples from description
        1000, 9999, 1001, 9998,                 // boundaries
        1111, 2222, 3333, 4444, 5555,           // repeated digits
        1234, 4321, 5678, 8765,                 // sequential digits
        1010, 9090, 5050, 1199, 9911,           // mixed patterns
        1999, 9001, 5000, 2500, 7500,           // spread
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let num = generate_test_case(s, mk);
            if seen.insert(num) {
                let output = Solution::minimum_sum(num);
                writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    while count < count_goal {
        let s = rng.gen_range_i64(1000, 9999) as i32;
        let mk = rng.gen_u8() % 11;
        let num = generate_test_case(s, mk);
        if seen.insert(num) {
            let output = Solution::minimum_sum(num);
            writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
            count += 1;
        }
    }
}
