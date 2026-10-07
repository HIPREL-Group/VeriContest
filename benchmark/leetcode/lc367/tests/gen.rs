use vstd::arithmetic::power::pow;
use vstd::prelude::*;

verus! {

pub open spec fn spec_is_perfect_square(num: int) -> bool {
    exists|k: nat| pow(k as int, 2) == num
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= i32::MAX,
    ensures
        1 <= result <= i32::MAX,

{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed >= 1 && seed <= 1_073_741_823 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2 + 1
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        i32::MAX
    } else if mutation_kind == 7 {
        if seed >= 1 {
            seed
        } else {
            1
        }
    } else if mutation_kind == 8 {
        4
    } else if mutation_kind == 9 {
        16
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

    // Seed pool: perfect squares, near-squares, boundaries, and interesting values
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17,
        24, 25, 26, 35, 36, 37, 48, 49, 50,
        99, 100, 101, 120, 121, 122,
        143, 144, 145, 168, 169, 170,
        255, 256, 257, 624, 625, 626,
        999, 1000, 1024, 2048, 4096,
        10000, 10001, 40000, 40001,
        1000000, 1048576,
        2_147_395_600, // 46340^2
        i32::MAX, i32::MAX - 1,
    ];
    // Add perfect squares: k^2 for various k
    for k in [1i64, 2, 3, 4, 5, 10, 100, 1000, 10000, 46340] {
        let sq = k * k;
        if sq >= 1 && sq <= i32::MAX as i64 {
            seeds.push(sq as i32);
            if sq > 1 { seeds.push((sq - 1) as i32); }
            if sq + 1 <= i32::MAX as i64 { seeds.push((sq + 1) as i32); }
        }
    }

    for &s in &seeds {
        if s < 1 { continue; }
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::is_perfect_square(n);
                writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,
            1 => rng.gen_range_i64(1, 1000) as i32,
            2 => rng.gen_range_i64(1000, 1_000_000) as i32,
            3 => rng.gen_range_i64(1_000_000, 1_000_000_000) as i32,
            _ => rng.gen_range_i64(1, i32::MAX as i64) as i32,
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::is_perfect_square(n);
            writeln!(out, "{}", json!({"input": {"num": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
