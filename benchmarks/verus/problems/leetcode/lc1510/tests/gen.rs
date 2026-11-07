use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 100000i32,
    ensures
        1i32 <= result <= 100000i32,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 100000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2                                      // halve
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        100000                                            // max boundary
    } else if mutation_kind == 7 {
        100001 - seed                                     // complement
    } else if mutation_kind == 8 {
        // clamp to small range for dense coverage
        if seed <= 100 {
            seed
        } else {
            (seed % 100) + 1
        }
    } else if mutation_kind == 9 {
        // mid-range
        50000
    } else {
        seed                                              // fallback
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
    let examples: Vec<i32> = vec![1, 2, 4];

    for &n in &examples {
        if count >= count_goal { break; }
        if seen.insert(n) {
            let output = Solution::winner_square_game(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Interesting seed pool: perfect squares, near-squares, boundaries
    let mut seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 16, 17, 24, 25, 26, 35, 36, 37,
        48, 49, 50, 63, 64, 65, 80, 81, 82,
        99, 100, 101, 143, 144, 145,
        224, 225, 226, 288, 289, 290,
        400, 500, 625, 900, 961, 1000,
        2500, 5000, 10000, 50000,
        99999, 99998, 100000,
    ];
    // Perfect squares up to 100000
    let mut k = 1i32;
    while k * k <= 100000 {
        seeds.push(k * k);
        if k * k > 1 { seeds.push(k * k - 1); }
        if k * k < 100000 { seeds.push(k * k + 1); }
        k += 1;
    }

    for &s in &seeds {
        if s < 1 || s > 100000 { continue; }
        for mk in 0..=10u8 {
            if count >= count_goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::winner_square_game(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    while count < count_goal {
        let s = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,           // tiny
            1 => rng.gen_range_i64(1, 100) as i32,          // small
            2 => rng.gen_range_i64(101, 1000) as i32,       // medium
            3 => rng.gen_range_i64(1001, 50000) as i32,     // large
            _ => rng.gen_range_i64(50001, 100000) as i32,   // max
        };
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::winner_square_game(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
