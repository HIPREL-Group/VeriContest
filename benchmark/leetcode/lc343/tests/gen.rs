use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        2i32 <= seed <= 58i32,
    ensures
        2 <= result <= 58,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 58 {
        (seed + 1) as i32                             // nudge up
    } else if mutation_kind == 2 && seed > 2 {
        (seed - 1) as i32                             // nudge down
    } else if mutation_kind == 3 {
        // mirror around midpoint 30
        let mirrored = 60 - seed;
        if mirrored >= 2 && mirrored <= 58 {
            mirrored
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        2                                             // min boundary
    } else if mutation_kind == 5 {
        58                                            // max boundary
    } else if mutation_kind == 6 {
        30                                            // midpoint
    } else if mutation_kind == 7 {
        // halve within range
        let half = seed / 2;
        if half >= 2 {
            half
        } else {
            2
        }
    } else if mutation_kind == 8 {
        // double within range
        if seed <= 29 {
            (seed * 2) as i32
        } else {
            58
        }
    } else if mutation_kind == 9 {
        // clamp to lower third
        if seed <= 20 {
            seed
        } else {
            2 + ((seed - 2) % 19)
        }
    } else {
        seed                                          // fallback
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
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
    let examples: Vec<i32> = vec![2, 10];
    for n in &examples {
        if count >= goal { break; }
        if seen.insert(*n) {
            let output = Solution::integer_break(*n);
            writeln!(out, "{}", json!({"input": {"n": *n}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: all values in range + interesting values
    let seeds: Vec<i32> = vec![
        2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 20, 25, 30, 35, 40, 45, 50, 55, 58,
        56, 57, 11, 12, 13, 14,
    ];

    for &s in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::integer_break(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts_0 = 0usize;
    while count < goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s = rng.gen_range_i32(2, 58);
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::integer_break(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
