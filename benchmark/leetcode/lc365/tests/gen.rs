use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_x: i32,
    seed_y: i32,
    seed_target: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32))
    requires
        1 <= seed_x <= 1000,
        1 <= seed_y <= 1000,
        1 <= seed_target <= 1000,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
        1 <= res.2 <= 1000,
{
    let x: i32 = if mutation_kind == 0 {
        seed_x                                          // identity
    } else if mutation_kind == 1 && seed_x < 1000 {
        seed_x + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_x > 1 {
        seed_x - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_x <= 500 {
        seed_x * 2                                      // double
    } else if mutation_kind == 4 {
        if seed_x / 2 >= 1 { seed_x / 2 } else { 1 }   // halve
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        1000                                            // max boundary
    } else {
        seed_x
    };

    let y: i32 = if mutation_kind == 7 && seed_y < 1000 {
        seed_y + 1                                      // nudge up
    } else if mutation_kind == 8 && seed_y > 1 {
        seed_y - 1                                      // nudge down
    } else if mutation_kind == 9 && seed_y <= 500 {
        seed_y * 2                                      // double
    } else if mutation_kind == 10 {
        if seed_y / 2 >= 1 { seed_y / 2 } else { 1 }   // halve
    } else if mutation_kind == 11 {
        seed_x                                          // y = x (same capacity)
    } else if mutation_kind == 12 {
        1                                               // min boundary
    } else if mutation_kind == 13 {
        1000                                            // max boundary
    } else {
        seed_y
    };

    let target: i32 = if mutation_kind == 14 && seed_target < 1000 {
        seed_target + 1                                 // nudge up
    } else if mutation_kind == 15 && seed_target > 1 {
        seed_target - 1                                 // nudge down
    } else if mutation_kind == 16 {
        1                                               // min boundary
    } else if mutation_kind == 17 {
        1000                                            // max boundary
    } else if mutation_kind == 18 {
        // target = x + y (max measurable), clamped to 1000
        if seed_x + seed_y <= 1000 {
            seed_x + seed_y
        } else {
            1000
        }
    } else if mutation_kind == 19 {
        seed_x                                          // target = x
    } else if mutation_kind == 20 {
        seed_y                                          // target = y
    } else {
        seed_target
    };

    (x, y, target)
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 21;

    // Seed pool: examples from description + interesting cases
    let seeds: Vec<(i32, i32, i32)> = vec![
        // Examples from description
        (3, 5, 4),
        (2, 6, 5),
        (1, 2, 3),
        // Boundary cases
        (1, 1, 1),
        (1, 1, 2),
        (1000, 1000, 1000),
        (1000, 1000, 1),
        (1, 1000, 1),
        (1000, 1, 1),
        (1, 1000, 1000),
        // GCD-interesting cases
        (6, 10, 4),    // gcd=2, target divisible
        (6, 10, 3),    // gcd=2, target not divisible
        (7, 11, 1),    // coprime
        (100, 200, 50),
        (12, 8, 4),    // gcd=4
        (15, 25, 10),  // gcd=5
        (500, 500, 500),
        (2, 3, 5),     // target = x + y
        (3, 7, 10),    // target = x + y
        (4, 6, 2),     // gcd=2
        (9, 6, 3),     // gcd=3
        (100, 75, 25), // gcd=25
        (1, 1, 1),     // smallest valid
    ];

    // Seed pool × mutation_kind
    for &(sx, sy, st) in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let (x, y, target) = generate_test_case(sx, sy, st, mk);
            if seen.insert((x, y, target)) {
                let result = Solution::can_measure_water(x, y, target);
                writeln!(out, "{}", json!({
                    "input": {"x": x, "y": y, "target": target},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let sx = rng.gen_range_i64(1, 1000) as i32;
        let sy = rng.gen_range_i64(1, 1000) as i32;
        let st = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (x, y, target) = generate_test_case(sx, sy, st, mk);
        if seen.insert((x, y, target)) {
            let result = Solution::can_measure_water(x, y, target);
            writeln!(out, "{}", json!({
                "input": {"x": x, "y": y, "target": target},
                "output": result
            })).unwrap();
            count += 1;
        }
    }
}
