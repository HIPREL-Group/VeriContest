use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_red: i32, seed_blue: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_red <= 100,
        1 <= seed_blue <= 100,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
{
    let red = if mutation_kind == 0 {
        seed_red                                              // identity
    } else if mutation_kind == 1 && seed_red < 100 {
        seed_red + 1                                          // nudge up
    } else if mutation_kind == 2 && seed_red > 1 {
        seed_red - 1                                          // nudge down
    } else if mutation_kind == 3 && seed_red >= 1 && seed_red <= 50 {
        seed_red * 2                                          // double
    } else if mutation_kind == 4 {
        let h = seed_red / 2;
        if h < 1 { 1 } else { h }                            // halve (clamped)
    } else if mutation_kind == 5 {
        1                                                     // min boundary
    } else if mutation_kind == 6 {
        100                                                   // max boundary
    } else {
        seed_red                                              // fallback
    };

    let blue = if mutation_kind == 7 && seed_blue < 100 {
        seed_blue + 1                                         // nudge up
    } else if mutation_kind == 8 && seed_blue > 1 {
        seed_blue - 1                                         // nudge down
    } else if mutation_kind == 9 {
        seed_red                                              // copy red seed
    } else if mutation_kind == 10 {
        let s = seed_red + seed_blue;
        if s > 100 { 100 } else { s }                        // sum (clamped)
    } else if mutation_kind == 11 {
        1                                                     // min boundary
    } else if mutation_kind == 12 {
        100                                                   // max boundary
    } else {
        seed_blue                                             // default
    };

    (red, blue)
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
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (2, 4),   // output 3
        (2, 1),   // output 2
        (1, 1),   // output 1
        (10, 1),  // output 2
    ];

    for &(r, b) in &examples {
        if count >= target_count { break; }
        if seen.insert((r, b)) {
            let result = Solution::max_height_of_triangle(r, b);
            writeln!(out, "{}", json!({"input": {"red": r, "blue": b}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with diverse values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 100), (100, 1), (100, 100),
        (50, 50), (1, 50), (50, 1),
        (10, 10), (20, 30), (30, 20),
        (5, 5), (99, 99), (2, 2), (3, 3),
        (1, 2), (2, 1), (10, 100), (100, 10),
        (25, 75), (75, 25), (33, 67), (67, 33),
        (48, 52), (52, 48), (90, 10), (10, 90),
    ];

    // Seed pool × mutation_kind
    for &(sr, sb) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (red, blue) = generate_test_case(sr, sb, mk);
            if seen.insert((red, blue)) {
                let result = Solution::max_height_of_triangle(red, blue);
                writeln!(out, "{}", json!({"input": {"red": red, "blue": blue}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sr = rng.gen_range_i64(1, 100) as i32;
        let sb = rng.gen_range_i64(1, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (red, blue) = generate_test_case(sr, sb, mk);
        if seen.insert((red, blue)) {
            let result = Solution::max_height_of_triangle(red, blue);
            writeln!(out, "{}", json!({"input": {"red": red, "blue": blue}, "output": result})).unwrap();
            count += 1;
        }
    }
}
