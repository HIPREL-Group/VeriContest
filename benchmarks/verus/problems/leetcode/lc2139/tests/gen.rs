use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_target: i32, seed_max_doubles: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_target <= 1_000_000_000,
        0 <= seed_max_doubles <= 100,
    ensures
        1 <= res.0 <= 1_000_000_000,
        0 <= res.1 <= 100,
{
    let target = if mutation_kind == 0 {
        seed_target                                         // identity
    } else if mutation_kind == 1 && seed_target < 1_000_000_000 {
        seed_target + 1                                     // nudge up
    } else if mutation_kind == 2 && seed_target > 1 {
        seed_target - 1                                     // nudge down
    } else if mutation_kind == 3 && seed_target <= 500_000_000 {
        seed_target * 2                                     // double
    } else if mutation_kind == 4 {
        if seed_target / 2 >= 1 { seed_target / 2 } else { 1 }  // halve
    } else if mutation_kind == 5 {
        1                                                   // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000                                       // max boundary
    } else if mutation_kind == 7 {
        2                                                   // small value
    } else {
        seed_target                                         // fallback
    };

    let max_doubles = if mutation_kind == 8 && seed_max_doubles < 100 {
        seed_max_doubles + 1                                // nudge up
    } else if mutation_kind == 9 && seed_max_doubles > 0 {
        seed_max_doubles - 1                                // nudge down
    } else if mutation_kind == 10 {
        0                                                   // zero (no doubles)
    } else if mutation_kind == 11 {
        100                                                 // max boundary
    } else if mutation_kind == 12 {
        if seed_max_doubles / 2 >= 0 { seed_max_doubles / 2 } else { 0 }  // halve
    } else {
        seed_max_doubles                                    // identity
    };

    (target, max_doubles)
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
        (5, 0),
        (19, 2),
        (10, 4),
    ];
    for (t, md) in &examples {
        if count >= target_count { break; }
        let result = Solution::min_moves(*t, *md);
        writeln!(out, "{}", json!({"input": {"target": t, "maxDoubles": md}, "output": result})).unwrap();
        seen.insert((*t as i64, *md as i64));
        count += 1;
    }

    // Seed pool: diverse target values × max_doubles values
    let target_seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 8, 10, 16, 19, 32, 64, 100, 128, 255, 256,
        1000, 1024, 10000, 100000, 1_000_000, 10_000_000, 100_000_000,
        500_000_000, 999_999_999, 1_000_000_000,
    ];
    let doubles_seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 5, 10, 20, 30, 50, 100,
    ];

    // Seed pool × mutation_kind
    for &st in &target_seeds {
        for &sd in &doubles_seeds {
            for mk in 0..num_mutations {
                if count >= target_count { break; }
                let (t, md) = generate_test_case(st, sd, mk);
                if seen.insert((t as i64, md as i64)) {
                    let result = Solution::min_moves(t, md);
                    writeln!(out, "{}", json!({"input": {"target": t, "maxDoubles": md}, "output": result})).unwrap();
                    count += 1;
                }
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let st = match count % 5 {
            0 => rng.gen_range_i64(1, 10),                    // tiny
            1 => rng.gen_range_i64(1, 1000),                  // small
            2 => rng.gen_range_i64(1, 1_000_000),             // medium
            3 => rng.gen_range_i64(1, 1_000_000_000),         // large
            _ => rng.gen_range_i64(999_000_000, 1_000_000_000), // near max
        } as i32;
        let sd = rng.gen_range_i64(0, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (t, md) = generate_test_case(st, sd, mk);
        if seen.insert((t as i64, md as i64)) {
            let result = Solution::min_moves(t, md);
            writeln!(out, "{}", json!({"input": {"target": t, "maxDoubles": md}, "output": result})).unwrap();
            count += 1;
        }
    }
}
