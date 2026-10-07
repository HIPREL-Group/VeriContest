use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i32, seed_y: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_x <= 100,
        1 <= seed_y <= 100,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
{
    let x = if mutation_kind == 0 {
        seed_x                                          // identity
    } else if mutation_kind == 1 && seed_x < 100 {
        seed_x + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_x > 1 {
        seed_x - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_x >= 1 && seed_x <= 50 {
        seed_x * 2                                      // double
    } else if mutation_kind == 4 {
        if seed_x >= 2 {
            seed_x / 2 + if seed_x / 2 < 1 { 1 } else { 0 }
        } else {
            seed_x                                      // halve (clamped)
        }
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        100                                             // max boundary
    } else {
        seed_x                                          // fallback
    };

    let y = if mutation_kind == 7 && seed_y < 100 {
        seed_y + 1                                      // nudge up
    } else if mutation_kind == 8 && seed_y > 1 {
        seed_y - 1                                      // nudge down
    } else if mutation_kind == 9 && seed_y >= 1 && seed_y <= 50 {
        seed_y * 2                                      // double
    } else if mutation_kind == 10 {
        1                                               // min boundary
    } else if mutation_kind == 11 {
        100                                             // max boundary
    } else if mutation_kind == 12 {
        // set y = 4*x to test exact threshold
        if x >= 1 && x <= 25 {
            x * 4
        } else {
            seed_y
        }
    } else if mutation_kind == 13 {
        // set y = 4*x + 1 (just above threshold)
        if x >= 1 && x <= 24 {
            x * 4 + 1
        } else {
            seed_y
        }
    } else if mutation_kind == 14 {
        // set y = 4*x - 1 (just below threshold for x rounds)
        if x >= 1 && x <= 25 && x * 4 - 1 >= 1 {
            x * 4 - 1
        } else {
            seed_y
        }
    } else {
        seed_y                                          // fallback
    };

    (x, y)
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
    let num_mutations: u8 = 15;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (2, 7),
        (4, 11),
    ];
    for (x, y) in &examples {
        if count >= target_count { break; }
        if seen.insert((*x as i64, *y as i64)) {
            let result = Solution::winning_player(*x, *y);
            writeln!(out, "{}", json!({"input": {"x": x, "y": y}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Curated seed pool covering boundaries and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 4), (1, 5), (1, 100),
        (100, 100), (100, 1), (50, 50),
        (1, 3), (1, 8), (2, 8), (2, 7),
        (3, 12), (3, 11), (3, 13),
        (5, 20), (5, 19), (5, 21),
        (10, 40), (10, 39), (10, 41),
        (25, 100), (25, 99), (24, 97),
        (50, 100), (100, 4), (1, 2),
    ];

    // Seed pool × mutation_kind
    for &(sx, sy) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (x, y) = generate_test_case(sx, sy, mk);
            if seen.insert((x as i64, y as i64)) {
                let result = Solution::winning_player(x, y);
                writeln!(out, "{}", json!({"input": {"x": x, "y": y}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sx = rng.gen_range_i64(1, 100) as i32;
        let sy = rng.gen_range_i64(1, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (x, y) = generate_test_case(sx, sy, mk);
        if seen.insert((x as i64, y as i64)) {
            let result = Solution::winning_player(x, y);
            writeln!(out, "{}", json!({"input": {"x": x, "y": y}, "output": result})).unwrap();
            count += 1;
        }
    }
}
