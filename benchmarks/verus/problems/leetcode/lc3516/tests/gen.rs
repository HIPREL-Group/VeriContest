use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i32, seed_y: i32, seed_z: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    requires
        1 <= seed_x <= 100,
        1 <= seed_y <= 100,
        1 <= seed_z <= 100,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
        1 <= res.2 <= 100,
{
    let x = if mutation_kind == 0 {
        seed_x                                          // identity
    } else if mutation_kind == 1 && seed_x < 100 {
        seed_x + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_x > 1 {
        seed_x - 1                                      // nudge down
    } else if mutation_kind == 3 {
        1                                               // min boundary
    } else if mutation_kind == 4 {
        100                                             // max boundary
    } else if mutation_kind == 5 && seed_x <= 50 {
        seed_x * 2                                      // double
    } else if mutation_kind == 6 {
        (seed_x - 1) / 2 + 1                            // halve (stay >= 1)
    } else {
        seed_x                                          // fallback
    };

    let y = if mutation_kind == 7 && seed_y < 100 {
        seed_y + 1                                      // nudge up
    } else if mutation_kind == 8 && seed_y > 1 {
        seed_y - 1                                      // nudge down
    } else if mutation_kind == 9 {
        seed_x                                          // y = x (same distance possible)
    } else if mutation_kind == 10 {
        1                                               // min boundary
    } else if mutation_kind == 11 {
        100                                             // max boundary
    } else {
        seed_y                                          // identity / fallback
    };

    let z = if mutation_kind == 12 {
        seed_x                                          // z = x (distance 0 from x)
    } else if mutation_kind == 13 {
        seed_y                                          // z = y (distance 0 from y)
    } else if mutation_kind == 14 {
        1                                               // min boundary
    } else if mutation_kind == 15 {
        100                                             // max boundary
    } else {
        seed_z                                          // identity / fallback
    };

    (x, y, z)
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0;
    let num_mutations: u8 = 16;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 7, 4),
        (2, 5, 6),
        (1, 5, 3),
    ];
    for (x, y, z) in &examples {
        if emitted >= count { break; }
        if seen.insert((*x, *y, *z)) {
            let result = Solution::find_closest(*x, *y, *z);
            writeln!(out, "{}", json!({"input": {"x": x, "y": y, "z": z}, "output": result})).unwrap();
            emitted += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seeds: Vec<(i32, i32, i32)> = vec![
        (1, 1, 1), (100, 100, 100), (1, 100, 50), (100, 1, 50),
        (50, 50, 50), (1, 1, 100), (100, 100, 1), (1, 100, 1),
        (1, 100, 100), (50, 51, 50), (49, 51, 50), (1, 2, 1),
        (99, 100, 100), (1, 2, 3), (10, 20, 15), (25, 75, 50),
        (1, 99, 50), (50, 50, 1), (50, 50, 100), (33, 67, 50),
    ];

    // Seed pool × mutation_kind
    for &(sx, sy, sz) in &seeds {
        for mk in 0..num_mutations {
            if emitted >= count { break; }
            let (x, y, z) = generate_test_case(sx, sy, sz, mk);
            if seen.insert((x, y, z)) {
                let result = Solution::find_closest(x, y, z);
                writeln!(out, "{}", json!({"input": {"x": x, "y": y, "z": z}, "output": result})).unwrap();
                emitted += 1;
            }
        }
        if emitted >= count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while emitted < count {
        let sx = rng.gen_range_i64(1, 100) as i32;
        let sy = rng.gen_range_i64(1, 100) as i32;
        let sz = rng.gen_range_i64(1, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (x, y, z) = generate_test_case(sx, sy, sz, mk);
        if seen.insert((x, y, z)) {
            let result = Solution::find_closest(x, y, z);
            writeln!(out, "{}", json!({"input": {"x": x, "y": y, "z": z}, "output": result})).unwrap();
            emitted += 1;
        }
    }
}
