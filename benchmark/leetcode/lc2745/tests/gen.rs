use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i32, seed_y: i32, seed_z: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    requires
        1 <= seed_x <= 50,
        1 <= seed_y <= 50,
        1 <= seed_z <= 50,
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 50,
        1 <= res.2 <= 50,
{
    let x: i32 = if mutation_kind == 0 {
        seed_x                                        // identity
    } else if mutation_kind == 1 && seed_x < 50 {
        seed_x + 1                                    // nudge up
    } else if mutation_kind == 2 && seed_x > 1 {
        seed_x - 1                                    // nudge down
    } else if mutation_kind == 3 && seed_x <= 25 {
        seed_x * 2                                    // double
    } else if mutation_kind == 4 {
        if seed_x / 2 >= 1 { seed_x / 2 } else { 1 } // halve
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        50                                            // max boundary
    } else if mutation_kind == 7 {
        25                                            // midpoint
    } else {
        seed_x                                        // fallback
    };

    let y: i32 = if mutation_kind == 8 && seed_y < 50 {
        seed_y + 1                                    // nudge up
    } else if mutation_kind == 9 && seed_y > 1 {
        seed_y - 1                                    // nudge down
    } else if mutation_kind == 10 {
        // set y = x for symmetry testing
        x
    } else if mutation_kind == 11 {
        1                                             // min boundary
    } else if mutation_kind == 12 {
        50                                            // max boundary
    } else {
        seed_y                                        // identity / fallback
    };

    let z: i32 = if mutation_kind == 13 && seed_z < 50 {
        seed_z + 1                                    // nudge up
    } else if mutation_kind == 14 && seed_z > 1 {
        seed_z - 1                                    // nudge down
    } else if mutation_kind == 15 {
        1                                             // min boundary
    } else if mutation_kind == 16 {
        50                                            // max boundary
    } else if mutation_kind == 17 {
        // set z = 1 (minimal AB count)
        1
    } else {
        seed_z                                        // identity / fallback
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
    let mut generated = 0;
    let num_mutations: u8 = 18;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 5, 1),
        (3, 2, 2),
    ];

    // Interesting seed triples: boundaries and special cases
    let seed_pool: Vec<(i32, i32, i32)> = vec![
        (1, 1, 1),     // all min
        (50, 50, 50),  // all max
        (1, 50, 1),    // x min, y max
        (50, 1, 1),    // x max, y min
        (25, 25, 25),  // midpoint
        (1, 1, 50),    // z max
        (50, 50, 1),   // z min
        (10, 10, 10),  // small equal
        (1, 2, 1),     // x < y by 1
        (2, 1, 1),     // x > y by 1
        (50, 49, 50),  // near max
        (49, 50, 50),  // near max
    ];

    // First emit examples
    for &(x, y, z) in examples.iter() {
        let result = Solution::longest_string(x, y, z);
        let key = (x, y, z);
        if seen.insert(key) {
            writeln!(out, "{}", json!({
                "input": {"x": x, "y": y, "z": z},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    // Then emit seed pool × mutations
    for &(sx, sy, sz) in seed_pool.iter() {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (x, y, z) = generate_test_case(sx, sy, sz, mk);
            let result = Solution::longest_string(x, y, z);
            let key = (x, y, z);
            if seen.insert(key) {
                writeln!(out, "{}", json!({
                    "input": {"x": x, "y": y, "z": z},
                    "output": result
                })).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while generated < count {
        let sx = rng.gen_range_i64(1, 50) as i32;
        let sy = rng.gen_range_i64(1, 50) as i32;
        let sz = rng.gen_range_i64(1, 50) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (x, y, z) = generate_test_case(sx, sy, sz, mk);
        let result = Solution::longest_string(x, y, z);
        let key = (x, y, z);
        if seen.insert(key) {
            writeln!(out, "{}", json!({
                "input": {"x": x, "y": y, "z": z},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
