use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_length: i32,
    seed_width: i32,
    seed_height: i32,
    seed_mass: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= seed_length <= 100000,
        1 <= seed_width <= 100000,
        1 <= seed_height <= 100000,
        1 <= seed_mass <= 1000,
    ensures
        1 <= result.0 <= 100000,
        1 <= result.1 <= 100000,
        1 <= result.2 <= 100000,
        1 <= result.3 <= 1000,
{
    let mut length = seed_length;
    let mut width = seed_width;
    let mut height = seed_height;
    let mut mass = seed_mass;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 {
        // all dimensions at boundary for bulky (>= 10000)
        length = 10000;
        width = 10000;
        height = 10000;
    } else if mutation_kind == 2 {
        // max mass (heavy)
        mass = 1000;
    } else if mutation_kind == 3 {
        // min mass (not heavy)
        mass = 1;
    } else if mutation_kind == 4 {
        // all minimums (neither)
        length = 1;
        width = 1;
        height = 1;
        mass = 1;
    } else if mutation_kind == 5 {
        // bulky + heavy (both)
        length = 100000;
        mass = 100;
    } else if mutation_kind == 6 {
        // just at heavy boundary
        mass = 100;
    } else if mutation_kind == 7 {
        // just below heavy boundary
        mass = 99;
    } else if mutation_kind == 8 {
        // max everything
        length = 100000;
        width = 100000;
        height = 100000;
        mass = 1000;
    } else if mutation_kind == 9 {
        // nudge length up (if possible)
        if seed_length < 100000 {
            length = seed_length + 1;
        }
    } else if mutation_kind == 10 {
        // nudge length down (if possible)
        if seed_length > 1 {
            length = seed_length - 1;
        }
    } else if mutation_kind == 11 {
        // nudge mass up (if possible)
        if seed_mass < 1000 {
            mass = seed_mass + 1;
        }
    } else if mutation_kind == 12 {
        // nudge mass down (if possible)
        if seed_mass > 1 {
            mass = seed_mass - 1;
        }
    } else if mutation_kind == 13 {
        // volume boundary: try to get near 10^9
        // 1000 * 1000 * 1000 = 10^9
        length = 1000;
        width = 1000;
        height = 1000;
    } else if mutation_kind == 14 {
        // just below volume boundary
        // 999 * 1000 * 1000 = 999_000_000 < 10^9
        length = 999;
        width = 1000;
        height = 1000;
    } else if mutation_kind == 15 {
        // dimension at boundary 10000
        length = 10000;
    } else if mutation_kind == 16 {
        // dimension just below boundary
        length = 9999;
    } else {
        // fallback: identity
    }

    (length, width, height, mass)
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

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32, i32)> = vec![
        (1000, 35, 700, 300),   // Example 1: "Both"
        (200, 50, 800, 50),     // Example 2: "Neither"
    ];
    for &(l, w, h, m) in &examples {
        if count >= goal { break; }
        let output = Solution::categorize_box(l, w, h, m);
        if seen.insert((l, w, h, m)) {
            writeln!(out, "{}", json!({
                "input": {"length": l, "width": w, "height": h, "mass": m},
                "output": output
            })).unwrap();
            count += 1;
        }
    }

    // Interesting seed values for dimensions and mass
    let dim_seeds: Vec<i32> = vec![
        1, 2, 10, 100, 999, 1000, 1001, 5000,
        9999, 10000, 10001, 50000, 99999, 100000,
    ];
    let mass_seeds: Vec<i32> = vec![
        1, 2, 50, 99, 100, 101, 500, 999, 1000,
    ];

    // Structured sweep: interesting seeds × mutations
    for &l in &dim_seeds {
        for &m in &mass_seeds {
            for mk in 0..=17u8 {
                if count >= goal { break; }
                let (rl, rw, rh, rm) = generate_test_case(l, l, l, m, mk);
                if seen.insert((rl, rw, rh, rm)) {
                    let output = Solution::categorize_box(rl, rw, rh, rm);
                    writeln!(out, "{}", json!({
                        "input": {"length": rl, "width": rw, "height": rh, "mass": rm},
                        "output": output
                    })).unwrap();
                    count += 1;
                }
            }
            if count >= goal { break; }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random inputs
    while count < goal {
        let l = rng.gen_range_i64(1, 100000) as i32;
        let w = rng.gen_range_i64(1, 100000) as i32;
        let h = rng.gen_range_i64(1, 100000) as i32;
        let m = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_u8() % 18;
        let (rl, rw, rh, rm) = generate_test_case(l, w, h, m, mk);
        if seen.insert((rl, rw, rh, rm)) {
            let output = Solution::categorize_box(rl, rw, rh, rm);
            writeln!(out, "{}", json!({
                "input": {"length": rl, "width": rw, "height": rh, "mass": rm},
                "output": output
            })).unwrap();
            count += 1;
        }
    }
}
