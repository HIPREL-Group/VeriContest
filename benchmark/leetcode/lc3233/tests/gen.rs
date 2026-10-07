use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_l: i32, seed_r: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_l <= 1000000000,
        1 <= seed_r <= 1000000000,
        seed_l <= seed_r,
    ensures
        1 <= result.0 <= result.1 <= 1000000000,
{
    let l = seed_l;
    let r = seed_r;
    if mutation_kind == 0 {
        // identity
        (l, r)
    } else if mutation_kind == 1 {
        // shrink range: l = r (single element)
        (l, l)
    } else if mutation_kind == 2 {
        // shrink range: r = l (single element from r side)
        (r, r)
    } else if mutation_kind == 3 && l < r {
        // nudge l up
        (l + 1, r)
    } else if mutation_kind == 4 && l < r {
        // nudge r down
        (l, r - 1)
    } else if mutation_kind == 5 {
        // set l to 1 (minimum boundary)
        (1, r)
    } else if mutation_kind == 6 {
        // set r to 1000000000 (maximum boundary)
        (l, 1000000000)
    } else if mutation_kind == 7 {
        // full range
        (1, 1000000000)
    } else if mutation_kind == 8 {
        // midpoint collapse
        let mid = l + (r - l) / 2;
        (mid, mid)
    } else if mutation_kind == 9 {
        // narrow range around l
        let new_r = if l <= 999999999 {
            l + 1
        } else {
            l
        };
        (l, new_r)
    } else if mutation_kind == 10 {
        // narrow range around r
        let new_l = if r >= 2 {
            r - 1
        } else {
            r
        };
        (new_l, r)
    } else if mutation_kind == 11 {
        // halve l
        let new_l = l / 2;
        let new_l = if new_l < 1 { 1i32 } else { new_l };
        (new_l, r)
    } else if mutation_kind == 12 {
        // double r (clamped)
        let new_r = if r <= 500000000 {
            r * 2
        } else {
            1000000000i32
        };
        (l, new_r)
    } else {
        // fallback: identity
        (l, r)
    }
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example test cases from description.md
    let examples: Vec<(i32, i32)> = vec![
        (5, 7),
        (4, 16),
    ];

    for (l, r) in &examples {
        let result = Solution::non_special_count(*l, *r);
        if seen.insert((*l, *r)) {
            writeln!(out, "{}", json!({
                "input": {"l": l, "r": r},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    // Interesting seed pairs for boundary testing
    let boundary_pairs: Vec<(i32, i32)> = vec![
        (1, 1),
        (1, 2),
        (1, 1000000000),
        (1000000000, 1000000000),
        (999999999, 1000000000),
        (1, 100),
        (1, 4),
        (4, 4),
        (9, 9),
        (25, 25),
        (4, 9),
        (1, 10000),
        (100, 1000),
        (1000, 10000),
        (10000, 100000),
        (100000, 1000000),
        (1000000, 10000000),
        (500000000, 1000000000),
    ];

    for (l, r) in &boundary_pairs {
        if generated >= count { break; }
        for mk in 0u8..=12 {
            if generated >= count { break; }
            let (gl, gr) = generate_test_case(*l, *r, mk);
            if seen.insert((gl, gr)) {
                let result = Solution::non_special_count(gl, gr);
                writeln!(out, "{}", json!({
                    "input": {"l": gl, "r": gr},
                    "output": result
                })).unwrap();
                generated += 1;
            }
        }
    }

    // Random test cases with size classes
    while generated < count {
        // Generate l and r with diverse ranges
        let (raw_l, raw_r) = match generated % 5 {
            0 => {
                // tiny range
                let l = rng.gen_range_i64(1, 1000000000) as i32;
                let r = l.saturating_add(rng.gen_range_i64(0, 10) as i32).min(1000000000);
                (l, r)
            },
            1 => {
                // small range
                let l = rng.gen_range_i64(1, 1000000000) as i32;
                let r = l.saturating_add(rng.gen_range_i64(0, 100) as i32).min(1000000000);
                (l, r)
            },
            2 => {
                // medium range
                let l = rng.gen_range_i64(1, 999999000) as i32;
                let r = l.saturating_add(rng.gen_range_i64(100, 10000) as i32).min(1000000000);
                (l, r)
            },
            3 => {
                // large range
                let l = rng.gen_range_i64(1, 999000000) as i32;
                let r = l.saturating_add(rng.gen_range_i64(10000, 1000000) as i32).min(1000000000);
                (l, r)
            },
            _ => {
                // full random range
                let a = rng.gen_range_i64(1, 1000000000) as i32;
                let b = rng.gen_range_i64(1, 1000000000) as i32;
                (a.min(b), a.max(b))
            },
        };

        let mutation_kind = rng.gen_u8() % 13;
        let (gl, gr) = generate_test_case(raw_l, raw_r, mutation_kind);

        if seen.insert((gl, gr)) {
            let result = Solution::non_special_count(gl, gr);
            writeln!(out, "{}", json!({
                "input": {"l": gl, "r": gr},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
