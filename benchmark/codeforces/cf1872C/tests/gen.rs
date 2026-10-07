use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_l: i32, seed_r: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_l <= 10_000_000,
        seed_l <= seed_r,
        seed_r <= 10_000_000,
    ensures
        result.0 >= 1,
        result.0 <= result.1,
        result.1 <= 10_000_000,
        1 <= (result.0 as int) <= (result.1 as int) <= 10_000_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_l, seed_r)
    } else if mutation_kind == 1 && seed_l < seed_r {
        // nudge l up (shrink range from left)
        (seed_l + 1, seed_r)
    } else if mutation_kind == 2 && seed_l < seed_r {
        // nudge r down (shrink range from right)
        (seed_l, seed_r - 1)
    } else if mutation_kind == 3 {
        // set l = r (single-point range)
        (seed_r, seed_r)
    } else if mutation_kind == 4 {
        // set l = 1 (minimum boundary)
        (1, seed_r)
    } else if mutation_kind == 5 {
        // set r = 10_000_000 (maximum boundary)
        (seed_l, 10_000_000)
    } else if mutation_kind == 6 {
        // both boundaries: l=1, r=10_000_000
        (1, 10_000_000)
    } else if mutation_kind == 7 && seed_l > 1 {
        // nudge l down (expand range from left)
        (seed_l - 1, seed_r)
    } else if mutation_kind == 8 && seed_r < 10_000_000 {
        // nudge r up (expand range from right)
        (seed_l, seed_r + 1)
    } else if mutation_kind == 9 {
        // set l = r = 1 (minimum single-point)
        (1, 1)
    } else if mutation_kind == 10 {
        // set l = r = 10_000_000 (maximum single-point)
        (10_000_000, 10_000_000)
    } else if mutation_kind == 11 {
        // halve the range: l stays, r = l + (r - l) / 2
        let mid = seed_l + (seed_r - seed_l) / 2;
        (seed_l, mid)
    } else {
        // fallback: identity
        (seed_l, seed_r)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let mut count: usize = 0;

    use std::io::Write;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut emit = |l: i32, r: i32, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let result = Solution::non_coprime_split(l, r);
        let output = match result {
            Some((a, b)) => json!([a, b]),
            None => json!(null),
        };
        writeln!(out, "{}", json!({
            "input": {"l": l, "r": r},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (11, 15),
        (1, 3),
        (18, 19),
        (41, 43),
        (777, 777),
        (8000000, 10000000),
        (2000, 2023),
        (1, 1),
        (1, 4),
        (2, 3),
        (9840769, 9840769),
    ];

    for &(l, r) in &examples {
        let (gl, gr) = generate_test_case(l, r, 0);
        emit(gl, gr, &mut out, &mut count);
    }

    // Hand-crafted seeds covering edge cases
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1),                       // minimal single
        (1, 2),                       // minimal range
        (1, 3),                       // small: no solution possible
        (1, 4),                       // first range with solution (4=2+2)
        (4, 4),                       // exact single point with solution
        (2, 3),                       // tiny range, no solution
        (3, 3),                       // prime single point
        (1, 10_000_000),              // full range
        (10_000_000, 10_000_000),     // max single point
        (9_999_999, 10_000_000),      // near max range
        (5_000_000, 5_000_000),       // mid single point
        (100, 200),                   // small range
        (999, 1001),                  // around 1000
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    for &(l, r) in &seeds {
        for &mk in &mutation_kinds {
            let (gl, gr) = generate_test_case(l, r, mk);
            emit(gl, gr, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds across size classes
    while count < target_count {
        let (l, r) = match count % 5 {
            0 => {
                // tiny range
                let l = rng.gen_range_i64(1, 10) as i32;
                let r = rng.gen_range_i64(l as i64, (l as i64 + 5).min(10_000_000)) as i32;
                (l, r)
            }
            1 => {
                // small range
                let l = rng.gen_range_i64(1, 100) as i32;
                let r = rng.gen_range_i64(l as i64, (l as i64 + 100).min(10_000_000)) as i32;
                (l, r)
            }
            2 => {
                // medium range
                let l = rng.gen_range_i64(1, 10_000) as i32;
                let r = rng.gen_range_i64(l as i64, (l as i64 + 10_000).min(10_000_000)) as i32;
                (l, r)
            }
            3 => {
                // large range
                let l = rng.gen_range_i64(1, 1_000_000) as i32;
                let r = rng.gen_range_i64(l as i64, 10_000_000) as i32;
                (l, r)
            }
            _ => {
                // single point
                let v = rng.gen_range_i64(1, 10_000_000) as i32;
                (v, v)
            }
        };
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (gl, gr) = generate_test_case(l, r, mk);
        emit(gl, gr, &mut out, &mut count);
    }
}
