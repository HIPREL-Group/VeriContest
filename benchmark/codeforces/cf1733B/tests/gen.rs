use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i64,
    seed_x: i64,
    seed_y: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64))
    requires
        2 <= seed_n <= 100_000,
        0 <= seed_x < seed_n,
        0 <= seed_y < seed_n,
    ensures
        2 <= result.0 <= 100_000,
        0 <= result.1 < result.0,
        0 <= result.2 < result.0,
{
    let n = seed_n;
    let x = seed_x;
    let y = seed_y;

    if mutation_kind == 0 {
        // Identity
        (n, x, y)
    } else if mutation_kind == 1 {
        // Swap x and y
        (n, y, x)
    } else if mutation_kind == 2 {
        // Set x = 0
        (n, 0, y)
    } else if mutation_kind == 3 {
        // Set y = 0
        (n, x, 0)
    } else if mutation_kind == 4 {
        // Both zero
        (n, 0, 0)
    } else if mutation_kind == 5 && n < 100_000 {
        // Nudge n up by 1, keep x and y valid (they're < seed_n <= n+1)
        (n + 1, x, y)
    } else if mutation_kind == 6 && n > 2 {
        // Nudge n down by 1 — only if x and y still valid
        if x < n - 1 && y < n - 1 {
            (n - 1, x, y)
        } else {
            (n, x, y)
        }
    } else if mutation_kind == 7 {
        // Set x = y (both same value)
        (n, y, y)
    } else if mutation_kind == 8 {
        // Set x = n-1 (max valid)
        (n, n - 1, y)
    } else if mutation_kind == 9 {
        // Set y = n-1 (max valid)
        (n, x, n - 1)
    } else if mutation_kind == 10 {
        // Both at max
        (n, n - 1, n - 1)
    } else if mutation_kind == 11 {
        // x = 0, y = n-1 (extremes)
        (n, 0, n - 1)
    } else if mutation_kind == 12 {
        // x = n-1, y = 0 (extremes swapped)
        (n, n - 1, 0)
    } else {
        // Fallback: identity
        (n, x, y)
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn format_output(r: Option<Vec<i64>>) -> serde_json::Value {
    match r {
        None => json!(-1),
        Some(v) => json!(v),
    }
}

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

    let mutation_kinds: u8 = 13;

    let mut emit = |n: i64, x: i64, y: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, generated: &mut usize| {
        if *generated >= count { return; }
        let key = format!("{},{},{}", n, x, y);
        if !seen.insert(key) { return; }
        let output = Solution::rule_of_league(n, x, y);
        writeln!(out, "{}", json!({
            "input": {"n": n, "x": x, "y": y},
            "output": format_output(output)
        })).unwrap();
        *generated += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i64, i64, i64)> = vec![
        (5, 2, 0),
        (8, 1, 2),
        (3, 0, 0),
        (2, 0, 1),
        (6, 3, 0),
    ];

    for &(n, x, y) in &examples {
        emit(n, x, y, &mut seen, &mut out, &mut generated);
    }

    // Handcrafted interesting seeds with all mutations
    let seeds: Vec<(i64, i64, i64)> = vec![
        (2, 0, 1),    // minimal n, feasible
        (2, 1, 0),    // minimal n, feasible (swapped)
        (2, 0, 0),    // both zero, infeasible
        (2, 1, 1),    // both nonzero, infeasible
        (3, 0, 2),    // n-1 divisible by hi
        (3, 0, 1),    // n-1 divisible by 1
        (5, 0, 2),    // n-1=4 divisible by 2
        (5, 0, 4),    // n-1=4 divisible by 4
        (5, 0, 3),    // n-1=4 not divisible by 3
        (10, 0, 3),   // n-1=9 divisible by 3
        (10, 0, 9),   // n-1=9 divisible by 9
        (100, 0, 99), // larger, hi=99
        (100_000, 0, 99_999), // max n
    ];

    for &(n, x, y) in &seeds {
        for mk in 0..mutation_kinds {
            let (gn, gx, gy) = generate_test_case(n, x, y, mk);
            emit(gn, gx, gy, &mut seen, &mut out, &mut generated);
        }
    }

    // Size classes for n
    let size_classes: Vec<(i64, i64)> = vec![
        (2, 5),            // tiny
        (6, 20),           // small
        (21, 100),         // medium
        (101, 1000),       // large
        (1001, 100_000),   // max
    ];

    // Random test cases with diverse sizes and mutations
    while generated < count {
        let class = rng.gen_range_usize(0, size_classes.len() - 1);
        let (lo, hi) = size_classes[class];
        let n = rng.gen_range_i64(lo, hi);
        let x = rng.gen_range_i64(0, n - 1);
        let y = rng.gen_range_i64(0, n - 1);
        let mk = rng.gen_u8() % mutation_kinds;
        let (gn, gx, gy) = generate_test_case(n, x, y, mk);
        emit(gn, gx, gy, &mut seen, &mut out, &mut generated);
    }
}
