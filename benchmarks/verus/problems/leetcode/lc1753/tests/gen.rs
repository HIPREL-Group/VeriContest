use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i32,
    seed_b: i32,
    seed_c: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_a <= 100_000,
        1 <= seed_b <= 100_000,
        1 <= seed_c <= 100_000,
    ensures
        1 <= result.0 <= 100_000,
        1 <= result.1 <= 100_000,
        1 <= result.2 <= 100_000,
{
    if mutation_kind == 0 {
        // Identity
        (seed_a, seed_b, seed_c)
    } else if mutation_kind == 1 && seed_a < 100_000 {
        // Nudge a up
        (seed_a + 1, seed_b, seed_c)
    } else if mutation_kind == 2 && seed_a > 1 {
        // Nudge a down
        (seed_a - 1, seed_b, seed_c)
    } else if mutation_kind == 3 && seed_b < 100_000 {
        // Nudge b up
        (seed_a, seed_b + 1, seed_c)
    } else if mutation_kind == 4 && seed_b > 1 {
        // Nudge b down
        (seed_a, seed_b - 1, seed_c)
    } else if mutation_kind == 5 && seed_c < 100_000 {
        // Nudge c up
        (seed_a, seed_b, seed_c + 1)
    } else if mutation_kind == 6 && seed_c > 1 {
        // Nudge c down
        (seed_a, seed_b, seed_c - 1)
    } else if mutation_kind == 7 {
        // Double a (clamped)
        let a2 = if seed_a <= 50_000 { seed_a * 2 } else { 100_000 };
        (a2, seed_b, seed_c)
    } else if mutation_kind == 8 {
        // Halve a (clamped)
        let a2 = seed_a / 2;
        let a2 = if a2 < 1 { 1i32 } else { a2 };
        (a2, seed_b, seed_c)
    } else if mutation_kind == 9 {
        // All min boundary
        (1, 1, 1)
    } else if mutation_kind == 10 {
        // All max boundary
        (100_000, 100_000, 100_000)
    } else if mutation_kind == 11 {
        // Set a = b (two equal piles)
        (seed_b, seed_b, seed_c)
    } else if mutation_kind == 12 {
        // Set a = c
        (seed_c, seed_b, seed_c)
    } else if mutation_kind == 13 {
        // Set b = c
        (seed_a, seed_c, seed_c)
    } else if mutation_kind == 14 {
        // All equal
        (seed_a, seed_a, seed_a)
    } else if mutation_kind == 15 {
        // Max a, keep b,c
        (100_000, seed_b, seed_c)
    } else if mutation_kind == 16 {
        // Min a, keep b,c
        (1, seed_b, seed_c)
    } else if mutation_kind == 17 {
        // Swap a and b
        (seed_b, seed_a, seed_c)
    } else if mutation_kind == 18 {
        // Swap a and c
        (seed_c, seed_b, seed_a)
    } else if mutation_kind == 19 {
        // Swap b and c
        (seed_a, seed_c, seed_b)
    } else {
        // Fallback: identity
        (seed_a, seed_b, seed_c)
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

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 4, 6),
        (4, 4, 6),
        (1, 8, 8),
    ];

    for (a, b, c) in &examples {
        if generated >= count { break; }
        if seen.insert((*a, *b, *c)) {
            let output = Solution::maximum_score(*a, *b, *c);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Interesting seed pool for stone piles
    let interesting: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 50, 100, 500, 1000, 5000,
        10_000, 50_000, 99_999, 100_000,
    ];

    // Iterate seed pool × mutation kinds
    'outer: for &sa in &interesting {
        for &sb in &interesting {
            for &sc in &interesting {
                for mk in 0..=19u8 {
                    if generated >= count { break 'outer; }
                    let (a, b, c) = generate_test_case(sa, sb, sc, mk);
                    if seen.insert((a, b, c)) {
                        let output = Solution::maximum_score(a, b, c);
                        writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": output})).unwrap();
                        generated += 1;
                    }
                }
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while generated < count {
        let sa = rng.gen_range_i64(1, 100_000) as i32;
        let sb = rng.gen_range_i64(1, 100_000) as i32;
        let sc = rng.gen_range_i64(1, 100_000) as i32;
        let mk = rng.gen_u8() % 20;
        let (a, b, c) = generate_test_case(sa, sb, sc, mk);
        if seen.insert((a, b, c)) {
            let output = Solution::maximum_score(a, b, c);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
