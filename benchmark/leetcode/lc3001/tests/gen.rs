use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: i32, b: i32, c: i32, d: i32, e: i32, f: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32, i32, i32, i32))
    requires
        1 <= a <= 8,
        1 <= b <= 8,
        1 <= c <= 8,
        1 <= d <= 8,
        1 <= e <= 8,
        1 <= f <= 8,
    ensures
        1 <= res.0 <= 8,
        1 <= res.1 <= 8,
        1 <= res.2 <= 8,
        1 <= res.3 <= 8,
        1 <= res.4 <= 8,
        1 <= res.5 <= 8,
        res.0 != res.2 || res.1 != res.3,
        res.0 != res.4 || res.1 != res.5,
        res.2 != res.4 || res.3 != res.5,
{
    // If any two pieces share a square, return a known-good configuration.
    // Collision probability is low (~5%) so diversity is preserved.
    if (a == c && b == d) || (a == e && b == f) || (c == e && d == f) {
        if mutation_kind % 3 == 0 {
            (1, 1, 2, 2, 3, 3)
        } else if mutation_kind % 3 == 1 {
            (1, 8, 8, 1, 4, 4)
        } else {
            (8, 8, 1, 1, 4, 5)
        }
    } else {
        // All three positions are distinct — apply mutations.
        // Swapping piece roles preserves distinctness.
        if mutation_kind == 0 {
            // identity
            (a, b, c, d, e, f)
        } else if mutation_kind == 1 {
            // swap rook and bishop
            (c, d, a, b, e, f)
        } else if mutation_kind == 2 {
            // swap rook and queen
            (e, f, c, d, a, b)
        } else if mutation_kind == 3 {
            // swap bishop and queen
            (a, b, e, f, c, d)
        } else {
            // fallback identity
            (a, b, c, d, e, f)
        }
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
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
    let mut total = 0;
    let num_mutations: u8 = 5;

    // Example inputs from problem description
    let examples: Vec<(i32, i32, i32, i32, i32, i32)> = vec![
        (1, 1, 8, 8, 2, 3),  // Example 1: output 2
        (5, 3, 3, 4, 5, 2),  // Example 2: output 1
    ];

    for &(a, b, c, d, e, f) in &examples {
        if total >= count { break; }
        let (ra, rb, rc, rd, re, rf) = generate_test_case(a, b, c, d, e, f, 0);
        if seen.insert((ra, rb, rc, rd, re, rf)) {
            let result = Solution::min_moves_to_capture_the_queen(ra, rb, rc, rd, re, rf);
            writeln!(out, "{}", json!({
                "input": {"a": ra, "b": rb, "c": rc, "d": rd, "e": re, "f": rf},
                "output": result
            })).unwrap();
            total += 1;
        }
    }

    // Interesting seed positions: corners, edges, center, diagonals
    let interesting: Vec<(i32, i32, i32, i32, i32, i32)> = vec![
        // Rook on same row as queen
        (3, 1, 5, 5, 3, 7),
        // Rook on same col as queen
        (2, 4, 6, 6, 7, 4),
        // Bishop on same diagonal as queen
        (5, 5, 2, 2, 6, 6),
        // Bishop on anti-diagonal with queen
        (1, 1, 3, 5, 5, 3),
        // Rook blocked by bishop
        (1, 1, 1, 4, 1, 8),
        // Bishop blocked by rook
        (4, 4, 2, 2, 6, 6),
        // All on corners
        (1, 1, 8, 8, 1, 8),
        (1, 1, 8, 8, 8, 1),
        // All on edges
        (1, 4, 4, 8, 8, 4),
        // Compact cluster
        (4, 4, 5, 5, 4, 5),
        (4, 4, 3, 3, 5, 5),
    ];

    // Interesting × mutations
    for &(a, b, c, d, e, f) in &interesting {
        for mk in 0..num_mutations {
            if total >= count { break; }
            let (ra, rb, rc, rd, re, rf) = generate_test_case(a, b, c, d, e, f, mk);
            if seen.insert((ra, rb, rc, rd, re, rf)) {
                let result = Solution::min_moves_to_capture_the_queen(ra, rb, rc, rd, re, rf);
                writeln!(out, "{}", json!({
                    "input": {"a": ra, "b": rb, "c": rc, "d": rd, "e": re, "f": rf},
                    "output": result
                })).unwrap();
                total += 1;
            }
        }
    }

    // Fill remaining with random seeds × random mutations
    let mut _attempts_0 = 0usize;
    while total < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let a = rng.gen_range_i64(1, 8) as i32;
        let b = rng.gen_range_i64(1, 8) as i32;
        let c = rng.gen_range_i64(1, 8) as i32;
        let d = rng.gen_range_i64(1, 8) as i32;
        let e = rng.gen_range_i64(1, 8) as i32;
        let f = rng.gen_range_i64(1, 8) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (ra, rb, rc, rd, re, rf) = generate_test_case(a, b, c, d, e, f, mk);
        if seen.insert((ra, rb, rc, rd, re, rf)) {
            let result = Solution::min_moves_to_capture_the_queen(ra, rb, rc, rd, re, rf);
            writeln!(out, "{}", json!({
                "input": {"a": ra, "b": rb, "c": rc, "d": rd, "e": re, "f": rf},
                "output": result
            })).unwrap();
            total += 1;
        }
    }
}
