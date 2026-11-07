use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_rows: i32,
    seed_cols: i32,
    r_frac: i32,
    c_frac: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32, i32))
    requires
        1 <= seed_rows <= 100,
        1 <= seed_cols <= 100,
        0 <= r_frac <= 99,
        0 <= c_frac <= 99,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
        0 <= res.2 < res.0,
        0 <= res.3 < res.1,
{
    let rows: i32;
    let cols: i32;
    let r_start: i32;
    let c_start: i32;

    if mutation_kind == 0 {
        // Identity
        rows = seed_rows;
        cols = seed_cols;
        r_start = r_frac % seed_rows;
        c_start = c_frac % seed_cols;
    } else if mutation_kind == 1 {
        // Minimum grid
        rows = 1;
        cols = 1;
        r_start = 0;
        c_start = 0;
    } else if mutation_kind == 2 {
        // Maximum grid
        rows = 100;
        cols = 100;
        r_start = r_frac;
        c_start = c_frac;
    } else if mutation_kind == 3 {
        // Start at origin
        rows = seed_rows;
        cols = seed_cols;
        r_start = 0;
        c_start = 0;
    } else if mutation_kind == 4 {
        // Start at bottom-right corner
        rows = seed_rows;
        cols = seed_cols;
        r_start = seed_rows - 1;
        c_start = seed_cols - 1;
    } else if mutation_kind == 5 {
        // Start at top-right corner
        rows = seed_rows;
        cols = seed_cols;
        r_start = 0;
        c_start = seed_cols - 1;
    } else if mutation_kind == 6 {
        // Start at bottom-left corner
        rows = seed_rows;
        cols = seed_cols;
        r_start = seed_rows - 1;
        c_start = 0;
    } else if mutation_kind == 7 {
        // Single row
        rows = 1;
        cols = seed_cols;
        r_start = 0;
        c_start = c_frac % seed_cols;
    } else if mutation_kind == 8 {
        // Single column
        rows = seed_rows;
        cols = 1;
        r_start = r_frac % seed_rows;
        c_start = 0;
    } else if mutation_kind == 9 {
        // Square grid
        rows = seed_rows;
        cols = seed_rows;
        r_start = r_frac % seed_rows;
        c_start = c_frac % seed_rows;
    } else if mutation_kind == 10 && seed_rows >= 3 && seed_cols >= 3 {
        // Center start (approximate)
        rows = seed_rows;
        cols = seed_cols;
        r_start = seed_rows / 2;
        c_start = seed_cols / 2;
    } else if mutation_kind == 11 && seed_rows > 1 {
        // Nudge rows down by 1
        rows = seed_rows - 1;
        cols = seed_cols;
        r_start = r_frac % (seed_rows - 1);
        c_start = c_frac % seed_cols;
    } else if mutation_kind == 12 && seed_cols > 1 {
        // Nudge cols down by 1
        rows = seed_rows;
        cols = seed_cols - 1;
        r_start = r_frac % seed_rows;
        c_start = c_frac % (seed_cols - 1);
    } else if mutation_kind == 13 && seed_rows < 100 && seed_cols < 100 {
        // Nudge both up by 1
        rows = seed_rows + 1;
        cols = seed_cols + 1;
        r_start = r_frac % (seed_rows + 1);
        c_start = c_frac % (seed_cols + 1);
    } else if mutation_kind == 14 {
        // Swap rows/cols dimensions
        rows = seed_cols;
        cols = seed_rows;
        r_start = r_frac % seed_cols;
        c_start = c_frac % seed_rows;
    } else {
        // Fallback: identity
        rows = seed_rows;
        cols = seed_cols;
        r_start = r_frac % seed_rows;
        c_start = c_frac % seed_cols;
    };

    (rows, cols, r_start, c_start)
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
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let target = 200;
    let num_mutations: u8 = 15;

    // Seed pool: (rows, cols, r_frac, c_frac)
    let seeds: Vec<(i32, i32, i32, i32)> = vec![
        (1, 1, 0, 0),
        (1, 4, 0, 0),
        (5, 6, 1, 4),
        (100, 100, 0, 0),
        (100, 100, 99, 99),
        (100, 100, 50, 50),
        (1, 100, 0, 50),
        (100, 1, 50, 0),
        (2, 2, 0, 0),
        (2, 2, 1, 1),
        (3, 3, 1, 1),
        (10, 10, 5, 5),
        (10, 10, 0, 9),
        (10, 10, 9, 0),
        (50, 50, 25, 25),
        (7, 13, 3, 6),
        (13, 7, 6, 3),
        (1, 2, 0, 0),
        (2, 1, 0, 0),
        (99, 100, 98, 99),
        (100, 99, 99, 98),
        (4, 5, 2, 3),
        (20, 30, 10, 15),
        (50, 100, 0, 99),
    ];

    // Seed pool × mutation_kind
    for &(sr, sc, rf, cf) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (rows, cols, r_start, c_start) = generate_test_case(sr, sc, rf, cf, mk);
            let key = (rows, cols, r_start, c_start);
            if seen.insert(key) {
                let result = Solution::spiral_matrix_iii(rows, cols, r_start, c_start);
                let result_json: Vec<Vec<i32>> = result;
                writeln!(out, "{}", json!({
                    "input": {
                        "rows": rows,
                        "cols": cols,
                        "rStart": r_start,
                        "cStart": c_start
                    },
                    "output": result_json
                })).unwrap();
                count += 1;
            }
        }
        if count >= target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sr = rng.gen_range_i64(1, 100) as i32;
        let sc = rng.gen_range_i64(1, 100) as i32;
        let rf = rng.gen_range_i64(0, 99) as i32;
        let cf = rng.gen_range_i64(0, 99) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (rows, cols, r_start, c_start) = generate_test_case(sr, sc, rf, cf, mk);
        let key = (rows, cols, r_start, c_start);
        if seen.insert(key) {
            let result = Solution::spiral_matrix_iii(rows, cols, r_start, c_start);
            let result_json: Vec<Vec<i32>> = result;
            writeln!(out, "{}", json!({
                "input": {
                    "rows": rows,
                    "cols": cols,
                    "rStart": r_start,
                    "cStart": c_start
                },
                "output": result_json
            })).unwrap();
            count += 1;
        }
    }
}
