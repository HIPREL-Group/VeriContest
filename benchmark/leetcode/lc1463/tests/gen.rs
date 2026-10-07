use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    fill_val: i32,
    alt_val: i32,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        2 <= rows <= 70,
        2 <= cols <= 70,
        0 <= fill_val <= 100,
        0 <= alt_val <= 100,
    ensures
        2 <= result.len() <= 70,
        2 <= result[0].len() <= 70,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall |i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len() ==> 0 <= #[trigger] result[i][j] <= 100,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            2 <= rows <= 70,
            2 <= cols <= 70,
            0 <= fill_val <= 100,
            0 <= alt_val <= 100,
            grid.len() == r,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len()
                    ==> 0 <= #[trigger] grid[i][j] <= 100,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                2 <= cols <= 70,
                0 <= fill_val <= 100,
                0 <= alt_val <= 100,
                0 <= r < rows,
                2 <= rows <= 70,
                row.len() == c,
                forall |j: int| 0 <= j < row.len() ==> 0 <= #[trigger] row[j] <= 100,
            decreases cols - c,
        {
            let v: i32 = if mutation_kind == 0 {
                // uniform fill
                fill_val
            } else if mutation_kind == 1 {
                // checkerboard pattern
                if (r + c) % 2 == 0 { fill_val } else { alt_val }
            } else if mutation_kind == 2 {
                // first row uses alt_val
                if r == 0 { alt_val } else { fill_val }
            } else if mutation_kind == 3 {
                // last row uses alt_val
                if r == rows - 1 { alt_val } else { fill_val }
            } else if mutation_kind == 4 {
                // diagonal cells use alt_val
                if r == c { alt_val } else { fill_val }
            } else if mutation_kind == 5 {
                // border cells use alt_val, interior uses fill_val
                if r == 0 || r == rows - 1 || c == 0 || c == cols - 1 {
                    alt_val
                } else {
                    fill_val
                }
            } else if mutation_kind == 6 {
                // corners use alt_val
                if (r == 0 || r == rows - 1) && (c == 0 || c == cols - 1) {
                    alt_val
                } else {
                    fill_val
                }
            } else if mutation_kind == 7 {
                // first column uses alt_val
                if c == 0 { alt_val } else { fill_val }
            } else {
                // fallback: uniform fill
                fill_val
            };
            row.push(v);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    assert(grid.len() == rows);
    assert(grid[0].len() == cols);
    grid
}

} // verus!

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

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", grid);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::cherry_pickup(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *count += 1;
    };

    // Example 1 from description.md
    emit(
        vec![vec![3,1,1], vec![2,5,1], vec![1,5,5], vec![2,1,1]],
        &mut seen, &mut out, &mut count,
    );

    // Example 2 from description.md
    emit(
        vec![
            vec![1,0,0,0,0,0,1],
            vec![2,0,0,0,0,3,0],
            vec![2,0,9,0,0,0,0],
            vec![0,3,0,5,4,0,0],
            vec![1,0,2,3,0,0,6],
        ],
        &mut seen, &mut out, &mut count,
    );

    // Size classes for rows and cols
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 2), (2, 3), (3, 2), (3, 3),   // tiny
        (5, 5), (4, 7), (7, 4), (10, 10), // small
        (20, 20), (15, 30), (30, 15),      // medium
        (50, 50), (40, 60), (60, 40),      // large
        (70, 70), (70, 2), (2, 70),        // max/edge
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply all mutations to various size classes with boundary fill values
    let fill_vals: Vec<(i32, i32)> = vec![
        (0, 0), (0, 100), (100, 0), (100, 100),
        (50, 50), (0, 1), (1, 0), (99, 100),
    ];

    for &(rows, cols) in &size_classes {
        for &(fv, av) in &fill_vals {
            for &mk in &mutation_kinds {
                if count >= count_target { break; }
                let grid = generate_test_case(rows, cols, fv, av, mk);
                emit(grid, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random grids with random mutations
    while count < count_target {
        let rows = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 4),   // tiny
            1 => rng.gen_range_usize(5, 15),   // small
            2 => rng.gen_range_usize(16, 40),  // medium
            3 => rng.gen_range_usize(41, 60),  // large
            _ => rng.gen_range_usize(61, 70),  // max
        };
        let cols = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 4),
            1 => rng.gen_range_usize(5, 15),
            2 => rng.gen_range_usize(16, 40),
            3 => rng.gen_range_usize(41, 60),
            _ => rng.gen_range_usize(61, 70),
        };
        let fill_val = rng.gen_range_i64(0, 100) as i32;
        let alt_val = rng.gen_range_i64(0, 100) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;

        // Build grid using the verified generator
        let mut grid = generate_test_case(rows, cols, fill_val, alt_val, mk);

        // Randomly overwrite some cells for extra diversity (unverified but valid)
        let num_overwrites = rng.gen_range_usize(0, rows * cols / 4 + 1);
        for _ in 0..num_overwrites {
            let ri = rng.gen_range_usize(0, rows - 1);
            let ci = rng.gen_range_usize(0, cols - 1);
            let v = rng.gen_range_i64(0, 100) as i32;
            grid[ri][ci] = v;
        }

        emit(grid, &mut seen, &mut out, &mut count);
    }
}
