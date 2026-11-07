use vstd::prelude::*;

verus! {

proof fn lemma_mul_bound(r: int, c: int, rows: int, cols: int)
    requires
        0 <= r < rows,
        0 <= c < cols,
        1 <= rows <= 10,
        1 <= cols <= 10,
    ensures
        0 <= r * cols + c < rows * cols,
{
    assert(r * cols + c < rows * cols) by(nonlinear_arith)
        requires 0 <= r < rows, 0 <= c < cols, 1 <= cols;
}

/// Constructs a valid m×n grid from a flat array of values and
/// dimensions, applying mutation_kind for diversity.
pub fn generate_test_case(
    rows: usize,
    cols: usize,
    flat_vals: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 10,
        1 <= cols <= 10,
        flat_vals.len() == rows * cols,
        forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 9,
    ensures
        1 <= result.len() <= 10,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i].len() <= 10,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result[0].len() ==> 0 <= #[trigger] result[i][j] <= 9,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();

    if mutation_kind == 1 {
        // All zeros
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                grid.len() == i,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==>
                    0 <= #[trigger] grid[r][c] <= 9,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    row.len() == j,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
                decreases cols - j,
            {
                row.push(0);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 2 {
        // All nines
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                grid.len() == i,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==>
                    0 <= #[trigger] grid[r][c] <= 9,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    row.len() == j,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
                decreases cols - j,
            {
                row.push(9);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 3 {
        // Column-constant: every row gets flat_vals[0..cols],
        // making grid[i][j] == grid[i+1][j] for all valid i.
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                flat_vals.len() == rows * cols,
                grid.len() == i,
                forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 9,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==>
                    0 <= #[trigger] grid[r][c] <= 9,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 10,
                    1 <= rows <= 10,
                    flat_vals.len() == rows * cols,
                    row.len() == j,
                    forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 9,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
                decreases cols - j,
            {
                // j < cols <= rows * cols = flat_vals.len()
                assert(j < flat_vals.len()) by {
                    assert(0 * cols + j < rows * cols) by(nonlinear_arith)
                        requires 0 < rows, 0 <= j < cols, 1 <= cols;
                }
                row.push(flat_vals[j]);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 4 {
        // Ascending columns: grid[i][j] = j % 10,
        // guaranteeing adjacent columns differ (for cols <= 10).
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                grid.len() == i,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==>
                    0 <= #[trigger] grid[r][c] <= 9,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 10,
                    row.len() == j,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
                decreases cols - j,
            {
                row.push((j % 10) as i32);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else {
        // Identity / fallback: reshape flat_vals into rows×cols grid
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                flat_vals.len() == rows * cols,
                grid.len() == i,
                forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 9,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==>
                    0 <= #[trigger] grid[r][c] <= 9,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= i < rows,
                    0 <= j <= cols,
                    1 <= rows <= 10,
                    1 <= cols <= 10,
                    flat_vals.len() == rows * cols,
                    row.len() == j,
                    forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 9,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
                decreases cols - j,
            {
                proof { lemma_mul_bound(i as int, j as int, rows as int, cols as int); }
                let idx = i * cols + j;
                row.push(flat_vals[idx]);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    }

    grid
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;
    use std::collections::HashSet;

    let mut rng = Rng::new(seed);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, generated: &mut usize| {
        if *generated >= count {
            return;
        }
        let key = format!("{:?}", grid);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::satisfies_conditions(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": result
        })).unwrap();
        *generated += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,0,2],vec![1,0,2]],
        vec![vec![1,1,1],vec![0,0,0]],
        vec![vec![1],vec![2],vec![3]],
    ];
    for grid in examples {
        emit(grid, &mut seen, &mut out, &mut generated);
    }

    // Structured seeds: interesting grid patterns
    let seeds: Vec<(usize, usize, Vec<i32>, u8)> = vec![
        // 1x1 grid
        (1, 1, vec![0], 0),
        (1, 1, vec![5], 0),
        (1, 1, vec![9], 0),
        // 1-row grids
        (1, 3, vec![1, 2, 3], 0),
        (1, 5, vec![0, 1, 2, 3, 4], 0),
        // 1-col grids
        (3, 1, vec![5, 5, 5], 0),
        (3, 1, vec![1, 2, 3], 0),
        // All same value (satisfies vertical, fails horizontal if cols > 1)
        (2, 2, vec![3, 3, 3, 3], 0),
        // Columns differ, rows same
        (2, 3, vec![1, 2, 3, 1, 2, 3], 0),
        // Max size
        (10, 10, vec![0; 100], 0),
        // All mutations on a 2x3 grid
        (2, 3, vec![4, 5, 6, 4, 5, 6], 1),
        (2, 3, vec![4, 5, 6, 4, 5, 6], 2),
        (2, 3, vec![4, 5, 6, 4, 5, 6], 3),
        (2, 3, vec![4, 5, 6, 4, 5, 6], 4),
    ];
    for (r, c, vals, mk) in seeds {
        let grid = generate_test_case(r, c, &vals, mk);
        emit(grid, &mut seen, &mut out, &mut generated);
    }

    // Random test cases
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];
    while generated < count {
        // Size classes
        let rows: usize = match rng.next_u64() % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(2, 5),
            3 => rng.gen_range_usize(5, 8),
            _ => rng.gen_range_usize(8, 10),
        };
        let cols: usize = match rng.next_u64() % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(2, 5),
            3 => rng.gen_range_usize(5, 8),
            _ => rng.gen_range_usize(8, 10),
        };

        let total = rows * cols;
        let mut flat_vals: Vec<i32> = Vec::with_capacity(total);
        for _ in 0..total {
            let v = if rng.next_u64() % 5 == 0 {
                *[0i32, 1, 9, 5, 0].iter()
                    .nth(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i32(0, 9)
            };
            flat_vals.push(v);
        }

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let grid = generate_test_case(rows, cols, &flat_vals, mk);
        emit(grid, &mut seen, &mut out, &mut generated);
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
