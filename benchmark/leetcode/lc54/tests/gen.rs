use vstd::prelude::*;

verus! {

proof fn lemma_mul_bound(a: int, b: int, m: int, n: int)
    requires
        0 <= a < m,
        0 <= b < n,
        1 <= m <= 10,
        1 <= n <= 10,
    ensures
        0 <= a * n + b < m * n,
        a * n + b <= 99,
{
    assert(a * n + b < m * n) by(nonlinear_arith)
        requires 0 <= a < m, 0 <= b < n, 1 <= n;
    assert(m * n <= 100) by(nonlinear_arith)
        requires 1 <= m <= 10, 1 <= n <= 10;
}

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
        forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
    ensures
        1 <= result.len() <= 10,
        1 <= result[0].len() <= 10,
        forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall|r: int, c: int| 0 <= r < result.len() && 0 <= c < result[r].len()
            ==> -100 <= #[trigger] result[r][c] <= 100,
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
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    row.len() == j,
                    forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100,
                decreases cols - j,
            {
                row.push(0);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 2 {
        // All -100 (min boundary)
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                grid.len() == i,
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    row.len() == j,
                    forall|c: int| 0 <= c < j ==> -100 <= #[trigger] row[c] <= 100,
                decreases cols - j,
            {
                row.push(-100);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 3 {
        // All 100 (max boundary)
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                grid.len() == i,
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    row.len() == j,
                    forall|c: int| 0 <= c < j ==> -100 <= #[trigger] row[c] <= 100,
                decreases cols - j,
            {
                row.push(100);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 4 {
        // Negate all values from flat_vals
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                flat_vals.len() == rows * cols,
                grid.len() == i,
                forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
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
                    forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                    forall|c: int| 0 <= c < j ==> -100 <= #[trigger] row[c] <= 100,
                decreases cols - j,
            {
                proof { lemma_mul_bound(i as int, j as int, rows as int, cols as int); }
                let idx = i * cols + j;
                let v = -flat_vals[idx];
                row.push(v);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 5 {
        // Absolute value of all values from flat_vals
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                flat_vals.len() == rows * cols,
                grid.len() == i,
                forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
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
                    forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                    forall|c: int| 0 <= c < j ==> -100 <= #[trigger] row[c] <= 100,
                decreases cols - j,
            {
                proof { lemma_mul_bound(i as int, j as int, rows as int, cols as int); }
                let idx = i * cols + j;
                let v = if flat_vals[idx] >= 0 { flat_vals[idx] } else { -flat_vals[idx] };
                row.push(v);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else {
        // Identity / fallback: reshape flat_vals into rows x cols grid
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 10,
                1 <= cols <= 10,
                flat_vals.len() == rows * cols,
                grid.len() == i,
                forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < cols
                    ==> -100 <= #[trigger] grid[r][c] <= 100,
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
                    forall|k: int| 0 <= k < flat_vals.len() ==> -100 <= #[trigger] flat_vals[k] <= 100,
                    forall|c: int| 0 <= c < j ==> -100 <= #[trigger] row[c] <= 100,
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(54);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;
    use std::collections::HashSet;

    let mut rng = Rng::new(seed);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::spiral_order(matrix.clone());
        let line = json!({
            "input": {"matrix": matrix},
            "output": output
        }).to_string();
        if seen.insert(line.clone()) {
            writeln!(out, "{}", line).unwrap();
            *emitted += 1;
        }
    };

    // Example 1: [[1,2,3],[4,5,6],[7,8,9]]
    {
        let flat: Vec<i32> = vec![1,2,3,4,5,6,7,8,9];
        let grid = generate_test_case(3, 3, &flat, 0);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }
    // Example 2: [[1,2,3,4],[5,6,7,8],[9,10,11,12]]
    {
        let flat: Vec<i32> = vec![1,2,3,4,5,6,7,8,9,10,11,12];
        let grid = generate_test_case(3, 4, &flat, 0);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Apply all mutations to the examples
    for mk in 1u8..=5 {
        let flat: Vec<i32> = vec![1,2,3,4,5,6,7,8,9];
        let grid = generate_test_case(3, 3, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Edge cases: 1x1 matrix
    for mk in 0u8..=5 {
        let flat: Vec<i32> = vec![42];
        let grid = generate_test_case(1, 1, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Edge cases: single row (1 x cols)
    for cols in [1usize, 2, 5, 10] {
        let flat: Vec<i32> = (1..=(cols as i32)).map(|x| x.min(100)).collect();
        let grid = generate_test_case(1, cols, &flat, 0);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Edge cases: single column (rows x 1)
    for rows in [1usize, 2, 5, 10] {
        let flat: Vec<i32> = (1..=(rows as i32)).map(|x| x.min(100)).collect();
        let grid = generate_test_case(rows, 1, &flat, 0);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Max size: 10x10
    {
        let flat: Vec<i32> = (1..=100).map(|x: i32| ((x - 1) % 201 - 100).max(-100).min(100)).collect();
        let grid = generate_test_case(10, 10, &flat, 0);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Boundary value matrices with all mutations
    for mk in 0u8..=5 {
        let flat: Vec<i32> = vec![-100; 20];
        let grid = generate_test_case(4, 5, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }
    for mk in 0u8..=5 {
        let flat: Vec<i32> = vec![100; 20];
        let grid = generate_test_case(4, 5, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Asymmetric shapes with random fill and all mutations
    let shapes: Vec<(usize, usize)> = vec![
        (1, 10), (10, 1), (2, 5), (5, 2), (3, 7), (7, 3),
        (1, 1), (2, 2), (4, 4), (6, 8), (8, 6), (10, 10),
    ];
    for &(r, c) in &shapes {
        let total = r * c;
        let mut flat: Vec<i32> = Vec::with_capacity(total);
        for _ in 0..total {
            flat.push(rng.gen_range_i32(-100, 100));
        }
        let mk = rng.gen_range_usize(0, 5) as u8;
        let grid = generate_test_case(r, c, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    // Random test cases with diverse size classes and mutations
    let mut _attempts_0 = 0usize;
    while emitted < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let rows: usize = match emitted % 5 {
            0 => 1,                                  // minimum
            1 => rng.gen_range_usize(1, 3),          // tiny
            2 => rng.gen_range_usize(2, 5),          // small
            3 => rng.gen_range_usize(4, 8),          // medium
            _ => rng.gen_range_usize(6, 10),         // large/max
        };
        let cols: usize = match emitted % 7 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(2, 5),
            3 => rng.gen_range_usize(4, 7),
            4 => rng.gen_range_usize(5, 10),
            5 => 10,
            _ => rng.gen_range_usize(1, 10),
        };

        let total = rows * cols;
        let mut flat: Vec<i32> = Vec::with_capacity(total);
        for k in 0..total {
            let v = if k % 5 == 0 {
                *[-100i32, -1, 0, 1, 100].iter()
                    .nth(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i32(-100, 100)
            };
            flat.push(v);
        }

        let mk = rng.gen_range_usize(0, 5) as u8;
        let grid = generate_test_case(rows, cols, &flat, mk);
        emit(grid, &mut seen, &mut out, &mut emitted);
    }

    eprintln!("Generated {} test cases to {:?}", emitted, out_path);
}
