use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures
        3 <= grid.len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 100000,

{
    let n = if values.len() < 3 { 3usize } else if values.len() > 100 { 100usize } else { values.len() };
    let cols = n;
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r = 0usize;
    while r < n
        invariant
            3 <= n <= 100,
            1 <= cols <= 100,
            cols == n,
            0 <= r <= n,
            grid.len() == r,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> 0 <= #[trigger] grid[i][j] <= 100000,

        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant
                3 <= n <= 100,
                0 <= r < n,
                1 <= cols <= 100,
                0 <= c <= cols,
                row.len() == c,
                grid.len() == r,
                forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> 0 <= #[trigger] grid[i][j] <= 100000,
                forall|j: int| 0 <= j < row.len() ==> 0 <= #[trigger] row[j] <= 100000,

            decreases cols - c,
        {
            let value = if r < values.len() && c < values[r].len() { values[r][c] } else { 0 };
            let mut value = if value < 0 { 0 } else if value > 100000 { 100000 } else { value };

            row.push(value);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
}


proof fn lemma_mul_bound(a: int, b: int, n: int)
    requires
        0 <= a < n,
        0 <= b < n,
        1 <= n <= 100,
    ensures
        0 <= a * n + b < n * n,
        a * n + b <= 9999,
{
    assert(a * n + b < n * n) by(nonlinear_arith)
        requires 0 <= a < n, 0 <= b < n, 1 <= n;
    assert(n * n <= 100 * 100) by(nonlinear_arith)
        requires 1 <= n <= 100;
}

/// Constructs a valid n*n grid for check_x_matrix from a flat array
/// of values and a matrix size, applying mutation_kind for diversity.
pub fn generate_candidate(
    n: usize,
    flat_vals: &Vec<i32>,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 100,
        flat_vals.len() == n * n,
        forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 100000,
    ensures
        1 <= grid.len() <= 100,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
            0 <= #[trigger] grid[i][j] <= 100000,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();

    if mutation_kind == 1 {
        // All zeros
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                grid.len() == i,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                    0 <= #[trigger] grid[r][c] <= 100000,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    row.len() == j,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100000,
                decreases n - j,
            {
                row.push(0);
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 2 {
        // X-matrix pattern: diagonal cells nonzero, off-diagonal 0
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                flat_vals.len() == n * n,
                grid.len() == i,
                forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 100000,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                    0 <= #[trigger] grid[r][c] <= 100000,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= i < n,
                    0 <= j <= n,
                    1 <= n <= 100,
                    flat_vals.len() == n * n,
                    row.len() == j,
                    forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 100000,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100000,
                decreases n - j,
            {
                let is_diag = (i == j) || (i + j + 1 == n);
                if is_diag {
                    proof { lemma_mul_bound(i as int, j as int, n as int); }
                    let idx = i * n + j;
                    let v = flat_vals[idx];
                    if v < 1 {
                        row.push(1);
                    } else {
                        row.push(v);
                    }
                } else {
                    row.push(0);
                }
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else if mutation_kind == 4 {
        // Diagonal = 100000, off-diagonal = 0 (always X-matrix)
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                grid.len() == i,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                    0 <= #[trigger] grid[r][c] <= 100000,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= i < n,
                    0 <= j <= n,
                    1 <= n <= 100,
                    row.len() == j,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100000,
                decreases n - j,
            {
                let is_diag: bool = if i == j { true } else if i + j + 1 == n { true } else { false };
                if is_diag {
                    row.push(100000);
                } else {
                    row.push(0);
                }
                j = j + 1;
            }
            grid.push(row);
            i = i + 1;
        }
    } else {
        // Identity / fallback: reshape flat_vals into n*n grid
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100,
                flat_vals.len() == n * n,
                grid.len() == i,
                forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 100000,
                forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                    0 <= #[trigger] grid[r][c] <= 100000,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= i < n,
                    0 <= j <= n,
                    1 <= n <= 100,
                    flat_vals.len() == n * n,
                    row.len() == j,
                    forall |k: int| 0 <= k < flat_vals.len() ==> 0 <= #[trigger] flat_vals[k] <= 100000,
                    forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100000,
                decreases n - j,
            {
                proof { lemma_mul_bound(i as int, j as int, n as int); }
                let idx = i * n + j;
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

    let mut rng = Rng::new(seed);

    // Example test cases from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![2,0,0,1],vec![0,3,1,0],vec![0,5,2,0],vec![4,0,0,2]],
        vec![vec![5,7,0],vec![0,3,1],vec![0,5,0]],
    ];
    for grid in &examples {
        let grid = generate_test_case(grid.clone());
        let result = Solution::check_x_matrix(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": result
        })).unwrap();
    }

    let remaining = if count > examples.len() { count - examples.len() } else { 0 };

    for i in 0..remaining {
        // Size classes for n
        let n: usize = match i % 6 {
            0 => 1,                                       // minimum
            1 => rng.gen_range_usize(1, 3),               // tiny
            2 => rng.gen_range_usize(3, 10),              // small
            3 => rng.gen_range_usize(11, 30),             // medium
            4 => rng.gen_range_usize(31, 70),             // large
            _ => rng.gen_range_usize(71, 100),            // max range
        };

        // Build flat_vals of size n*n
        let total = n * n;
        let mut flat_vals: Vec<i32> = Vec::with_capacity(total);
        for _ in 0..total {
            let v = if rng.next_u64() % 5 == 0 {
                *[0i32, 1, 100000, 99999, 50000].iter()
                    .nth(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i32(0, 100000)
            };
            flat_vals.push(v);
        }

        // Choose mutation kind for diversity
        let mutation_kind: u8 = match i % 10 {
            0 => 0,  // identity (random grid)
            1 => 1,  // all zeros
            2 => 2,  // X-matrix pattern
            3 => 4,  // diagonal max X-matrix
            _ => rng.gen_range_usize(0, 4) as u8,
        };

        let grid = generate_candidate(n, &flat_vals, mutation_kind);
        let grid = generate_test_case(grid.clone());
        let result = Solution::check_x_matrix(grid.clone());

        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": result
        })).unwrap();
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
