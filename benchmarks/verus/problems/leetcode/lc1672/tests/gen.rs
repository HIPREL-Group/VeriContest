use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<Vec<i32>>` (accounts grid) for maximum_wealth
/// from seed rows, applying mutation_kind to diversify generated inputs.
///
/// Mutations:
///   0 — identity (copy seed rows as-is)
///   1 — set all elements to rows[0][0] (uniform grid)
///   2 — nudge rows[0][0] up by 1 (if < 100)
///   3 — nudge rows[0][0] down by 1 (if > 1)
///   4 — set all elements to 1 (min boundary)
///   5 — set all elements to 100 (max boundary)
///   6 — swap first and last rows (if rows.len() >= 2)
pub fn generate_test_case(
    rows: &Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows.len() <= 50,
        1 <= rows[0].len() <= 50,
        forall|i: int|
            0 <= i < rows.len()
                ==> #[trigger] rows[i].len() == rows[0].len(),
        forall|i: int, j: int|
            0 <= i < rows.len() && 0 <= j < rows[i].len()
                ==> 1 <= #[trigger] rows[i][j] <= 100,
    ensures
        1 <= result.len() <= 50,
        1 <= result[0].len() <= 50,
        forall|i: int|
            0 <= i < result.len()
                ==> #[trigger] result[i].len() == result[0].len(),
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len()
                ==> 1 <= #[trigger] result[i][j] <= 100,
{
    let m = rows.len();
    let n = rows[0].len();
    let mut result: Vec<Vec<i32>> = Vec::new();

    if mutation_kind == 1 || mutation_kind == 4 || mutation_kind == 5 {
        // Constant fill: all elements set to val
        let val: i32 = if mutation_kind == 4 {
            1i32
        } else if mutation_kind == 5 {
            100i32
        } else {
            rows[0][0]
        };
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                m == rows.len(),
                1 <= m <= 50,
                1 <= n <= 50,
                n == rows[0].len(),
                1 <= val <= 100,
                result.len() == i,
                forall|k: int| 0 <= k < i as int
                    ==> (#[trigger] result[k]).len() == n,
                forall|k: int, l: int|
                    0 <= k < i as int && 0 <= l < n as int
                        ==> 1 <= #[trigger] result[k][l] <= 100,
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 50,
                    1 <= val <= 100,
                    row.len() == j,
                    forall|l: int| 0 <= l < j as int
                        ==> 1 <= #[trigger] row[l] <= 100,
                decreases n - j,
            {
                row.push(val);
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        assert(result.len() == m);
        result
    } else if mutation_kind == 6 && m >= 2 {
        // Swap first and last rows
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                m == rows.len(),
                n == rows[0].len(),
                1 <= m <= 50,
                1 <= n <= 50,
                m >= 2,
                result.len() == i,
                forall|k: int| 0 <= k < rows.len()
                    ==> (#[trigger] rows[k]).len() == n,
                forall|k: int, l: int|
                    0 <= k < rows.len() && 0 <= l < rows[k].len()
                        ==> 1 <= #[trigger] rows[k][l] <= 100,
                forall|k: int| 0 <= k < i as int
                    ==> (#[trigger] result[k]).len() == n,
                forall|k: int, l: int|
                    0 <= k < i as int && 0 <= l < n as int
                        ==> 1 <= #[trigger] result[k][l] <= 100,
            decreases m - i,
        {
            let src: usize = if i == 0 {
                m - 1
            } else if i == m - 1 {
                0
            } else {
                i
            };
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 50,
                    0 <= src < m,
                    m == rows.len(),
                    n == rows[0].len(),
                    forall|k: int| 0 <= k < rows.len()
                        ==> (#[trigger] rows[k]).len() == n,
                    forall|k: int, l: int|
                        0 <= k < rows.len() && 0 <= l < rows[k].len()
                            ==> 1 <= #[trigger] rows[k][l] <= 100,
                    row.len() == j,
                    forall|l: int| 0 <= l < j as int
                        ==> 1 <= #[trigger] row[l] <= 100,
                decreases n - j,
            {
                row.push(rows[src][j]);
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        assert(result.len() == m);
        result
    } else {
        // Identity (mutation_kind == 0 or fallback) with optional nudge
        // mutation_kind == 2: nudge rows[0][0] up by 1
        // mutation_kind == 3: nudge rows[0][0] down by 1
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                m == rows.len(),
                n == rows[0].len(),
                1 <= m <= 50,
                1 <= n <= 50,
                result.len() == i,
                forall|k: int| 0 <= k < rows.len()
                    ==> (#[trigger] rows[k]).len() == n,
                forall|k: int, l: int|
                    0 <= k < rows.len() && 0 <= l < rows[k].len()
                        ==> 1 <= #[trigger] rows[k][l] <= 100,
                forall|k: int| 0 <= k < i as int
                    ==> (#[trigger] result[k]).len() == n,
                forall|k: int, l: int|
                    0 <= k < i as int && 0 <= l < n as int
                        ==> 1 <= #[trigger] result[k][l] <= 100,
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    0 <= i < m,
                    1 <= n <= 50,
                    m == rows.len(),
                    n == rows[0].len(),
                    forall|k: int| 0 <= k < rows.len()
                        ==> (#[trigger] rows[k]).len() == n,
                    forall|k: int, l: int|
                        0 <= k < rows.len() && 0 <= l < rows[k].len()
                            ==> 1 <= #[trigger] rows[k][l] <= 100,
                    row.len() == j,
                    forall|l: int| 0 <= l < j as int
                        ==> 1 <= #[trigger] row[l] <= 100,
                decreases n - j,
            {
                if i == 0 && j == 0 && mutation_kind == 2 && rows[0][0] < 100 {
                    row.push(rows[0][0] + 1);
                } else if i == 0 && j == 0 && mutation_kind == 3 && rows[0][0] > 1 {
                    row.push(rows[0][0] - 1);
                } else {
                    row.push(rows[i][j]);
                }
                j = j + 1;
            }
            result.push(row);
            i = i + 1;
        }
        assert(result.len() == m);
        result
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

fn random_row(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut row = Vec::with_capacity(n);
    for _ in 0..n {
        row.push(rng.gen_range_i64(1, 100) as i32);
    }
    row
}

fn random_grid(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(m);
    for _ in 0..m {
        grid.push(random_row(rng, n));
    }
    grid
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut seen = std::collections::HashSet::new();
    let mut count: usize = 0;

    let mut emit = |accounts: Vec<Vec<i32>>,
                    seen: &mut std::collections::HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", accounts);
        if !seen.insert(key) { return; }
        let result = Solution::maximum_wealth(accounts.clone());
        writeln!(out, "{}", json!({
            "input": {"accounts": accounts},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    // Example 1: accounts = [[1,2,3],[3,2,1]] -> 6
    {
        let grid = vec![vec![1,2,3], vec![3,2,1]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: accounts = [[1,5],[7,3],[3,5]] -> 10
    {
        let grid = vec![vec![1,5], vec![7,3], vec![3,5]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: accounts = [[2,8,7],[7,1,3],[1,9,5]] -> 17
    {
        let grid = vec![vec![2,8,7], vec![7,1,3], vec![1,9,5]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single cell
    {
        let grid = vec![vec![50]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single row
    {
        let grid = vec![vec![1, 100, 50]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single column
    {
        let grid = vec![vec![10], vec![20], vec![30]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: boundary values
    {
        let grid = vec![vec![1, 1], vec![1, 1]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }
    {
        let grid = vec![vec![100, 100], vec![100, 100]];
        for mk in 0u8..=6 {
            let accounts = generate_test_case(&grid, mk);
            emit(accounts, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];
    while count < target_count {
        // Diverse m (rows) size classes
        let m: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                              // single row
            1 => rng.gen_range_usize(2, 5),      // tiny
            2 => rng.gen_range_usize(6, 15),     // small
            3 => rng.gen_range_usize(16, 35),    // medium
            _ => rng.gen_range_usize(36, 50),    // max
        };

        // Diverse n (cols) size classes
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                              // single column
            1 => rng.gen_range_usize(2, 5),      // tiny
            2 => rng.gen_range_usize(6, 15),     // small
            3 => rng.gen_range_usize(16, 35),    // medium
            _ => rng.gen_range_usize(36, 50),    // max
        };

        // ~20% boundary-heavy grids (values near 1 or 100)
        let grid = if rng.gen_range_usize(0, 4) == 0 {
            let boundary_vals = [1i32, 2, 50, 99, 100];
            let mut g = Vec::with_capacity(m);
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(boundary_vals[rng.gen_range_usize(0, boundary_vals.len() - 1)]);
                }
                g.push(row);
            }
            g
        } else {
            random_grid(&mut rng, m, n)
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let accounts = generate_test_case(&grid, mk);
        emit(accounts, &mut seen, &mut out, &mut count);
    }
}
