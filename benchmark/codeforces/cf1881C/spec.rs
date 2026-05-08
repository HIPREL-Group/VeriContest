use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

pub open spec fn spec_i4max(a: int, b: int, c: int, d: int) -> int {
    spec_i2max(spec_i2max(a, b), spec_i2max(c, d))
}

pub open spec fn spec_cell(grid: Seq<i64>, n: int, r: int, c: int) -> int
    recommends
        grid.len() == n * n,
        0 <= r < n,
        0 <= c < n,
{
    grid[r * n + c] as int
}

pub open spec fn spec_orbit_max4(grid: Seq<i64>, n: int, i: int, j: int) -> int
    recommends
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j < n / 2,
{
    spec_i4max(
        spec_cell(grid, n, i, j),
        spec_cell(grid, n, j, n - 1 - i),
        spec_cell(grid, n, n - 1 - i, n - 1 - j),
        spec_cell(grid, n, n - 1 - j, i),
    )
}

pub open spec fn spec_orbit_cost(grid: Seq<i64>, n: int, i: int, j: int) -> int
    recommends
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j < n / 2,
{
    let m = spec_orbit_max4(grid, n, i, j);
    (m - spec_cell(grid, n, i, j)) + (m - spec_cell(grid, n, j, n - 1 - i))
        + (m - spec_cell(grid, n, n - 1 - i, n - 1 - j)) + (m - spec_cell(grid, n, n - 1 - j, i))
}

impl Solution {
    pub open spec fn spec_row_sum(grid: Seq<i64>, n: int, ri: int, j_end: int) -> int
        recommends
            n % 2 == 0,
            2 <= n <= 1000,
            grid.len() == n * n,
            0 <= ri < n / 2,
            0 <= j_end <= n / 2,
        decreases j_end + 1,
    {
        if j_end <= 0 {
            0
        } else {
            Self::spec_row_sum(grid, n, ri, j_end - 1) + spec_orbit_cost(grid, n, ri, j_end - 1)
        }
    }

    pub open spec fn spec_rows_sum(grid: Seq<i64>, n: int, ri_end: int) -> int
        recommends
            n % 2 == 0,
            2 <= n <= 1000,
            grid.len() == n * n,
            0 <= ri_end <= n / 2,
        decreases ri_end + 1,
    {
        if ri_end <= 0 {
            0
        } else {
            Self::spec_rows_sum(grid, n, ri_end - 1) + Self::spec_row_sum(grid, n, ri_end - 1, n / 2)
        }
    }

    pub fn min_ops_perfect_square(n: usize, grid: Vec<i64>) -> (res: i64)
        requires
            2 <= (n as int) <= 1000,
            (n as int) % 2 == 0,
            (grid.len() as int) == (n as int) * (n as int),
            forall|k: int|
                0 <= k < (grid.len() as int) ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
        ensures
            (res as int) == Self::spec_rows_sum(grid@, n as int, n as int / 2),
    {
    }
}

}
