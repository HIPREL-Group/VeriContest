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
        let half = n / 2;
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < half
            decreases half - i,
        {
            let mut j: usize = 0;
            while j < half
                decreases half - j,
            {
                let v0 = grid[i * n + j];
                let v1 = grid[j * n + (n - 1 - i)];
                let v2 = grid[(n - 1 - i) * n + (n - 1 - j)];
                let v3 = grid[(n - 1 - j) * n + i];
                let mut m = v0;
                if v1 > m {
                    m = v1;
                }
                if v2 > m {
                    m = v2;
                }
                if v3 > m {
                    m = v3;
                }
                total = total + (m - v0) + (m - v1) + (m - v2) + (m - v3);
                j = j + 1;
            }
            i = i + 1;
        }
        total
    }
}

}
