use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub open spec fn count_ones_in_row(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        decreases j
    {
        if j <= 0 {
            0
        } else {
            Self::count_ones_in_row(grid, i, j - 1) + if grid[i]@[j - 1] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn count_ones_in_col(grid: Seq<Vec<i32>>, j: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::count_ones_in_col(grid, j, i - 1) + if grid[i - 1]@[j] == 1 { 1int } else { 0int }
        }
    }

    pub open spec fn is_special(grid: Seq<Vec<i32>>, i: int, j: int) -> bool {
        &&& 0 <= i < grid.len()
        &&& 0 <= j < grid[i]@.len()
        &&& grid[i]@[j] == 1
        &&& Self::count_ones_in_row(grid, i, grid[i]@.len() as int) == 1
        &&& Self::count_ones_in_col(grid, j, grid.len() as int) == 1
    }

    pub open spec fn count_special_in_row(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        decreases j
    {
        if j <= 0 {
            0
        } else {
            Self::count_special_in_row(grid, i, j - 1)
                + if Self::is_special(grid, i, j - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn count_special_in_grid(grid: Seq<Vec<i32>>, n: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::count_special_in_grid(grid, n, i - 1)
                + Self::count_special_in_row(grid, i - 1, n)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn num_special(mat: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= mat.len() <= 100,
            forall |r: int| 0 <= r < mat.len() ==> 1 <= #[trigger] mat[r].len() <= 100,
            forall |r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
            forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
        ensures
            res as int == Self::count_special_in_grid(mat@, mat[0].len() as int, mat.len() as int),
    {
        let m = mat.len();
        let n = mat[0].len();
        let mut row_sums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut s: i32 = 0;
            let mut j: usize = 0;
            while j < n {
                s = s + mat[i][j];
                j = j + 1;
            }
            row_sums.push(s);
            i = i + 1;
        }
        let mut col_sums: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut s: i32 = 0;
            let mut k: usize = 0;
            while k < m {
                s = s + mat[k][j];
                k = k + 1;
            }
            col_sums.push(s);
            j = j + 1;
        }
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < m {
            let mut j: usize = 0;
            while j < n {
                if mat[i][j] == 1 && row_sums[i] == 1 && col_sums[j] == 1 {
                    count = count + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count
    }
}
}
