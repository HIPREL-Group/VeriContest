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
        while i < m
            invariant
                m == mat.len(),
                n == mat[0].len(),
                1 <= m <= 100,
                1 <= n <= 100,
                forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                0 <= i <= m,
                row_sums@.len() == i as int,
                forall |r: int| 0 <= r < i as int ==> (#[trigger] row_sums@[r]) as int == Self::count_ones_in_row(mat@, r, n as int),
                forall |r: int| 0 <= r < i as int ==> 0 <= (#[trigger] row_sums@[r]) <= n as i32,
            decreases m - i
        {
            let mut s: i32 = 0;
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    0 <= i < m,
                    m == mat.len(),
                    n == mat[0].len(),
                    1 <= m <= 100,
                    1 <= n <= 100,
                    forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                    forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                    0 <= s as int <= j as int,
                    s as int == Self::count_ones_in_row(mat@, i as int, j as int),
                decreases n - j
            {
                proof {
                    assert(Self::count_ones_in_row(mat@, i as int, (j + 1) as int)
                        == Self::count_ones_in_row(mat@, i as int, j as int)
                            + if mat@[i as int]@[j as int] == 1 { 1int } else { 0int });
                }
                s = s + mat[i][j];
                j = j + 1;
            }
            row_sums.push(s);
            i = i + 1;
        }
        let mut col_sums: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                m == mat.len(),
                n == mat[0].len(),
                1 <= m <= 100,
                1 <= n <= 100,
                forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                row_sums@.len() == m as int,
                forall |r: int| 0 <= r < m as int ==> (#[trigger] row_sums@[r]) as int == Self::count_ones_in_row(mat@, r, n as int),
                0 <= j <= n,
                col_sums@.len() == j as int,
                forall |c: int| 0 <= c < j as int ==> (#[trigger] col_sums@[c]) as int == Self::count_ones_in_col(mat@, c, m as int),
                forall |c: int| 0 <= c < j as int ==> 0 <= (#[trigger] col_sums@[c]) <= m as i32,
            decreases n - j
        {
            let mut s: i32 = 0;
            let mut k: usize = 0;
            while k < m
                invariant
                    0 <= k <= m,
                    0 <= j < n,
                    m == mat.len(),
                    n == mat[0].len(),
                    1 <= m <= 100,
                    1 <= n <= 100,
                    forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                    forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                    0 <= s as int <= k as int,
                    s as int == Self::count_ones_in_col(mat@, j as int, k as int),
                decreases m - k
            {
                proof {
                    assert(Self::count_ones_in_col(mat@, j as int, (k + 1) as int)
                        == Self::count_ones_in_col(mat@, j as int, k as int)
                            + if mat@[k as int]@[j as int] == 1 { 1int } else { 0int });
                }
                s = s + mat[k][j];
                k = k + 1;
            }
            col_sums.push(s);
            j = j + 1;
        }
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < m
            invariant
                m == mat.len(),
                n == mat[0].len(),
                1 <= m <= 100,
                1 <= n <= 100,
                forall |r: int| 0 <= r < mat.len() ==> 1 <= #[trigger] mat[r].len() <= 100,
                forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                row_sums@.len() == m as int,
                col_sums@.len() == n as int,
                forall |r: int| 0 <= r < m as int ==> (#[trigger] row_sums@[r]) as int == Self::count_ones_in_row(mat@, r, n as int),
                forall |c: int| 0 <= c < n as int ==> (#[trigger] col_sums@[c]) as int == Self::count_ones_in_col(mat@, c, m as int),
                0 <= i <= m,
                0 <= count as int <= i as int * n as int,
                count as int == Self::count_special_in_grid(mat@, n as int, i as int),
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    m == mat.len(),
                    n == mat[0].len(),
                    1 <= m <= 100,
                    1 <= n <= 100,
                    forall |r: int| 0 <= r < mat.len() ==> 1 <= #[trigger] mat[r].len() <= 100,
                    forall |r: int| 0 <= r < mat.len() ==> mat[r].len() == n,
                    forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len() ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
                    row_sums@.len() == m as int,
                    col_sums@.len() == n as int,
                    forall |r: int| 0 <= r < m as int ==> (#[trigger] row_sums@[r]) as int == Self::count_ones_in_row(mat@, r, n as int),
                    forall |c: int| 0 <= c < n as int ==> (#[trigger] col_sums@[c]) as int == Self::count_ones_in_col(mat@, c, m as int),
                    0 <= i < m,
                    0 <= j <= n,
                    0 <= count as int <= i as int * n as int + j as int,
                    count as int == Self::count_special_in_grid(mat@, n as int, i as int)
                        + Self::count_special_in_row(mat@, i as int, j as int),
                decreases n - j
            {
                let mut is_spec = false;
                if mat[i][j] == 1 && row_sums[i] == 1 && col_sums[j] == 1 {
                    is_spec = true;
                }
                proof {
                    assert(mat@[i as int]@.len() == n as int);
                    assert(row_sums@[i as int] as int == Self::count_ones_in_row(mat@, i as int, n as int));
                    assert(col_sums@[j as int] as int == Self::count_ones_in_col(mat@, j as int, m as int));
                    assert(Self::count_ones_in_row(mat@, i as int, mat@[i as int]@.len() as int)
                        == Self::count_ones_in_row(mat@, i as int, n as int));
                    assert(Self::count_ones_in_col(mat@, j as int, mat@.len() as int)
                        == Self::count_ones_in_col(mat@, j as int, m as int));
                    assert(is_spec == Self::is_special(mat@, i as int, j as int));
                    assert(Self::count_special_in_row(mat@, i as int, (j + 1) as int)
                        == Self::count_special_in_row(mat@, i as int, j as int)
                            + if Self::is_special(mat@, i as int, j as int) { 1int } else { 0int });
                }
                if is_spec {
                    assert((count as int) < 10000) by(nonlinear_arith)
                        requires
                            0 <= count as int,
                            count as int <= i as int * n as int + j as int,
                            j < n,
                            i < m,
                            m <= 100,
                            n <= 100,
                    {}
                    count = count + 1;
                }
                j = j + 1;
            }
            proof {
                assert(j == n);
                assert(0 <= count as int <= (i as int + 1) * n as int) by(nonlinear_arith)
                    requires
                        0 <= count as int,
                        count as int <= i as int * n as int + j as int,
                        j == n,
                        0 <= i as int,
                        0 <= n as int,
                {}
                assert(Self::count_special_in_grid(mat@, n as int, (i + 1) as int)
                    == Self::count_special_in_grid(mat@, n as int, i as int)
                        + Self::count_special_in_row(mat@, i as int, n as int));
            }
            i = i + 1;
        }
        count
    }
}
}
