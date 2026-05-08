use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;




















pub open spec fn is_all_ones_square(mat: Seq<Vec<i32>>, r: int, c: int, s: int) -> bool {
    &&& s >= 1
    &&& r >= 0 && r + s <= mat.len()
    &&& c >= 0 && c + s <= mat[0int].len()
    &&& forall|dr: int, dc: int|
        0 <= dr < s && 0 <= dc < s ==> #[trigger] mat[r + dr][c + dc] == 1
}

pub open spec fn min3(a: int, b: int, c: int) -> int {
    if a <= b && a <= c { a }
    else if b <= c { b }
    else { c }
}

pub open spec fn dp_val(mat: Seq<Vec<i32>>, i: int, j: int) -> int
    decreases (if i > 0 { i } else { 0 }) + (if j > 0 { j } else { 0 })
{
    if i < 0 || j < 0 { 0 }
    else if mat[i][j] != 1 { 0 }
    else if i == 0 || j == 0 { 1 }
    else { 1 + min3(dp_val(mat, i - 1, j), dp_val(mat, i, j - 1), dp_val(mat, i - 1, j - 1)) }
}

pub open spec fn row_sum(mat: Seq<Vec<i32>>, i: int, j: int, n: int) -> int
    decreases (if j < n { n - j } else { 0 })
{
    if j >= n { 0 }
    else { dp_val(mat, i, j) + row_sum(mat, i, j + 1, n) }
}

pub open spec fn total_sum(mat: Seq<Vec<i32>>, i: int, m: int, n: int) -> int
    decreases (if i < m { m - i } else { 0 })
{
    if i >= m { 0 }
    else { row_sum(mat, i, 0, n) + total_sum(mat, i + 1, m, n) }
}

proof fn dp_val_bounds(mat: Seq<Vec<i32>>, m: int, n: int, i: int, j: int)
    requires
        m == mat.len(),
        m >= 1,
        n >= 1,
        0 <= i < m,
        0 <= j < n,
        forall |r: int| 0 <= r < m ==> (#[trigger] mat[r]).len() == n,
        forall |r: int, c: int| 0 <= r < m && 0 <= c < n
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        0 <= dp_val(mat, i, j),
        dp_val(mat, i, j) <= i + 1,
        dp_val(mat, i, j) <= j + 1,
    decreases i + j
{
    if mat[i][j] != 1 {
    } else if i == 0 || j == 0 {
    } else {
        dp_val_bounds(mat, m, n, i - 1, j);
        dp_val_bounds(mat, m, n, i, j - 1);
        dp_val_bounds(mat, m, n, i - 1, j - 1);
    }
}

proof fn row_sum_split(mat: Seq<Vec<i32>>, i: int, a: int, b: int, n: int)
    requires
        a <= b,
        b <= n,
    ensures
        row_sum(mat, i, a, n) == row_sum(mat, i, a, b) + row_sum(mat, i, b, n),
    decreases b - a
{
    if a < b {
        row_sum_split(mat, i, a + 1, b, n);
    }
}

proof fn total_sum_split(mat: Seq<Vec<i32>>, a: int, b: int, m: int, n: int)
    requires
        a <= b,
        b <= m,
    ensures
        total_sum(mat, a, m, n) == total_sum(mat, a, b, n) + total_sum(mat, b, m, n),
    decreases b - a
{
    if a < b {
        total_sum_split(mat, a + 1, b, m, n);
    }
}

proof fn row_sum_nonneg(mat: Seq<Vec<i32>>, m: int, n: int, i: int, j: int)
    requires
        m == mat.len(),
        m >= 1,
        n >= 1,
        0 <= i < m,
        0 <= j,
        forall |r: int| 0 <= r < m ==> (#[trigger] mat[r]).len() == n,
        forall |r: int, c: int| 0 <= r < m && 0 <= c < n
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        row_sum(mat, i, j, n) >= 0,
    decreases (if j < n { n - j } else { 0 })
{
    if j < n {
        dp_val_bounds(mat, m, n, i, j);
        row_sum_nonneg(mat, m, n, i, j + 1);
    }
}

proof fn total_sum_nonneg(mat: Seq<Vec<i32>>, m: int, n: int, i: int)
    requires
        m == mat.len(),
        m >= 1,
        n >= 1,
        0 <= i,
        forall |r: int| 0 <= r < m ==> (#[trigger] mat[r]).len() == n,
        forall |r: int, c: int| 0 <= r < m && 0 <= c < n
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        total_sum(mat, i, m, n) >= 0,
    decreases (if i < m { m - i } else { 0 })
{
    if i < m {
        row_sum_nonneg(mat, m, n, i, 0);
        total_sum_nonneg(mat, m, n, i + 1);
    }
}

proof fn row_sum_upper_bound(mat: Seq<Vec<i32>>, m: int, n: int, i: int, j: int)
    requires
        m == mat.len(),
        1 <= m <= 300,
        1 <= n <= 300,
        0 <= i < m,
        0 <= j,
        forall |r: int| 0 <= r < m ==> (#[trigger] mat[r]).len() == n,
        forall |r: int, c: int| 0 <= r < m && 0 <= c < n
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        row_sum(mat, i, j, n) <= (if j < n { (n - j) * 300 } else { 0 }),
    decreases (if j < n { n - j } else { 0 })
{
    if j < n {
        dp_val_bounds(mat, m, n, i, j);
        row_sum_upper_bound(mat, m, n, i, j + 1);
        assert(dp_val(mat, i, j) <= 300) by {
            assert(dp_val(mat, i, j) <= i + 1);
            assert(i + 1 <= 300);
        }
        assert((n - j) * 300 >= 300 + (n - j - 1) * 300) by (nonlinear_arith)
            requires n > j;
    }
}

proof fn total_sum_upper_bound(mat: Seq<Vec<i32>>, m: int, n: int, i: int)
    requires
        m == mat.len(),
        1 <= m <= 300,
        1 <= n <= 300,
        0 <= i,
        forall |r: int| 0 <= r < m ==> (#[trigger] mat[r]).len() == n,
        forall |r: int, c: int| 0 <= r < m && 0 <= c < n
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        total_sum(mat, i, m, n) <= (if i < m { (m - i) * n * 300 } else { 0 }),
    decreases (if i < m { m - i } else { 0 })
{
    if i < m {
        row_sum_upper_bound(mat, m, n, i, 0);
        total_sum_upper_bound(mat, m, n, i + 1);
        assert(row_sum(mat, i, 0, n) <= n * 300);
        if i + 1 < m {
            assert(total_sum(mat, i + 1, m, n) <= (m - i - 1) * n * 300);
        }
        assert(n * 300 + (m - i - 1) * n * 300 <= (m - i) * n * 300) by (nonlinear_arith)
            requires m > i, n >= 1;
    }
}

impl Solution {
    fn set_dp(dp: &mut Vec<Vec<i32>>, row: usize, col: usize, value: i32)
        requires
            row < old(dp)@.len(),
            col < old(dp)@[row as int].len(),
        ensures
            dp@.len() == old(dp)@.len(),
            forall |r: int| 0 <= r < dp@.len() ==> (#[trigger] dp@[r]).len() == old(dp)@[r].len(),
            forall |r: int, c: int|
                0 <= r < dp@.len() && 0 <= c < dp@[r].len()
                    ==> #[trigger] dp@[r][c] == if r == row as int && c == col as int { value } else { old(dp)@[r][c] },
    {
        let mut current_row = dp[row].clone();
        current_row.set(col, value);
        dp.set(row, current_row);
    }

    pub fn count_squares(matrix: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= matrix.len() <= 300,
            forall |i: int| 0 <= i < matrix.len() ==> 1 <= (#[trigger] matrix[i]).len() <= 300,
            forall |i: int| 0 <= i < matrix.len() ==> (#[trigger] matrix[i]).len() == matrix[0].len(),
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[0].len()
                ==> #[trigger] matrix[i][j] == 0 || matrix[i][j] == 1,
        ensures
            result as int == total_sum(matrix@, 0, matrix.len() as int, matrix[0].len() as int),
    {
        let m = matrix.len();
        let n = matrix[0].len();

        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                m == matrix.len(),
                n == matrix[0].len(),
                dp@.len() == i as int,
                0 <= i <= m,
                forall |r: int| 0 <= r < i ==> (#[trigger] dp@[r]).len() == n as int,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==> #[trigger] dp@[r][c] == 0i32,
            decreases m - i
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    n == matrix[0].len(),
                    row@.len() == j as int,
                    0 <= j <= n,
                    forall |c: int| 0 <= c < j ==> #[trigger] row@[c] == 0i32,
                decreases n - j
            {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }

        proof {
            total_sum_upper_bound(matrix@, m as int, n as int, 0);
            assert(m as int * n as int * 300 <= 27_000_000) by (nonlinear_arith)
                requires 1 <= m as int <= 300, 1 <= n as int <= 300;
            total_sum_nonneg(matrix@, m as int, n as int, 0);
        }

        let mut ans: i32 = 0;
        i = 0;
        while i < m
            invariant
                m == matrix.len(),
                n == matrix[0].len(),
                1 <= m <= 300,
                1 <= n <= 300,
                dp@.len() == m as int,
                forall |r: int| 0 <= r < m ==> (#[trigger] dp@[r]).len() == n as int,
                forall |i2: int| 0 <= i2 < matrix.len() ==> 1 <= (#[trigger] matrix[i2]).len() <= 300,
                forall |i2: int| 0 <= i2 < matrix.len() ==> (#[trigger] matrix[i2]).len() == matrix[0].len(),
                forall |i2: int, j2: int| 0 <= i2 < matrix.len() && 0 <= j2 < matrix[0].len()
                    ==> #[trigger] matrix[i2][j2] == 0 || matrix[i2][j2] == 1,
                0 <= i <= m,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < n
                    ==> (#[trigger] dp@[r][c]) as int == dp_val(matrix@, r, c),
                forall |r: int, c: int| i <= r < m && 0 <= c < n
                    ==> (#[trigger] dp@[r][c]) == 0i32,
                ans as int == total_sum(matrix@, 0, i as int, n as int),
                0 <= ans as int <= 27_000_000,
            decreases m - i
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    m == matrix.len(),
                    n == matrix[0].len(),
                    1 <= m <= 300,
                    1 <= n <= 300,
                    dp@.len() == m as int,
                    forall |r: int| 0 <= r < m ==> (#[trigger] dp@[r]).len() == n as int,
                    forall |i2: int| 0 <= i2 < matrix.len() ==> 1 <= (#[trigger] matrix[i2]).len() <= 300,
                    forall |i2: int| 0 <= i2 < matrix.len() ==> (#[trigger] matrix[i2]).len() == matrix[0].len(),
                    forall |i2: int, j2: int| 0 <= i2 < matrix.len() && 0 <= j2 < matrix[0].len()
                        ==> #[trigger] matrix[i2][j2] == 0 || matrix[i2][j2] == 1,
                    0 <= i < m,
                    0 <= j <= n,
                    forall |r: int, c: int| 0 <= r < i && 0 <= c < n
                        ==> (#[trigger] dp@[r][c]) as int == dp_val(matrix@, r, c),
                    forall |c: int| 0 <= c < j
                        ==> (#[trigger] dp@[i as int][c]) as int == dp_val(matrix@, i as int, c),
                    forall |c: int| j <= c < n
                        ==> (#[trigger] dp@[i as int][c]) == 0i32,
                    forall |r: int, c: int| i + 1 <= r < m && 0 <= c < n
                        ==> (#[trigger] dp@[r][c]) == 0i32,
                    ans as int == total_sum(matrix@, 0, i as int, n as int) + row_sum(matrix@, i as int, 0, j as int),
                    0 <= ans as int <= 27_000_000,
                decreases n - j
            {
                let ghost ii = i as int;
                let ghost jj = j as int;

                if matrix[i][j] == 1 {
                    if i == 0 || j == 0 {
                        Self::set_dp(&mut dp, i, j, 1);
                    } else {
                        let a = dp[i - 1][j];
                        let b = dp[i][j - 1];
                        let c = dp[i - 1][j - 1];
                        proof {
                            assert(a as int == dp_val(matrix@, ii - 1, jj));
                            assert(b as int == dp_val(matrix@, ii, jj - 1));
                            assert(c as int == dp_val(matrix@, ii - 1, jj - 1));
                            dp_val_bounds(matrix@, m as int, n as int, ii - 1, jj);
                            dp_val_bounds(matrix@, m as int, n as int, ii, jj - 1);
                            dp_val_bounds(matrix@, m as int, n as int, ii - 1, jj - 1);
                        }
                        let min_val = if a <= b && a <= c { a } else if b <= c { b } else { c };
                        Self::set_dp(&mut dp, i, j, 1 + min_val);
                    }
                }

                proof {
                    dp_val_bounds(matrix@, m as int, n as int, ii, jj);

                    assert(dp@[ii][jj] as int == dp_val(matrix@, ii, jj));

                    assert(0 <= dp@[ii][jj] as int <= 300) by {
                        assert(dp@[ii][jj] as int == dp_val(matrix@, ii, jj));
                        assert(dp_val(matrix@, ii, jj) <= ii + 1);
                        assert(ii + 1 <= 300);
                    }

                    row_sum_split(matrix@, ii, 0, jj, jj + 1);
                    assert(row_sum(matrix@, ii, jj + 1, jj + 1) == 0int);
                    assert(row_sum(matrix@, ii, jj, jj + 1) == dp_val(matrix@, ii, jj) + 0int);
                    assert(row_sum(matrix@, ii, jj, jj + 1) == dp_val(matrix@, ii, jj));

                    row_sum_split(matrix@, ii, 0, jj + 1, n as int);
                    row_sum_nonneg(matrix@, m as int, n as int, ii, jj + 1);
                    total_sum_split(matrix@, 0, ii, m as int, n as int);
                    total_sum_split(matrix@, 0, ii + 1, m as int, n as int);
                    total_sum_nonneg(matrix@, m as int, n as int, ii + 1);
                    row_sum_nonneg(matrix@, m as int, n as int, ii, 0);

                    assert(total_sum(matrix@, 0, ii + 1, n as int)
                        == total_sum(matrix@, 0, ii, n as int) + row_sum(matrix@, ii, 0, n as int));
                    assert(row_sum(matrix@, ii, 0, n as int)
                        == row_sum(matrix@, ii, 0, jj + 1) + row_sum(matrix@, ii, jj + 1, n as int));
                    assert(row_sum(matrix@, ii, jj + 1, n as int) >= 0);
                    assert(total_sum(matrix@, ii + 1, m as int, n as int) >= 0);
                    assert(total_sum(matrix@, 0, m as int, n as int)
                        == total_sum(matrix@, 0, ii + 1, n as int) + total_sum(matrix@, ii + 1, m as int, n as int));

                    total_sum_upper_bound(matrix@, m as int, n as int, 0);
                    assert(m as int * n as int * 300 <= 27_000_000) by (nonlinear_arith)
                        requires 1 <= m as int <= 300, 1 <= n as int <= 300;
                }

                ans = ans + dp[i][j];
                j = j + 1;
            }

            proof {
                let ii = i as int;
                total_sum_split(matrix@, 0, ii, ii + 1, n as int);
                assert(total_sum(matrix@, ii + 1, ii + 1, n as int) == 0int);
                assert(total_sum(matrix@, ii, ii + 1, n as int) == row_sum(matrix@, ii, 0, n as int) + 0int);
                assert(total_sum(matrix@, ii, ii + 1, n as int) == row_sum(matrix@, ii, 0, n as int));
                assert(ans as int == total_sum(matrix@, 0, ii + 1, n as int));

                assert forall |r: int, c: int| 0 <= r < ii + 1 && 0 <= c < n as int
                    implies (#[trigger] dp@[r][c]) as int == dp_val(matrix@, r, c) by {};
            }

            i = i + 1;
        }

        ans
    }
}

}
