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
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }
        let mut ans: i32 = 0;
        i = 0;
        while i < m {
            let mut j: usize = 0;
            while j < n {
                if matrix[i][j] == 1 {
                    if i == 0 || j == 0 {
                        Self::set_dp(&mut dp, i, j, 1);
                    } else {
                        let a = dp[i - 1][j];
                        let b = dp[i][j - 1];
                        let c = dp[i - 1][j - 1];
                        let min_val = if a <= b && a <= c { a } else if b <= c { b } else { c };
                        Self::set_dp(&mut dp, i, j, 1 + min_val);
                    }
                }
                ans = ans + dp[i][j];
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
