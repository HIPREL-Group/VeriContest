use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_val(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn row_abs_sum(row: Seq<i32>, j: int) -> int
        decreases j
    {
        if j <= 0 { 0int }
        else { Self::row_abs_sum(row, j - 1) + Self::abs_val(row[j - 1] as int) }
    }

    pub open spec fn matrix_abs_sum(matrix: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0int }
        else { Self::matrix_abs_sum(matrix, i - 1) + Self::row_abs_sum(matrix[i - 1]@, matrix[i - 1].len() as int) }
    }

    pub open spec fn row_neg_count(row: Seq<i32>, j: int) -> int
        decreases j
    {
        if j <= 0 { 0int }
        else { Self::row_neg_count(row, j - 1) + if row[j - 1] < 0 { 1int } else { 0int } }
    }

    pub open spec fn matrix_neg_count(matrix: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0int }
        else { Self::matrix_neg_count(matrix, i - 1) + Self::row_neg_count(matrix[i - 1]@, matrix[i - 1].len() as int) }
    }

    pub open spec fn row_min_abs(row: Seq<i32>, j: int) -> int
        decreases j
    {
        if j <= 0 { 100_001int }
        else { Self::spec_min(Self::row_min_abs(row, j - 1), Self::abs_val(row[j - 1] as int)) }
    }

    pub open spec fn matrix_min_abs(matrix: Seq<Vec<i32>>, i: int) -> int
        decreases i
    {
        if i <= 0 { 100_001int }
        else { Self::spec_min(Self::matrix_min_abs(matrix, i - 1), Self::row_min_abs(matrix[i - 1]@, matrix[i - 1].len() as int)) }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn max_matrix_sum(matrix: Vec<Vec<i32>>) -> (result: i64)
        requires
            2 <= matrix.len() <= 250,
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix.len(),
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==>
                -100_000 <= #[trigger] matrix[r][c] <= 100_000,
        ensures
            Self::matrix_neg_count(matrix@, matrix.len() as int) % 2 == 0 ==>
                result as int == Self::matrix_abs_sum(matrix@, matrix.len() as int),
            Self::matrix_neg_count(matrix@, matrix.len() as int) % 2 != 0 ==>
                result as int == Self::matrix_abs_sum(matrix@, matrix.len() as int)
                    - 2 * Self::matrix_min_abs(matrix@, matrix.len() as int),
    {
        let n = matrix.len();
        let mut total_sum: i64 = 0;
        let mut neg_count: i64 = 0;
        let mut min_abs: i64 = 100_001;
        let mut i = 0;
        while i < n {
            let mut j = 0;
            while j < n {
                let val = matrix[i][j] as i64;
                let abs_v = if val < 0 { -val } else { val };
                total_sum = total_sum + abs_v;
                if matrix[i][j] < 0 {
                    neg_count = neg_count + 1;
                }
                if abs_v < min_abs {
                    min_abs = abs_v;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        if neg_count % 2 == 0 {
            total_sum
        } else {
            total_sum - 2 * min_abs
        }
    }
}

}
