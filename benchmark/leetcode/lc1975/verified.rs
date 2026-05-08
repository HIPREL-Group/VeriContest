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

    proof fn spec_min_assoc(a: int, b: int, c: int)
        ensures Self::spec_min(a, Self::spec_min(b, c)) == Self::spec_min(Self::spec_min(a, b), c)
    {}

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
        while i < n
            invariant
                2 <= n <= 250,
                n == matrix.len(),
                forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == n,
                forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==>
                    -100_000 <= #[trigger] matrix[r][c] <= 100_000,
                0 <= i <= n,
                total_sum as int == Self::matrix_abs_sum(matrix@, i as int),
                neg_count as int == Self::matrix_neg_count(matrix@, i as int),
                min_abs as int == Self::matrix_min_abs(matrix@, i as int),
                0 <= (total_sum as int) <= (i as int) * (n as int) * 100_000,
                0 <= (neg_count as int) <= (i as int) * (n as int),
                0 <= (min_abs as int) <= 100_001,
            decreases n - i
        {
            let mut j = 0;
            while j < n
                invariant
                    2 <= n <= 250,
                    n == matrix.len(),
                    forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == n,
                    forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==>
                        -100_000 <= #[trigger] matrix[r][c] <= 100_000,
                    0 <= i < n,
                    0 <= j <= n,
                    total_sum as int == Self::matrix_abs_sum(matrix@, i as int)
                        + Self::row_abs_sum(matrix[i as int]@, j as int),
                    neg_count as int == Self::matrix_neg_count(matrix@, i as int)
                        + Self::row_neg_count(matrix[i as int]@, j as int),
                    min_abs as int == Self::spec_min(
                        Self::matrix_min_abs(matrix@, i as int),
                        Self::row_min_abs(matrix[i as int]@, j as int)),
                    0 <= (total_sum as int) <= ((i as int) * (n as int) + (j as int)) * 100_000,
                    0 <= (neg_count as int) <= (i as int) * (n as int) + (j as int),
                    0 <= (min_abs as int) <= 100_001,
                decreases n - j
            {
                proof {
                    assert(i < matrix.len());
                    assert(matrix[i as int].len() == n);
                    assert(j < matrix[i as int].len());
                }
                let val = matrix[i][j] as i64;
                let abs_v = if val < 0 { -val } else { val };

                assert((total_sum as int) + (abs_v as int) <= 6_250_000_000)
                by(nonlinear_arith)
                    requires
                        0 <= total_sum as int,
                        (total_sum as int) <= ((i as int) * (n as int) + (j as int)) * 100_000,
                        0 <= abs_v as int,
                        (abs_v as int) <= 100_000,
                        0 <= i as int, (i as int) < 250,
                        0 <= n as int, (n as int) <= 250,
                        0 <= j as int, (j as int) < 250,
                {}

                total_sum = total_sum + abs_v;
                if matrix[i][j] < 0 {
                    assert((neg_count as int) < 62_500) by(nonlinear_arith)
                        requires
                            0 <= neg_count as int,
                            (neg_count as int) <= (i as int) * (n as int) + (j as int),
                            j < n,
                            i < n,
                            n <= 250,
                    {}
                    neg_count = neg_count + 1;
                }
                if abs_v < min_abs {
                    min_abs = abs_v;
                }

                proof {
                    assert(Self::row_abs_sum(matrix[i as int]@, (j + 1) as int)
                        == Self::row_abs_sum(matrix[i as int]@, j as int)
                            + Self::abs_val(matrix[i as int]@[j as int] as int));
                    assert(Self::row_neg_count(matrix[i as int]@, (j + 1) as int)
                        == Self::row_neg_count(matrix[i as int]@, j as int)
                            + if matrix[i as int]@[j as int] < 0 { 1int } else { 0int });
                    assert(Self::row_min_abs(matrix[i as int]@, (j + 1) as int)
                        == Self::spec_min(
                            Self::row_min_abs(matrix[i as int]@, j as int),
                            Self::abs_val(matrix[i as int]@[j as int] as int)));
                    Self::spec_min_assoc(
                        Self::matrix_min_abs(matrix@, i as int),
                        Self::row_min_abs(matrix[i as int]@, j as int),
                        Self::abs_val(matrix[i as int]@[j as int] as int));
                }

                assert(0 <= (total_sum as int)
                    <= ((i as int) * (n as int) + ((j + 1) as int)) * 100_000)
                by(nonlinear_arith)
                    requires
                        0 <= total_sum as int,
                        (total_sum as int)
                            <= ((i as int) * (n as int) + (j as int)) * 100_000 + 100_000,
                        0 <= j as int,
                        0 <= i as int,
                        0 <= n as int,
                {}

                j = j + 1;
            }

            proof {
                assert(j == n);
                assert(Self::matrix_abs_sum(matrix@, (i + 1) as int)
                    == Self::matrix_abs_sum(matrix@, i as int)
                        + Self::row_abs_sum(matrix[i as int]@, n as int));
                assert(Self::matrix_neg_count(matrix@, (i + 1) as int)
                    == Self::matrix_neg_count(matrix@, i as int)
                        + Self::row_neg_count(matrix[i as int]@, n as int));
                assert(Self::matrix_min_abs(matrix@, (i + 1) as int)
                    == Self::spec_min(
                        Self::matrix_min_abs(matrix@, i as int),
                        Self::row_min_abs(matrix[i as int]@, n as int)));
            }

            assert(0 <= (total_sum as int) <= (((i + 1) as int) * (n as int)) * 100_000)
            by(nonlinear_arith)
                requires
                    0 <= total_sum as int,
                    (total_sum as int) <= ((i as int) * (n as int) + (n as int)) * 100_000,
                    0 <= i as int,
                    0 <= n as int,
            {}
            assert(0 <= (neg_count as int) <= ((i + 1) as int) * (n as int))
            by(nonlinear_arith)
                requires
                    0 <= neg_count as int,
                    (neg_count as int) <= (i as int) * (n as int) + (n as int),
                    0 <= i as int,
                    0 <= n as int,
            {}

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
