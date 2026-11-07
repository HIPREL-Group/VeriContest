use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_toeplitz(matrix: Seq<Vec<i32>>) -> bool {
    forall |i: int, j: int|
        1 <= i < matrix.len() && 1 <= j < matrix[0].len() ==> #[trigger] matrix[i][j] == matrix[i - 1][j - 1]
}

impl Solution {
    pub fn is_toeplitz_matrix(matrix: Vec<Vec<i32>>) -> (result: bool)
        requires
            1 <= matrix.len() <= 20,
            forall |i: int| 0 <= i < matrix.len() ==> 1 <= #[trigger] matrix[i].len() <= 20,
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[0].len() ==> 0 <= #[trigger] matrix[i][j] <= 99,
        ensures
            result == is_toeplitz(matrix@),
    {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut i: usize = 1;
        while i < rows
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                1 <= rows <= 20,
                1 <= cols <= 20,
                1 <= i <= rows,
                forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] matrix[r].len() <= 20,
                forall |r: int| 0 <= r < rows ==> #[trigger] matrix[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] matrix[r][c] <= 99,
                forall |r: int, c: int|
                    1 <= r < i && 1 <= c < cols ==> #[trigger] matrix[r][c] == matrix[r - 1][c - 1],
            decreases rows - i,
        {
            let mut j: usize = 1;
            while j < cols
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    1 <= rows <= 20,
                    1 <= cols <= 20,
                    1 <= i < rows,
                    1 <= j <= cols,
                    forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] matrix[r].len() <= 20,
                    forall |r: int| 0 <= r < rows ==> #[trigger] matrix[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 0 <= #[trigger] matrix[r][c] <= 99,
                    forall |r: int, c: int|
                        1 <= r < i && 1 <= c < cols ==> #[trigger] matrix[r][c] == matrix[r - 1][c - 1],
                    forall |c: int|
                        1 <= c < j ==> #[trigger] matrix[i as int][c] == matrix[i as int - 1][c - 1],
                decreases cols - j,
            {
                proof {
                    assert(1 <= i);
                    assert(i < rows);
                    assert(1 <= j);
                    assert(j < cols);
                    assert(matrix[i as int].len() == cols);
                    assert(matrix[i as int - 1].len() == cols);
                }
                if matrix[i][j] != matrix[i - 1][j - 1] {
                    proof {
                        assert(!is_toeplitz(matrix@)) by {
                            if is_toeplitz(matrix@) {
                                assert(1 <= i);
                                assert(i < matrix.len());
                                assert(1 <= j);
                                assert(j < matrix[0].len());
                                assert(matrix[i as int][j as int] == matrix[i as int - 1][j as int - 1]);
                                assert(false);
                            }
                        };
                    }
                    return false;
                }
                j += 1;
            }
            proof {
                assert(j == cols);
                assert forall |r: int, c: int|
                    1 <= r < i as int + 1 && 1 <= c < cols implies #[trigger] matrix[r][c] == matrix[r - 1][c - 1] by {
                    if r < i as int {
                    } else {
                        assert(r == i as int);
                    }
                };
            }
            i += 1;
        }
        proof {
            assert(i == rows);
            assert(is_toeplitz(matrix@)) by {
                assert forall |r: int, c: int|
                    1 <= r < matrix.len() && 1 <= c < matrix[0].len() implies #[trigger] matrix[r][c] == matrix[r - 1][c - 1] by {
                    assert(r < i as int);
                };
            };
        }
        true
    }
}

}
