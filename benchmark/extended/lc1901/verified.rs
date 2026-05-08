use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_peak_grid(mat: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= mat.len() <= 500,
            forall |i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 500,
            forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 100_000,
            forall |i: int, j: int|
                0 <= i && i + 1 < mat.len() && 0 <= j < mat[0].len() ==> #[trigger] mat[i][j] != mat[i + 1][j],
            forall |i: int, j: int|
                0 <= i < mat.len() && 0 <= j && j + 1 < mat[0].len() ==> #[trigger] mat[i][j] != mat[i][j + 1],
        ensures
            result.len() == 2,
            0 <= result[0] < mat.len() as i32,
            0 <= result[1] < mat[0].len() as i32,
            result[0] > 0 ==> mat[result[0] as int][result[1] as int] > mat[result[0] as int - 1][result[1] as int],
            result[0] + 1 < mat.len() as i32 ==> mat[result[0] as int][result[1] as int] > mat[result[0] as int + 1][result[1] as int],
            result[1] > 0 ==> mat[result[0] as int][result[1] as int] > mat[result[0] as int][result[1] as int - 1],
            result[1] + 1 < mat[0].len() as i32 ==> mat[result[0] as int][result[1] as int] > mat[result[0] as int][result[1] as int + 1],
    {
        let rows = mat.len();
        let cols = mat[0].len();
        let mut best_row: usize = 0;
        let mut best_col: usize = 0;
        let mut best_val = mat[0][0];

        let mut i: usize = 0;
        while i < rows
            invariant
                rows == mat.len(),
                cols == mat[0].len(),
                1 <= rows <= 500,
                1 <= cols <= 500,
                0 <= i <= rows,
                0 <= best_row < rows,
                0 <= best_col < cols,
                best_col < mat[best_row as int].len(),
                best_val == mat[best_row as int][best_col as int],
                forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] mat[r].len() <= 500,
                forall |r: int| 0 <= r < rows ==> #[trigger] mat[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 1 <= #[trigger] mat[r][c] <= 100_000,
                forall |r: int, c: int|
                    0 <= r && r + 1 < rows && 0 <= c < cols ==> #[trigger] mat[r][c] != mat[r + 1][c],
                forall |r: int, c: int|
                    0 <= r < rows && 0 <= c && c + 1 < cols ==> #[trigger] mat[r][c] != mat[r][c + 1],
                forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==> mat[r][c] <= best_val,
            decreases rows - i,
        {
            let mut j: usize = 0;
            while j < cols
                invariant
                    rows == mat.len(),
                    cols == mat[0].len(),
                    1 <= rows <= 500,
                    1 <= cols <= 500,
                    0 <= i < rows,
                    0 <= j <= cols,
                    0 <= best_row < rows,
                    0 <= best_col < cols,
                    best_col < mat[best_row as int].len(),
                    best_val == mat[best_row as int][best_col as int],
                    forall |r: int| 0 <= r < rows ==> 1 <= #[trigger] mat[r].len() <= 500,
                    forall |r: int| 0 <= r < rows ==> #[trigger] mat[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> 1 <= #[trigger] mat[r][c] <= 100_000,
                    forall |r: int, c: int|
                        0 <= r && r + 1 < rows && 0 <= c < cols ==> #[trigger] mat[r][c] != mat[r + 1][c],
                    forall |r: int, c: int|
                        0 <= r < rows && 0 <= c && c + 1 < cols ==> #[trigger] mat[r][c] != mat[r][c + 1],
                    forall |r: int, c: int| 0 <= r < i && 0 <= c < cols ==> mat[r][c] <= best_val,
                    forall |c: int| 0 <= c < j ==> #[trigger] mat[i as int][c] <= best_val,
                decreases cols - j,
            {
                proof {
                    assert(i < rows);
                    assert(j < cols);
                    assert(mat[i as int].len() == cols);
                    assert(j < mat[i as int].len());
                    assert(best_row < rows);
                    assert(mat[best_row as int].len() == cols);
                    assert(best_col < mat[best_row as int].len());
                }
                let old_best = best_val;
                if mat[i][j] > best_val {
                    best_row = i;
                    best_col = j;
                    best_val = mat[i][j];
                    proof {
                        assert(old_best < best_val);
                        assert(best_row == i);
                        assert(best_col == j);
                        assert(best_col < mat[best_row as int].len());
                        assert forall |r: int, c: int| 0 <= r < i && 0 <= c < cols implies mat[r][c] <= best_val by {
                            assert(mat[r][c] <= old_best);
                        };
                        assert forall |c: int| 0 <= c < j implies #[trigger] mat[i as int][c] <= best_val by {
                            assert(mat[i as int][c] <= old_best);
                        };
                    }
                } else {
                    proof {
                        assert(mat[i as int][j as int] <= best_val);
                    }
                }
                j += 1;
            }
            proof {
                assert(j == cols);
                assert forall |r: int, c: int| 0 <= r < i + 1 && 0 <= c < cols implies mat[r][c] <= best_val by {
                    if r < i {
                    } else {
                        assert(r == i);
                    }
                };
            }
            i += 1;
        }

        proof {
            assert(i == rows);
            assert forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols implies mat[r][c] <= best_val by {
                assert(r < i);
            };
        }

        let mut result = Vec::new();
        result.push(best_row as i32);
        result.push(best_col as i32);

        proof {
            if best_row > 0 {
                assert(mat[(best_row - 1) as int][best_col as int] <= best_val);
                assert(mat[(best_row - 1) as int][best_col as int] != mat[best_row as int][best_col as int]);
                assert(best_val == mat[best_row as int][best_col as int]);
                assert(mat[(best_row - 1) as int][best_col as int] < best_val);
            }
            if best_row + 1 < rows {
                assert(mat[(best_row + 1) as int][best_col as int] <= best_val);
                assert(mat[best_row as int][best_col as int] != mat[(best_row + 1) as int][best_col as int]);
                assert(best_val == mat[best_row as int][best_col as int]);
                assert(mat[(best_row + 1) as int][best_col as int] < best_val);
            }
            if best_col > 0 {
                assert(mat[best_row as int][(best_col - 1) as int] <= best_val);
                assert(mat[best_row as int][(best_col - 1) as int] != mat[best_row as int][best_col as int]);
                assert(best_val == mat[best_row as int][best_col as int]);
                assert(mat[best_row as int][(best_col - 1) as int] < best_val);
            }
            if best_col + 1 < cols {
                assert(mat[best_row as int][(best_col + 1) as int] <= best_val);
                assert(mat[best_row as int][best_col as int] != mat[best_row as int][(best_col + 1) as int]);
                assert(best_val == mat[best_row as int][best_col as int]);
                assert(mat[best_row as int][(best_col + 1) as int] < best_val);
            }
        }

        result
    }
}

}
