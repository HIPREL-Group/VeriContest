use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn transpose(matrix: Vec<Vec<i32>>) -> (res: Vec<Vec<i32>>)
        requires
            1 <= matrix.len() <= 1_000,
            1 <= matrix[0].len() <= 1_000,
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            matrix.len() * matrix[0].len() <= 100_000,
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -1_000_000_000 <= #[trigger] matrix[r][c] <= 1_000_000_000,
        ensures
            res.len() == matrix[0].len(),
            forall |c: int| 0 <= c < res.len() ==> #[trigger] res[c].len() == matrix.len(),
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[0].len() ==> #[trigger] res[c][r] == matrix[r][c],
    {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                1 <= rows <= 1_000,
                1 <= cols <= 1_000,
                rows * cols <= 100_000,
                forall |r: int| 0 <= r < rows ==> #[trigger] matrix[r].len() == cols,
                forall |r: int, cc: int| 0 <= r < rows && 0 <= cc < cols ==> -1_000_000_000 <= #[trigger] matrix[r][cc] <= 1_000_000_000,
                c <= cols,
                result.len() == c,
                forall |cc: int| 0 <= cc < c ==> #[trigger] result[cc].len() == rows,
                forall |r: int, cc: int| 0 <= r < rows && 0 <= cc < c ==> #[trigger] result[cc][r] == matrix[r][cc],
            decreases cols - c,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut r: usize = 0;
            while r < rows
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    1 <= rows <= 1_000,
                    1 <= cols <= 1_000,
                    rows * cols <= 100_000,
                    forall |rr: int| 0 <= rr < rows ==> #[trigger] matrix[rr].len() == cols,
                    forall |rr: int, cc: int| 0 <= rr < rows && 0 <= cc < cols ==> -1_000_000_000 <= #[trigger] matrix[rr][cc] <= 1_000_000_000,
                    c < cols,
                    r <= rows,
                    row.len() == r,
                    forall |rr: int| 0 <= rr < r ==> #[trigger] row[rr] == matrix[rr][c as int],
                decreases rows - r,
            {
                proof {
                    assert(matrix[r as int].len() == cols);
                }
                row.push(matrix[r][c]);
                r += 1;
            }
            result.push(row);
            c += 1;
        }
        result
    }
}

}
