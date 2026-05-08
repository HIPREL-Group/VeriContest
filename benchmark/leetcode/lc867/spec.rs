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
    }
}

}
