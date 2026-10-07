use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_has_zero(matrix: Seq<Vec<i32>>, row: int) -> bool {
        exists |col: int| 0 <= col < matrix[row].len() && matrix[row][col] == 0
    }

    pub open spec fn col_has_zero(matrix: Seq<Vec<i32>>, col: int) -> bool {
        exists |row: int| 0 <= row < matrix.len() && col < matrix[row].len() && matrix[row][col] == 0
    }

    pub open spec fn should_zero(matrix: Seq<Vec<i32>>, row: int, col: int) -> bool {
        Self::row_has_zero(matrix, row) || Self::col_has_zero(matrix, col)
    }

    pub fn set_zeroes(matrix: &mut Vec<Vec<i32>>)
        requires
            1 <= (*old(matrix)).len() <= 200,
            1 <= (*old(matrix))[0].len() <= 200,
            forall |row: int| 0 <= row < (*old(matrix)).len() ==> #[trigger] (*old(matrix))[row].len() == (*old(matrix))[0].len(),
            forall |row: int, col: int|
                0 <= row < (*old(matrix)).len() && 0 <= col < (*old(matrix))[row].len() ==> i32::MIN <= #[trigger] (*old(matrix))[row][col] <= i32::MAX,
        ensures
            matrix@.len() == old(matrix)@.len(),
            forall |row: int| 0 <= row < matrix@.len() ==> #[trigger] matrix@[row].len() == old(matrix)@[row].len(),
            forall |row: int, col: int|
                0 <= row < matrix@.len() && 0 <= col < matrix@[row].len() ==> #[trigger] matrix@[row][col] == if Self::should_zero(old(matrix)@, row, col) {
                    0
                } else {
                    old(matrix)@[row][col]
                },
    {
    }
}

}
