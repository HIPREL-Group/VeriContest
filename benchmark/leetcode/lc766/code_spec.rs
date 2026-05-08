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
        {
            let mut j: usize = 1;
            while j < cols
            {
                if matrix[i][j] != matrix[i - 1][j - 1] {
                    return false;
                }
                j += 1;
            }
            i += 1;
        }
        true
    }
}

}
