use vstd::prelude::*;
use vstd::arithmetic::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn search_matrix(matrix: Vec<Vec<i32>>, target: i32) -> (res: bool) 
        requires
            1 <= matrix.len() <= 100, 
            1 <= matrix[0].len() <= 100, 
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len()
                ==> -10_000 <= #[trigger] matrix[i][j] <= 10_000, 
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1 ==> 
                #[trigger] matrix[i][j] <= matrix[i][j + 1], 
            forall |i: int| 1 <= i < matrix.len() ==> 
                #[trigger] matrix[i][0] > matrix[i - 1][matrix[0].len() - 1],
            -10_000 <= target <= 10_000, 
        ensures
            res == (exists |i: int, j: int| 
                0 <= i < matrix.len() && 0 <= j < matrix[i].len() && matrix[i][j] == target),
    {
        
    }
}

}