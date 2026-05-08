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
        let rows = matrix.len() as i32;
        let cols = matrix[0].len() as i32;

        let mut start = 0;
        let mut end = rows * cols - 1;

        while start <= end 
        {
            let mid = start + (end - start) / 2;
            let mid_value = matrix[(mid / cols) as usize][(mid % cols) as usize];

            if mid_value == target {
                return true;
            } else if mid_value < target {
                start = mid + 1;
            } else {
                end = mid - 1;
            }
        }

        false
    }
}

}