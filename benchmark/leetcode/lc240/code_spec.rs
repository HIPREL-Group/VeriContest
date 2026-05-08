use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn search_matrix(matrix: Vec<Vec<i32>>, target: i32) -> (res: bool) 
        requires 
            1 <= matrix.len() <= 300, 
            1 <= matrix[0].len() <= 300, 
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),  
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len()
                ==> -1_000_000_000 <= #[trigger] matrix[i][j] <= 1_000_000_000, 
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1 ==> 
                #[trigger] matrix[i][j] < matrix[i][j + 1], 
            forall |i: int, j: int| 0 <= j < matrix[0].len() && 0 <= i < matrix.len() - 1 ==>
                #[trigger] matrix[i][j] < matrix[i + 1][j], 
            -1_000_000_000 <= target <= 1_000_000_000, 
        ensures 
            res == (exists |i: int, j: int| 
                0 <= i < matrix.len() && 0 <= j < matrix[i].len() && matrix[i][j] == target),
    {
        let m = matrix.len() as i32 - 1;
        let n = matrix[0].len() as i32 - 1;

        let mut row = m;
        let mut col = 0;
        while row >= 0 && col <= n 
        {
            let current = matrix[row as usize][col as usize];
            if current == target {
                return true;
            } else if current < target {
                col += 1;
            } else {
                row -= 1;
            }
        }
        false
    }
}

}