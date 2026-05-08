use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub proof fn lemma_column_sorted_implies_all_less(matrix: &Vec<Vec<i32>>, row: int, col: int, target: i32)
        requires
            0 <= row < matrix.len(),
            0 <= col < matrix[0].len(),
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int| 0 <= j < matrix[0].len() && 0 <= i < matrix.len() - 1 ==>
                #[trigger] matrix[i][j] < matrix[i + 1][j],
            matrix[row][col] < target,
        ensures
            forall |i: int| 0 <= i <= row ==> matrix[i][col] < target,
        decreases row,
    {
        assert forall |i: int| 0 <= i <= row implies matrix[i][col] < target by {
            if i == row {
                assert(matrix[i][col] == matrix[row][col]);
            } else if i == row - 1 {
                assert(matrix[i][col] < matrix[row][col]);
            } else {
                if row > 0 {
                    Self::lemma_column_sorted_implies_all_less(matrix, row - 1, col, target);
                }
            }
        }
    }

    pub proof fn lemma_row_sorted_implies_all_greater(matrix: &Vec<Vec<i32>>, row: int, col: int, target: i32)
        requires
            0 <= row < matrix.len(),
            0 <= col < matrix[row].len(),
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1 ==>
                #[trigger] matrix[i][j] < matrix[i][j + 1],
            matrix[row][col] > target,
        ensures
            forall |j: int| col <= j < matrix[row].len() ==> matrix[row][j] > target,
        decreases matrix[row].len() - col,
    {
        assert forall |j: int| col <= j < matrix[row].len() implies matrix[row][j] > target by {
            if j == col {
                assert(matrix[row][j] == matrix[row][col]);
            } else if j == col + 1 {
                assert(matrix[row][col] < matrix[row][j]);
            } else {
                if col + 1 < matrix[row].len() {
                    Self::lemma_row_sorted_implies_all_greater(matrix, row, col + 1, target);
                }
            }
        }
    }

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
            invariant
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
                m == matrix.len() - 1,
                n == matrix[0].len() - 1,
                -1 <= row <= m,
                0 <= col <= n + 1,
                forall |i: int, j: int| 
                    0 <= i < matrix.len() && 0 <= j < matrix[i].len() && i <= row && j < col
                    ==> matrix[i][j] < target,
                forall |i: int, j: int| 
                    0 <= i < matrix.len() && 0 <= j < matrix[i].len() && i > row && j >= col
                    ==> matrix[i][j] > target,
                forall |i: int, j: int| 
                    (0 <= i < matrix.len() && 0 <= j < matrix[0].len() && matrix[i][j] == target)
                    ==> (0 <= i <= row && col <= j < matrix[0].len()),
            decreases row + n - col + 1
        {
            assert(col < matrix[row as int].len());
            
            let current = matrix[row as usize][col as usize];
            if current == target {
                return true;
            } else if current < target {
                proof {
                    Self::lemma_column_sorted_implies_all_less(&matrix, row as int, col as int, target);
                }
                col += 1;
            } else {
                proof {
                    Self::lemma_row_sorted_implies_all_greater(&matrix, row as int, col as int, target);
                }
                row -= 1;
            }
        }
        false
    }
}

}