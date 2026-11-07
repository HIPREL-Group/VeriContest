use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;


pub open spec fn spec_col_max(matrix: Seq<Vec<i32>>, j: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1int
    } else if (matrix[k - 1][j] as int) > spec_col_max(matrix, j, k - 1) {
        matrix[k - 1][j] as int
    } else {
        spec_col_max(matrix, j, k - 1)
    }
}


pub open spec fn spec_answer_element(matrix: Seq<Vec<i32>>, i: int, j: int) -> int {
    if matrix[i][j] == -1 {
        spec_col_max(matrix, j, matrix.len() as int)
    } else {
        matrix[i][j] as int
    }
}


pub open spec fn col_has_nonneg(matrix: Seq<Vec<i32>>, j: int, k: int) -> bool
    decreases k,
{
    if k <= 0 {
        false
    } else if matrix[k - 1][j] >= 0 {
        true
    } else {
        col_has_nonneg(matrix, j, k - 1)
    }
}

impl Solution {
    pub fn modified_matrix(matrix: Vec<Vec<i32>>) -> (answer: Vec<Vec<i32>>)
        requires
            2 <= matrix.len() <= 50,
            2 <= matrix[0].len() <= 50,
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int|
                0 <= i < matrix.len() && 0 <= j < matrix[i].len()
                ==> -1 <= #[trigger] matrix[i][j] <= 100,
            forall |j: int| 0 <= j < matrix[0].len()
                ==> #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int),
        ensures
            answer.len() == matrix.len(),
            forall |i: int| 0 <= i < answer.len()
                ==> #[trigger] answer[i].len() == matrix[0].len(),
            forall |i: int, j: int|
                0 <= i < answer.len() && 0 <= j < answer[i].len()
                ==> #[trigger] answer[i][j] as int == spec_answer_element(matrix@, i, j),
    {
        let m = matrix.len();
        let n = matrix[0].len();
        
        let mut col_max: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let mut mx: i32 = -1;
            let mut i: usize = 0;
            while i < m {
                if matrix[i][j] > mx {
                    mx = matrix[i][j];
                }
                i = i + 1;
            }
            col_max.push(mx);
            j = j + 1;
        }
        
        let mut answer: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                if matrix[i][j] == -1 {
                    row.push(col_max[j]);
                } else {
                    row.push(matrix[i][j]);
                }
                j = j + 1;
            }
            answer.push(row);
            i = i + 1;
        }
        answer
    }
}

} 
