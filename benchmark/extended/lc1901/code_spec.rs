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
        while i < rows {
            let mut j: usize = 0;
            while j < cols {
                if mat[i][j] > best_val {
                    best_row = i;
                    best_col = j;
                    best_val = mat[i][j];
                }
                j += 1;
            }
            i += 1;
        }

        let mut result = Vec::new();
        result.push(best_row as i32);
        result.push(best_col as i32);
        result
    }
}

}
