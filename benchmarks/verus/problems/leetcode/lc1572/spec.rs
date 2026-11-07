use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn diag_sum_spec(mat: Seq<Vec<i32>>, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else {
            let n = mat.len() as int;
            let i = k - 1;
            Self::diag_sum_spec(mat, k - 1) + mat[i][i] as int + (if i != n - 1 - i { mat[i][n - 1 - i] as int } else { 0 })
        }
    }

    pub fn diagonal_sum(mat: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= mat.len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat.len(),
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> 1 <= #[trigger] mat[i][j] <= 100,
        ensures
            result as int == Self::diag_sum_spec(mat@, mat@.len() as int),
    {

    }
}

}
