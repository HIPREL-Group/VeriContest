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
        let n = mat.len();
        let mut sum: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == mat.len(),
                1 <= n <= 100,
                forall |ii: int| 0 <= ii < n ==> (#[trigger] mat[ii]).len() == n,
                forall |ii: int, jj: int| 0 <= ii < n && 0 <= jj < n ==> 1 <= #[trigger] mat[ii][jj] <= 100,
                sum as int == Self::diag_sum_spec(mat@, i as int),
                0 <= sum <= 200 * (i as int),
            decreases n - i,
        {
            sum = sum + mat[i][i];
            if i != n - 1 - i {
                sum = sum + mat[i][n - 1 - i];
            }
            i = i + 1;
        }

        sum
    }
}

}
