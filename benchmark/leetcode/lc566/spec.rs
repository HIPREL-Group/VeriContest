use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn matrix_reshape(mat: Vec<Vec<i32>>, r: i32, c: i32) -> (res: Vec<Vec<i32>>)
        requires
            1 <= mat.len() <= 100,
            1 <= mat[0].len() <= 100,
            1 <= r <= 300,
            1 <= c <= 300,
            forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == mat[0].len(),
            forall |i:int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==> -1_000 <= #[trigger] mat[i][j] <= 1_000, 
            mat.len() * mat[0].len() <= usize::MAX,
            r * c <= usize::MAX,
        ensures
            ({
                let m = mat.len();
                let n = mat[0].len();
                if m * n != r as usize * c as usize {
                    res@ =~= mat@
                } else {
                    res.len() == r as int
                    && (forall |i: int| 0 <= i < r ==> #[trigger] res[i].len() == c as int)
                    && (forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                        res[((i * n + j) / c as int) as int][((i * n + j) % c as int) as int] == mat[i][j])
                }
            }),
    {
        
    }
}

}