use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_sum(row: Seq<i32>, len: int) -> int
        decreases len
    {
        if len <= 0 {
            0
        } else {
            Self::row_sum(row, len - 1) + row[len - 1] as int
        }
    }

    pub open spec fn is_weaker(mat: Seq<Vec<i32>>, i: int, j: int) -> bool {
        let ci = Self::row_sum(mat[i]@, mat[i]@.len() as int);
        let cj = Self::row_sum(mat[j]@, mat[j]@.len() as int);
        ci < cj || (ci == cj && i < j)
    }

    pub fn k_weakest_rows(mat: Vec<Vec<i32>>, k: i32) -> (result: Vec<i32>)
        requires
            2 <= mat.len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> 2 <= (#[trigger] mat[i]).len() <= 100,
            forall |i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            1 <= k <= mat.len() as i32,
            forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len()
                ==> #[trigger] mat[i][j] == 0 || mat[i][j] == 1,
        ensures
            result.len() == k as int,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] result@[i] < mat.len() as i32,
            forall |i: int, j: int| 0 <= i < j < k as int ==> result@[i] != result@[j],
            forall |i: int, j: int| 0 <= i < j < k as int
                ==> Self::is_weaker(mat@, result@[i] as int, result@[j] as int),
            forall |p: int, r: int| 0 <= p < k as int && 0 <= r < mat.len()
                && Self::is_weaker(mat@, r, result@[p] as int)
                ==> (exists |q: int| 0 <= q < p && result@[q] == r as i32),
    {
    }
}

}
