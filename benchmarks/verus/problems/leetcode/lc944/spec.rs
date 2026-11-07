use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_inversion(strs: Seq<String>, row: int, col: int) -> bool {
        strs[row - 1]@[col] > strs[row]@[col]
    }

    pub open spec fn col_bad(strs: Seq<String>, col: int) -> bool {
        exists |row: int| 1 <= row < strs.len() && #[trigger] Self::col_inversion(strs, row, col)
    }

    pub open spec fn bad_cols_prefix(strs: Seq<String>, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0
        } else {
            Self::bad_cols_prefix(strs, cols - 1) + (if Self::col_bad(strs, cols - 1) { 1int } else { 0int })
        }
    }

    pub fn min_deletion_size(strs: Vec<String>) -> (res: i32)
        requires
            1 <= strs.len() <= 100,
            1 <= strs[0]@.len() <= 1000,
            forall |i: int| 0 <= i < strs.len() ==> #[trigger] strs[i]@.len() == strs[0]@.len(),
            forall |i: int, j: int| 0 <= i < strs.len() && 0 <= j < strs[i]@.len() ==>
                'a' <= #[trigger] strs[i]@[j] <= 'z',
        ensures
            0 <= res <= strs[0]@.len(),
            res as int == Self::bad_cols_prefix(strs@, strs[0]@.len() as int),
    {
    }
}

}
