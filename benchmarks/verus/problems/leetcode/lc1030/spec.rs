use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_spec(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn dist_spec(r: int, c: int, rc: int, cc: int) -> int {
        Self::abs_spec(r - rc) + Self::abs_spec(c - cc)
    }

    pub open spec fn cell_covered(result: Seq<Vec<i32>>, r: int, c: int) -> bool {
        exists|k: int| 0 <= k < result.len() && result[k][0] as int == r && result[k][1] as int == c
    }

    pub fn all_cells_dist_order(rows: i32, cols: i32, r_center: i32, c_center: i32) -> (result: Vec<Vec<i32>>)
        requires
            1 <= rows <= 100,
            1 <= cols <= 100,
            0 <= r_center < rows,
            0 <= c_center < cols,
        ensures
            result@.len() == rows as int * cols as int,
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                Self::dist_spec(
                    result@[i][0] as int, result@[i][1] as int,
                    r_center as int, c_center as int,
                ) <= Self::dist_spec(
                    result@[i + 1][0] as int, result@[i + 1][1] as int,
                    r_center as int, c_center as int,
                ),
            forall|r: int, c: int| 0 <= r < rows as int && 0 <= c < cols as int ==>
                (#[trigger] Self::cell_covered(result@, r, c)),
    {
    }
}

}
