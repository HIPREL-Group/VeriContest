use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_min(ops: Seq<Vec<i32>>, len: int, init: i32, col: int) -> i32
        decreases len,
    {
        if len <= 0 {
            init
        } else {
            let prev = Self::col_min(ops, len - 1, init, col);
            let v = ops[len - 1]@[col];
            if v < prev { v } else { prev }
        }
    }

    pub fn max_count(m: i32, n: i32, ops: Vec<Vec<i32>>) -> (result: i32)
        requires
            m >= 1,
            n >= 1,
            m <= 40000,
            n <= 40000,
            0 <= ops@.len() <= 10_000,
            forall|i: int| 0 <= i < ops@.len() ==> (#[trigger] ops@[i]).len() == 2,
            forall|i: int| 0 <= i < ops@.len() ==>
                1 <= ops@[i]@[0] && ops@[i]@[0] <= m &&
                1 <= ops@[i]@[1] && ops@[i]@[1] <= n,
        ensures
            result == Self::col_min(ops@, ops@.len() as int, m, 0)
                * Self::col_min(ops@, ops@.len() as int, n, 1),
    {
    }
}

} 
