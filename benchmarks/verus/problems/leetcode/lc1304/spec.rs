use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub fn sum_zero(n: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 1000,
        ensures
            result@.len() == n as int,
            Self::seq_sum(result@, result@.len() as int) == 0,
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
    {
    }
}

}
