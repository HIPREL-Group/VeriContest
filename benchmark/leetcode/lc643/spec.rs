use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(s: Seq<i32>, start: int, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            s[start] + Self::window_sum(s, start + 1, k - 1)
        }
    }

    pub fn find_max_average_core(nums: Vec<i32>, k: i32) -> (result: i64)
        requires
            nums.len() <= 100_000,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums@[i] <= 10_000,
        ensures
            forall |i: int| 0 <= i <= nums@.len() - (k as int) ==>
                Self::window_sum(nums@, i, k as int) <= result as int,
            exists |i: int| 0 <= i <= nums@.len() - (k as int)
                && result as int == Self::window_sum(nums@, i, k as int),
    {
    }
}

}
