use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::window_sum(nums, start, len - 1) + nums[start + len - 1] as int
        }
    }

    pub fn get_averages(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            0 <= k <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==> (
                if i < k as int || i + k as int >= (nums.len() as int) {
                    #[trigger] result[i] == -1
                } else {
                    #[trigger] result[i] as int == Self::window_sum(nums@, i - k as int, 2 * k as int + 1) / (2 * k as int + 1)
                }
            ),
    {
    }
}

}
