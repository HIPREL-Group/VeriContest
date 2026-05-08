use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max_width_ramp(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50_000,
        ensures
            0 <= result <= nums.len() as int - 1,
            forall |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] ==> j - i <= result,
            result == 0 <==> (forall |i: int, j: int|
                0 <= i < j < nums.len() ==> nums[i] > nums[j]),
            result > 0 ==> (exists |i: int, j: int|
                0 <= i < j < nums.len() && nums[i] <= nums[j] && result == j - i),
    {
    }
}

}
