use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn suffix_merge_value(nums: Seq<i32>, start: int) -> int
        decreases nums.len() - start,
    {
        if start + 1 >= nums.len() {
            nums[start] as int
        } else {
            let right = Self::suffix_merge_value(nums, start + 1);
            if nums[start] as int <= right {
                nums[start] as int + right
            } else {
                nums[start] as int
            }
        }
    }

    pub fn max_array_value(nums: Vec<i32>) -> (ans: i64)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
        ensures
            ans as int == Self::suffix_merge_value(nums@, 0),
    {
    }
}

}
