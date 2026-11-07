use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn even_or_prefix(nums: Seq<i32>, k: int) -> i32
        recommends
            0 <= k <= nums.len(),
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            let prev = Self::even_or_prefix(nums, k - 1);
            if nums[k - 1] % 2 == 0 {
                prev | nums[k - 1]
            } else {
                prev
            }
        }
    }

    pub fn even_number_bitwise_o_rs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == Self::even_or_prefix(nums@, nums.len() as int),
    {
    }
}

}
