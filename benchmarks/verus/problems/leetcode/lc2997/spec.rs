use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_prefix(nums: Seq<i32>, len: int) -> i32
        recommends
            0 <= len <= nums.len(),
        decreases len,
    {
        if len <= 0 {
            0
        } else {
            Self::xor_prefix(nums, len - 1) ^ nums[len - 1]
        }
    }

    pub open spec fn xor_all(nums: Seq<i32>) -> i32 {
        Self::xor_prefix(nums, nums.len() as int)
    }

    pub open spec fn popcount_nonneg(x: int) -> int
        decreases if x > 0 { x } else { 0int },
    {
        if x <= 0 {
            0
        } else {
            (x % 2) + Self::popcount_nonneg(x / 2)
        }
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            0 <= k <= 1_000_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            result as int == Self::popcount_nonneg((Self::xor_all(nums@) ^ k) as int),
    {
    }
}

}
