use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn good_index(nums: Seq<i32>, k: int, idx: int) -> bool {
        0 <= idx < nums.len()
        && 1 <= k
        && k <= idx
        && idx + k < nums.len()
        && (forall |j: int| idx - k <= j < idx - 1 ==> #[trigger] nums[j] >= nums[j + 1])
        && (forall |j: int| idx + 1 <= j < idx + k ==> #[trigger] nums[j] <= nums[j + 1])
    }

    pub fn good_indices(nums: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 100_000,
            1 <= k as int <= nums.len() as int / 2,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        ensures
            forall |i: int| 0 <= i < result@.len() ==>
                0 <= result@[i] < nums.len() as i32
                && Self::good_index(nums@, k as int, result@[i] as int),
            forall |idx: int| 0 <= idx < nums.len() && Self::good_index(nums@, k as int, idx)
                ==> #[trigger] result@.contains(idx as i32),
            forall |a: int, b: int| 0 <= a < b < result@.len() ==> result@[a] < result@[b],
    {
    }
}

}
