use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_contains(nums: Seq<i32>, k: i32) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] == k
    }

    pub open spec fn is_disappeared(nums: Seq<i32>, k: i32) -> bool {
        1 <= k <= nums.len() && !Self::seq_contains(nums, k)
    }

    pub fn find_disappeared_numbers(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
        ensures
            forall|i: int| 0 <= i < result.len() ==> #[trigger] Self::is_disappeared(nums@, result[i]),
            forall|k: int| 1 <= k <= nums.len() && Self::is_disappeared(nums@, k as i32) ==> #[trigger] Self::seq_contains(result@, k as i32),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] < #[trigger] result[j],
    {
    }
}

} 
