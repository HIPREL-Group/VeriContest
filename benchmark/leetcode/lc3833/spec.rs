use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn range_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            Self::range_sum(nums, l, r - 1) + nums[r - 1] as int
        }
    }

    pub open spec fn dominant_at(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() - 1
            && nums[i] as int
                > Self::range_sum(nums, i + 1, nums.len() as int) / (nums.len() - i - 1)
    }

    pub open spec fn dominant_count_prefix(nums: Seq<i32>, k: nat) -> int
        recommends
            k <= nums.len(),
        decreases k,
    {
        if k == 0 {
            0
        } else {
            Self::dominant_count_prefix(nums, (k - 1) as nat)
                + if Self::dominant_at(nums, k as int - 1) { 1int } else { 0int }
        }
    }

    pub fn dominant_indices(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
        ensures
            res as int == Self::dominant_count_prefix(nums@, nums.len() as nat),
    {
    }
}

}
