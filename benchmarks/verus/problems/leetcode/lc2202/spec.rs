use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_max(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::prefix_max(nums, end - 1);
            let cur = nums[end - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn removable_count(nums: Seq<i32>, k: int) -> int {
        if k <= 1 {
            0
        } else if k - 1 <= nums.len() {
            k - 1
        } else {
            nums.len() as int
        }
    }

    pub open spec fn maximum_top_spec(nums: Seq<i32>, k: int) -> int {
        if k == 0 {
            nums[0] as int
        } else if nums.len() == 1 {
            if k % 2 == 1 { -1 } else { nums[0] as int }
        } else {
            let r = Self::removable_count(nums, k);
            let removed_best = Self::prefix_max(nums, r);
            let keep = if k < nums.len() { nums[k] as int } else { -1 };
            if removed_best >= keep { removed_best } else { keep }
        }
    }

    pub fn maximum_top(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            0 <= k <= 1_000_000_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result as int == Self::maximum_top_spec(nums@, k as int),
    {
        
    }
}

}
