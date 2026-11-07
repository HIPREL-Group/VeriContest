use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pickable(nums: Seq<i32>, cap: int, i: int) -> int {
        if nums[i] as int <= cap { 1 } else { 0 }
    }

    pub open spec fn max_pick_prefix(nums: Seq<i32>, cap: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n == 1 {
            Self::pickable(nums, cap, 0)
        } else {
            let skip = Self::max_pick_prefix(nums, cap, n - 1);
            let take = Self::max_pick_prefix(nums, cap, n - 2) + Self::pickable(nums, cap, n - 1);
            if take > skip { take } else { skip }
        }
    }

    pub open spec fn feasible_cap(nums: Seq<i32>, cap: int, k: int) -> bool {
        Self::max_pick_prefix(nums, cap, nums.len() as int) >= k
    }

    pub open spec fn max_elem_prefix(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            nums[0] as int
        } else {
            let p = Self::max_elem_prefix(nums, n - 1);
            let c = nums[n - 1] as int;
            if p >= c { p } else { c }
        }
    }

    pub open spec fn max_elem(nums: Seq<i32>) -> int {
        Self::max_elem_prefix(nums, nums.len() as int)
    }

    pub fn min_capability(nums: Vec<i32>, k: i32) -> (ans: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            1 <= k <= (nums.len() as int + 1) / 2,
        ensures
            1 <= ans <= Self::max_elem(nums@),
            Self::feasible_cap(nums@, ans as int, k as int),
            forall |x: int| 1 <= x < ans ==> !#[trigger] Self::feasible_cap(nums@, x, k as int),
    {
    }
}

}
