use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_sum(nums, n - 1) + nums[n - 1] as int
        }
    }

    pub open spec fn feasible_cap(nums: Seq<i32>, x: int) -> bool {
        forall |n: int| 1 <= n <= nums.len() ==> #[trigger] Self::prefix_sum(nums, n) <= x * n
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

    pub fn minimize_array_value(nums: Vec<i32>) -> (ans: i32)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
        ensures
            0 <= ans <= Self::max_elem(nums@),
            Self::feasible_cap(nums@, ans as int),
            forall |x: int| 0 <= x < ans ==> !#[trigger] Self::feasible_cap(nums@, x),
    {
    }
}

}
