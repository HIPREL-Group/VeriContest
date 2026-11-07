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

    fn max_elem_exec(nums: &Vec<i32>) -> (m: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            m as int == Self::max_elem(nums@),
    {
        let mut m = nums[0];
        let mut i: usize = 1;
        while i < nums.len() {
            if nums[i] > m {
                m = nums[i];
            }
            i = i + 1;
        }
        m
    }

    fn count_with_cap(nums: &Vec<i32>, cap: i32) -> (count: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            0 <= cap,
        ensures
            count as int == Self::max_pick_prefix(nums@, cap as int, nums.len() as int),
    {
        let mut prev2: i32 = 0;
        let mut prev1: i32 = if nums[0] <= cap { 1 } else { 0 };
        let mut i: usize = 1;
        while i < nums.len() {
            let can_take: i32 = if nums[i] <= cap { 1 } else { 0 };
            let take = prev2 + can_take;
            let curr = if take > prev1 { take } else { prev1 };
            prev2 = prev1;
            prev1 = curr;
            i = i + 1;
        }
        prev1
    }

    fn can_rob(nums: &Vec<i32>, cap: i32, k: i32) -> (ok: bool)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
            0 <= cap,
            1 <= k <= (nums.len() as int + 1) / 2,
        ensures
            ok == Self::feasible_cap(nums@, cap as int, k as int),
    {
        Self::count_with_cap(nums, cap) >= k
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
        let mut left: i32 = 1;
        let mut right: i32 = Self::max_elem_exec(&nums);
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_rob(&nums, mid, k) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}

}
