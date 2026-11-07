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

    fn max_elem_exec(nums: &Vec<i32>) -> (m: i32)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
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

    fn can_make(nums: &Vec<i32>, x: i32) -> (ok: bool)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000000000,
            0 <= x,
        ensures
            ok == Self::feasible_cap(nums@, x as int),
    {
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            s = s + nums[i] as i64;
            let denom = i as i64 + 1;
            if (s + denom - 1) / denom > x as i64 {
                return false;
            }
            i = i + 1;
        }
        true
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
        let mut left: i32 = 0;
        let mut right: i32 = Self::max_elem_exec(&nums);
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_make(&nums, mid) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}

}
