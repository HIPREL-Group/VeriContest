use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn one_change_cap(a: int, b: int, k: int) -> int {
        Self::max2(Self::max2(a, b), Self::max2(k - a, k - b))
    }

    pub open spec fn pair_cost(nums: Seq<i32>, k: int, i: int, d: int) -> int {
        let n = nums.len() as int;
        let a = nums[i] as int;
        let b = nums[n - 1 - i] as int;
        let cur_diff = if a >= b { a - b } else { b - a };
        let b1 = if k >= a { k - a } else { 0 };
        let b2 = if k >= b { k - b } else { 0 };
        let cap = Self::max2(Self::max2(a, b), Self::max2(b1, b2));
        if cur_diff == d {
            0
        } else if d <= cap {
            1
        } else {
            2
        }
    }

    pub open spec fn total_cost_from(nums: Seq<i32>, k: int, d: int, i: int) -> int
        decreases if i < nums.len() / 2 { nums.len() / 2 - i } else { 0 },
    {
        let pairs = nums.len() as int / 2;
        if i >= pairs {
            0
        } else {
            Self::pair_cost(nums, k, i, d) + Self::total_cost_from(nums, k, d, i + 1)
        }
    }

    pub open spec fn total_cost(nums: Seq<i32>, k: int, d: int) -> int {
        Self::total_cost_from(nums, k, d, 0)
    }

    pub open spec fn min_changes_spec(nums: Seq<i32>, k: i32, result: int) -> bool {
        &&& 2 <= nums.len() <= 100000
        &&& nums.len() % 2 == 0
        &&& 0 <= k <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= k
        &&& exists |d: int|
            0 <= d <= k as int
            && result == Self::total_cost(nums, k as int, d)
            && forall |d2: int| 0 <= d2 <= k as int ==> result <= Self::total_cost(nums, k as int, d2)
    }

    pub fn min_changes(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            2 <= nums.len() <= 100000,
            nums.len() % 2 == 0,
            0 <= k <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= k,
        ensures
            Self::min_changes_spec(nums@, k, result as int),
    {
    }
}

}
