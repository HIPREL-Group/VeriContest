use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value_prefix(nums: Seq<i32>, end: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value_prefix(nums, end - 1, v)
                + if nums[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn count_value(nums: Seq<i32>, v: int) -> int {
        Self::count_value_prefix(nums, nums.len() as int, v)
    }

    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sum_smallest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases 101 - v,
    {
        if k <= 0 || v > 100 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_smallest_from(nums, k - t, v + 1)
        }
    }

    pub open spec fn sum_largest_from(nums: Seq<i32>, k: int, v: int) -> int
        decreases v,
    {
        if k <= 0 || v < 1 {
            0
        } else {
            let c = Self::count_value(nums, v);
            let t = Self::min_int(k, c);
            t * v + Self::sum_largest_from(nums, k - t, v - 1)
        }
    }

    pub open spec fn sum_smallest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_smallest_from(nums, k, 1)
    }

    pub open spec fn sum_largest_k(nums: Seq<i32>, k: int) -> int {
        Self::sum_largest_from(nums, k, 100)
    }

    pub open spec fn abs_int(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub fn abs_difference(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= nums.len(),
        ensures
            res as int == Self::abs_int(Self::sum_largest_k(nums@, k as int) - Self::sum_smallest_k(nums@, k as int)),
    {
    }
}

} 
