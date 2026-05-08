use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, target: int, idx: int) -> int
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            (if nums[idx] as int == target { 1int } else { 0int })
                + Self::count_value(nums, target, idx + 1)
        }
    }

    pub open spec fn all_single(nums: Seq<i32>, v: int, n: int) -> bool
        decreases if v <= n { n - v + 1 } else { 0int },
    {
        if v >= n {
            true
        } else {
            Self::count_value(nums, v, 0) == 1 && Self::all_single(nums, v + 1, n)
        }
    }

    pub open spec fn is_good_spec(nums: Seq<i32>) -> bool {
        if nums.len() < 2 {
            false
        } else {
            let n = nums.len() - 1;
            Self::count_value(nums, n, 0) == 2 && Self::all_single(nums, 1, n)
        }
    }

    pub fn is_good(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 200,
        ensures
            result == Self::is_good_spec(nums@),
    {
    }
}

}
