use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn filter_lt(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] < pivot {
            Self::filter_lt(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_lt(s, n - 1, pivot)
        }
    }

    pub open spec fn filter_eq(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] == pivot {
            Self::filter_eq(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_eq(s, n - 1, pivot)
        }
    }

    pub open spec fn filter_gt(s: Seq<i32>, n: int, pivot: i32) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] > pivot {
            Self::filter_gt(s, n - 1, pivot).push(s[n - 1])
        } else {
            Self::filter_gt(s, n - 1, pivot)
        }
    }

    pub fn pivot_array(nums: Vec<i32>, pivot: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
            exists |i: int| 0 <= i < nums.len() && nums[i] == pivot,
        ensures
            result.len() == nums.len(),
            result@ == Self::filter_lt(nums@, nums.len() as int, pivot)
                + Self::filter_eq(nums@, nums.len() as int, pivot)
                + Self::filter_gt(nums@, nums.len() as int, pivot),
    {
    }
}

}
