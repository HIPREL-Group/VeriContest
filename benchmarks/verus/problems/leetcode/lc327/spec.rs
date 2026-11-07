use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_segment_sum(nums: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= nums.len(),
        decreases r - l,
    {
        if r <= l {
            0
        } else {
            Self::spec_segment_sum(nums, l, r - 1) + nums[r - 1] as int
        }
    }

    pub open spec fn spec_count_for_start(nums: Seq<i32>, lower: int, upper: int, i: int, end_excl: int) -> int
        recommends
            0 <= i < nums.len(),
            i <= end_excl <= nums.len(),
        decreases end_excl - i,
    {
        if end_excl <= i {
            0
        } else {
            Self::spec_count_for_start(nums, lower, upper, i, end_excl - 1)
                + if lower <= Self::spec_segment_sum(nums, i, end_excl) <= upper {
                    1int
                } else {
                    0int
                }
        }
    }

    pub open spec fn spec_count_starts_prefix(nums: Seq<i32>, lower: int, upper: int, upto_i: int) -> int
        recommends
            0 <= upto_i <= nums.len(),
        decreases upto_i,
    {
        if upto_i <= 0 {
            0
        } else {
            Self::spec_count_starts_prefix(nums, lower, upper, upto_i - 1)
                + Self::spec_count_for_start(nums, lower, upper, upto_i - 1, nums.len() as int)
        }
    }

    pub open spec fn spec_count_range_sum(nums: Seq<i32>, lower: int, upper: int) -> int
        recommends
            1 <= nums.len(),
    {
        Self::spec_count_starts_prefix(nums, lower, upper, nums.len() as int)
    }

    pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100000,
            forall|i: int| 0 <= i < nums.len() ==> -2147483648 <= #[trigger] nums[i] <= 2147483647,
            -100000 <= lower as int <= upper as int <= 100000,
            Self::spec_count_range_sum(nums@, lower as int, upper as int) <= i32::MAX,
        ensures
            res as int == Self::spec_count_range_sum(nums@, lower as int, upper as int),
    {
    }
}

}
