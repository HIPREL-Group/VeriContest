use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn alt_end_count(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else if end > nums.len() {
            Self::alt_end_count(nums, nums.len() as int)
        } else if end == 1 {
            1
        } else if nums[end - 1] != nums[end - 2] {
            Self::alt_end_count(nums, end - 1) + 1
        } else {
            1
        }
    }

    pub open spec fn alt_total_prefix(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else if end > nums.len() {
            Self::alt_total_prefix(nums, nums.len() as int)
        } else {
            Self::alt_total_prefix(nums, end - 1) + Self::alt_end_count(nums, end)
        }
    }

    pub open spec fn count_alternating_subarrays_spec(nums: Seq<i32>) -> int {
        Self::alt_total_prefix(nums, nums.len() as int)
    }

    pub fn count_alternating_subarrays(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || #[trigger] nums[i] == 1),
        ensures
            result as int == Self::count_alternating_subarrays_spec(nums@),
    {
        let n = nums.len();
        let mut result: i64 = 0;
        let mut cur: i64 = 0;
        let mut i: usize = 0;

        while i < n {
            if i == 0 {
                cur = 1;
            } else if nums[i] != nums[i - 1] {
                cur = cur + 1;
            } else {
                cur = 1;
            }
            result = result + cur;
            i = i + 1;
        }

        result
    }
}

}
