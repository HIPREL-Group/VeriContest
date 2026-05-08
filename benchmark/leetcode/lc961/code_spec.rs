use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    pub open spec fn valid_input(nums: Seq<i32>) -> bool {
        4 <= nums.len() <= 10_000 &&
        nums.len() % 2 == 0 &&
        exists |k: int|
            0 <= k < nums.len() &&
            (forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000) &&
            Self::count_occurrences(nums, nums[k]) == nums.len() / 2 &&
            (forall |i: int| 0 <= i < nums.len() && nums[i] != nums[k] ==> #[trigger] Self::count_occurrences(nums, nums[i]) == 1)
    }

    pub fn repeated_n_times(nums: Vec<i32>) -> (res: i32)
        requires
            Self::valid_input(nums@),
        ensures
            Self::count_occurrences(nums@, res) == nums.len() / 2,
    {
        let n = nums.len();
        let mut i: usize = 2;

        while i < n
        {
            if nums[i] == nums[i - 1] {
                return nums[i];
            }
            if nums[i] == nums[i - 2] {
                return nums[i];
            }
            i += 1;
        }

        nums[0]
    }
}

}
