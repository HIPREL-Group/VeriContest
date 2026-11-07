use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(nums: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else { nums[lo] as int + Self::sum_range(nums, lo + 1, hi) }
    }

    pub fn pivot_index(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == -1 || 0 <= result < nums.len(),
            result >= 0 ==> Self::sum_range(nums@, 0, result as int) == Self::sum_range(nums@, result as int + 1, nums.len() as int),
            result >= 0 ==> forall |j: int| 0 <= j < result as int ==>
                Self::sum_range(nums@, 0, j) != Self::sum_range(nums@, j + 1, nums.len() as int),
            result == -1 ==> forall |j: int| 0 <= j < nums.len() as int ==>
                Self::sum_range(nums@, 0, j) != Self::sum_range(nums@, j + 1, nums.len() as int),
    {
        let n = nums.len();
        let mut total: i32 = 0;
        let mut i: usize = 0;

        while i < n
        {
            total = total + nums[i];
            i = i + 1;
        }

        let mut left_sum: i32 = 0;
        i = 0;
        while i < n
        {
            if left_sum == total - left_sum - nums[i] {
                return i as i32;
            }
            left_sum = left_sum + nums[i];
            i = i + 1;
        }
        -1
    }
}

}
