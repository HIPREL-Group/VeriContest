use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    pub open spec fn array_element_sum(nums: Seq<i32>, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::array_element_sum(nums, idx - 1) + nums[idx - 1] as int
        }
    }

    pub open spec fn array_digit_sum(nums: Seq<i32>, idx: int) -> int
        decreases idx,
    {
        if idx <= 0 {
            0
        } else {
            Self::array_digit_sum(nums, idx - 1) + Self::digit_sum(nums[idx - 1] as int)
        }
    }

    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a > b { a - b } else { b - a }
    }

    pub fn difference_of_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 2000,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 2000,
        ensures
            result == Self::abs_diff(
                Self::array_element_sum(nums@, nums.len() as int), 
                Self::array_digit_sum(nums@, nums.len() as int)
            ),
    {
    }
}

}
