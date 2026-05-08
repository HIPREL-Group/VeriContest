use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn value_present(nums: Seq<i32>, left: int, right: int, v: nat) -> bool {
        exists |j: int| left <= j < right && nums[j] == v as i32
    }

    pub open spec fn count_distinct_upto(nums: Seq<i32>, left: int, right: int, upto: nat) -> nat
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::count_distinct_upto(nums, left, right, (upto - 1) as nat)
                + if Self::value_present(nums, left, right, upto) { 1nat } else { 0nat }
        }
    }

    pub open spec fn distinct_count(nums: Seq<i32>, left: int, right: int) -> nat {
        Self::count_distinct_upto(nums, left, right, 50)
    }

    pub open spec fn distinct_diff_spec(nums: Seq<i32>, i: int) -> int {
        Self::distinct_count(nums, 0, i + 1) as int
            - Self::distinct_count(nums, i + 1, nums.len() as int) as int
    }

    fn count_distinct(nums: &Vec<i32>, left: usize, right: usize) -> (result: i32)
        requires
            left <= right <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            result as nat == Self::distinct_count(nums@, left as int, right as int),
            0 <= result <= 50,
    {
    }

    pub fn distinct_difference_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] == Self::distinct_diff_spec(nums@, i),
    {
    }
}

}
