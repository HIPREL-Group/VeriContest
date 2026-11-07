use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_max_index(nums: Seq<i32>, idx: int) -> bool {
        0 <= idx < nums.len() &&
        forall |j: int| 0 <= j < nums.len() ==> nums[idx] >= #[trigger] nums[j]
    }

    pub open spec fn is_dominant(nums: Seq<i32>, idx: int) -> bool {
        Self::is_max_index(nums, idx) &&
        forall |j: int| 0 <= j < nums.len() && j != idx ==> nums[idx] >= 2 * #[trigger] nums[j]
    }

    pub fn dominant_index(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
            exists |i: int| #![trigger nums[i]] 0 <= i < nums.len() &&
                forall |j: int| 0 <= j < nums.len() && j != i ==> nums[i] > #[trigger] nums[j],
        ensures
            -1 <= result < nums.len() as i32,
            result >= 0 ==> Self::is_dominant(nums@, result as int),
            result < 0 ==> forall |i: int| 0 <= i < nums.len() ==> !Self::is_dominant(nums@, i),
    {
    }
}

}
