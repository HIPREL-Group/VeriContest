use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_triplet(nums: Seq<i32>, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < j < k < nums.len()
        &&& nums[i] < nums[j]
        &&& nums[k] < nums[j]
    }

    pub open spec fn triplet_sum(nums: Seq<i32>, i: int, j: int, k: int) -> int {
        nums[i] as int + nums[j] as int + nums[k] as int
    }

    pub fn minimum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
        ensures
            result == -1 ==> forall |i: int, j: int, k: int|
                !Self::is_mountain_triplet(nums@, i, j, k),
            result != -1 ==> exists |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                && result as int == Self::triplet_sum(nums@, i, j, k),
            result != -1 ==> forall |i: int, j: int, k: int|
                Self::is_mountain_triplet(nums@, i, j, k)
                ==> result as int <= Self::triplet_sum(nums@, i, j, k),
    {
    }
}

}
