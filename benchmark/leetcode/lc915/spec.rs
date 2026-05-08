use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_partition(nums: Seq<i32>, k: int) -> bool {
        1 <= k < nums.len()
        && (forall |a: int, b: int| #![trigger nums[a], nums[b]]
            0 <= a < k && k <= b < nums.len() ==> nums[a] <= nums[b])
    }

    pub fn partition_disjoint(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
            exists |k: int| Self::valid_partition(nums@, k),
        ensures
            1 <= result as int,
            (result as int) < nums.len() as int,
            Self::valid_partition(nums@, result as int),
            forall |k: int| 1 <= k && k < result as int ==> !Self::valid_partition(nums@, k),
    {
    }
}

}
