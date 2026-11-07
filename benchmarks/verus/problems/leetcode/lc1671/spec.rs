use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_subseq(nums: Seq<i32>, indices: Seq<int>, peak: int) -> bool {
        &&& indices.len() >= 3
        &&& 0 < peak < indices.len() - 1
        &&& (forall |k: int| 0 <= k < indices.len() ==> 0 <= (#[trigger] indices[k]) < nums.len())
        &&& (forall |k: int| 0 <= k < peak ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) < nums[indices[k + 1]])
        &&& (forall |k: int| peak <= k < indices.len() - 1 ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) > nums[indices[k + 1]])
    }

    pub fn minimum_mountain_removals(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000i32,
            exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() as int
                && nums[a] < nums[b] && nums[b] > nums[c],
        ensures
            result >= 0,
            exists |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                && indices.len() == nums.len() - result as int,
            forall |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                ==> indices.len() <= nums.len() - result as int,
    {
    }
}

}
