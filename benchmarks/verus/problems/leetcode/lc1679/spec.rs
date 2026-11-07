use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_indices_distinct(left_idx: Seq<int>, right_idx: Seq<int>) -> bool {
    &&& forall |i: int, j: int| 0 <= i < j < left_idx.len()
        ==> left_idx[i] != left_idx[j]
    &&& forall |i: int, j: int| 0 <= i < j < right_idx.len()
        ==> right_idx[i] != right_idx[j]
    &&& forall |i: int, j: int| 0 <= i < left_idx.len() && 0 <= j < right_idx.len()
        ==> left_idx[i] != right_idx[j]
}

pub open spec fn is_valid_matching(nums: Seq<i32>, left_idx: Seq<int>, right_idx: Seq<int>, k: int) -> bool {
    &&& left_idx.len() == right_idx.len()
    &&& forall |i: int| 0 <= i < left_idx.len() ==> {
        &&& 0 <= left_idx[i] < nums.len()
        &&& 0 <= right_idx[i] < nums.len()
        &&& left_idx[i] != right_idx[i]
        &&& nums[left_idx[i]] as int + nums[right_idx[i]] as int == k
    }
    &&& all_indices_distinct(left_idx, right_idx)
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            0 <= result,
            2 * result as int <= nums.len() as int,
            exists |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                && left_idx.len() == result as int,
            forall |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                ==> left_idx.len() <= result as int,
    {
    }
}

}
