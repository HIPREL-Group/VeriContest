use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_k_distant(nums: Seq<i32>, key: int, k: int, i: int) -> bool {
    exists|j: int| 0 <= j < nums.len() && (i - j <= k && j - i <= k) && nums[j] as int == key
}

impl Solution {
    pub fn find_k_distant_indices(nums: Vec<i32>, key: i32, k: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() && nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] && nums[i] <= 1000,
            1 <= key && key <= 1000,
            exists |i: int| 0 <= i < nums.len() && nums[i] == key,
            1 <= k && k as int <= nums.len() as int,
        ensures
            forall |p: int| 0 <= p < result.len() ==> 0 <= #[trigger] result[p] < nums.len() as i32,
            forall |a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
            forall |p: int| 0 <= p < result.len() ==> is_k_distant(nums@, key as int, k as int, #[trigger] result[p] as int),
            forall |i: int| 0 <= i < nums@.len() && is_k_distant(nums@, key as int, k as int, i) ==>
                exists|p: int| 0 <= p < result.len() && #[trigger] result[p] as int == i,
    {
    }
}

}
