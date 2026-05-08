use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_pair(nums: Seq<i32>, k: int, i: int, j: int) -> bool {
    0 <= i < j < nums.len()
    && nums[i] == nums[j]
    && (i * j) % k == 0
}

pub open spec fn count_inner(nums: Seq<i32>, k: int, i: int, j: int) -> int
    decreases j - i - 1,
{
    if j <= i + 1 {
        0
    } else {
        count_inner(nums, k, i, j - 1)
            + if is_valid_pair(nums, k, i, j - 1) { 1int } else { 0int }
    }
}

pub open spec fn count_all(nums: Seq<i32>, k: int, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        count_all(nums, k, i + 1) + count_inner(nums, k, i, nums.len() as int)
    }
}

impl Solution {
    pub fn count_pairs(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            res as int == count_all(nums@, k as int, 0),
    {
    }
}

} 
