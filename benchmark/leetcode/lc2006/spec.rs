use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff_is_k(a: i32, b: i32, k: i32) -> bool {
        a - b == k || b - a == k
    }

    pub open spec fn count_pairs_from(nums: Seq<i32>, k: i32, i: int, j: int) -> int
        decreases nums.len() - i, nums.len() - j
    {
        if i >= nums.len() {
            0
        } else if j >= nums.len() {
            Self::count_pairs_from(nums, k, i + 1, i + 2)
        } else {
            (if Self::abs_diff_is_k(nums[i], nums[j], k) { 1int } else { 0int })
                + Self::count_pairs_from(nums, k, i, j + 1)
        }
    }

    pub fn count_k_difference(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 99,
        ensures
            result == Self::count_pairs_from(nums@, k, 0, 1),
    {
    }
}

}
