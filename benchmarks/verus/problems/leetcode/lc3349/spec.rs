use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_strictly_increasing(nums: Seq<i32>, start: int, len: int) -> bool {
        1 <= len
        && 0 <= start
        && start + len <= nums.len()
        && forall |j: int| start <= j < start + len - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn adjacent_pair_at(nums: Seq<i32>, a: int, k: int) -> bool {
        1 <= k
        && 0 <= a
        && a + 2 * k <= nums.len()
        && Self::is_strictly_increasing(nums, a, k)
        && Self::is_strictly_increasing(nums, a + k, k)
    }

    pub open spec fn has_adjacent_increasing_subarrays(nums: Seq<i32>, k: int) -> bool {
        1 <= k
        && exists |a: int| #[trigger] Self::adjacent_pair_at(nums, a, k)
    }

    pub fn has_increasing_subarrays(nums: Vec<i32>, k: i32) -> (result: bool)
        requires
            2 <= nums.len() <= 100,
            1 < 2 * k as int,
            2 * k as int <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result <==> Self::has_adjacent_increasing_subarrays(nums@, k as int),
    {
    }
}

}
