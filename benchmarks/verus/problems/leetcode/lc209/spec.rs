use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_range(s: Seq<i32>, start: int, end: int) -> int
        recommends
            0 <= start <= end <= s.len(),
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            s[start] as int + Self::sum_range(s, start + 1, end)
        }
    }

    pub open spec fn sum_len(s: Seq<i32>, start: int, len: int) -> int {
        Self::sum_range(s, start, start + len)
    }

    pub fn min_sub_array_len(target: i32, nums: Vec<i32>) -> (k: i32)
        requires
            1 <= target <= 1_000_000_000,
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            0 <= k <= nums.len(),
            k == 0 ==> forall |i: int, len: int|
                0 <= i && 1 <= len && i + len <= nums.len() as int ==>
                #[trigger] Self::sum_len(nums@, i, len) < target as int,
            k > 0 ==> exists |i: int|
                0 <= i && i + k as int <= nums.len() as int &&
                #[trigger] Self::sum_len(nums@, i, k as int) >= target as int,
            k > 0 ==> forall |i: int, len: int|
                0 <= i && 1 <= len < k as int && i + len <= nums.len() as int ==>
                #[trigger] Self::sum_len(nums@, i, len) < target as int,
    {
    }
}

}
