use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn imin(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sub_or(nums: Seq<i32>, start: int, end: int) -> i32
        decreases end - start,
    {
        if end <= start {
            0i32
        } else {
            Self::sub_or(nums, start, end - 1) | nums[end - 1]
        }
    }

    pub open spec fn min_len_start_upto(nums: Seq<i32>, k: i32, start: int, upto: int) -> int
        decreases upto - start,
    {
        if upto <= start {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_start_upto(nums, k, start, upto - 1);
            let cand = if Self::sub_or(nums, start, upto) >= k {
                upto - start
            } else {
                nums.len() as int + 1
            };
            Self::imin(prev, cand)
        }
    }

    pub open spec fn min_len_prefix(nums: Seq<i32>, k: i32, processed: int) -> int
        decreases processed,
    {
        if processed <= 0 {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_prefix(nums, k, processed - 1);
            let cur = Self::min_len_start_upto(nums, k, processed - 1, nums.len() as int);
            Self::imin(prev, cur)
        }
    }

    pub open spec fn minimum_subarray_length_spec(nums: Seq<i32>, k: i32) -> int {
        let best = Self::min_len_prefix(nums, k, nums.len() as int);
        if best <= nums.len() as int { best } else { -1 }
    }

    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 1_000_000_000,
        ensures
            result as int == Self::minimum_subarray_length_spec(nums@, k),
    {
    }
}

}
