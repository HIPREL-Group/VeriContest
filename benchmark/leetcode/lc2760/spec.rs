use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn can_extend(nums: Seq<i32>, threshold: int, k: int) -> bool
        recommends
            1 <= k < nums.len(),
    {
        nums[k] as int <= threshold && (nums[k] as int % 2) != (nums[k - 1] as int % 2)
    }

    pub open spec fn greedy_len_k(nums: Seq<i32>, threshold: int, i: int, k: int) -> int
        recommends
            0 <= i < nums.len(),
            0 <= k <= nums.len() - i - 1,
        decreases k,
    {
        if k <= 0 {
            if nums[i] as int % 2 == 0 && nums[i] as int <= threshold { 1int } else { 0int }
        } else {
            let prev = Self::greedy_len_k(nums, threshold, i, k - 1);
            let idx = i + k;
            if prev == k && Self::can_extend(nums, threshold, idx) {
                prev + 1int
            } else {
                prev
            }
        }
    }

    pub open spec fn start_len(nums: Seq<i32>, threshold: int, i: int) -> int
        recommends
            0 <= i < nums.len(),
    {
        Self::greedy_len_k(nums, threshold, i, nums.len() - i - 1)
    }

    pub open spec fn best_prefix(nums: Seq<i32>, threshold: int, upto: int) -> int
        recommends
            0 <= upto <= nums.len(),
        decreases upto,
    {
        if upto <= 0 {
            0
        } else {
            let s = upto - 1;
            let prev = Self::best_prefix(nums, threshold, upto - 1);
            let cur = Self::start_len(nums, threshold, s);
            if cur > prev { cur } else { prev }
        }
    }

    pub fn longest_alternating_subarray(nums: Vec<i32>, threshold: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            1 <= threshold <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::best_prefix(nums@, threshold as int, nums.len() as int),
            0 <= result <= nums.len(),
    {
    }
}

}
