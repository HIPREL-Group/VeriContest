use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn div_contrib(nums: Seq<i32>, d: int, idx: nat) -> nat {
        if (nums[idx as int] as int) % d == 0 { 1nat } else { 0nat }
    }

    pub open spec fn div_score_prefix(nums: Seq<i32>, d: int, k: nat) -> nat
        decreases k,
    {
        if k == 0 {
            0
        } else {
            Self::div_score_prefix(nums, d, (k - 1) as nat) + Self::div_contrib(nums, d, (k - 1) as nat)
        }
    }

    pub open spec fn div_score(nums: Seq<i32>, d: int) -> nat {
        Self::div_score_prefix(nums, d, nums.len() as nat)
    }

    pub open spec fn best_divisor_prefix(nums: Seq<i32>, divisors: Seq<i32>, k: nat) -> int
        decreases k,
    {
        if k == 0 {
            0
        } else if k == 1 {
            divisors[0] as int
        } else {
            let prev = Self::best_divisor_prefix(nums, divisors, (k - 1) as nat);
            let cur = divisors[k as int - 1] as int;
            let s_prev = Self::div_score(nums, prev);
            let s_cur = Self::div_score(nums, cur);
            if s_cur > s_prev || (s_cur == s_prev && cur < prev) {
                cur
            } else {
                prev
            }
        }
    }

    fn score(nums: &Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            d > 0,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result as nat == Self::div_score(nums@, d as int),
            0 <= result <= nums.len(),
    {
    }

    pub fn max_div_score(nums: Vec<i32>, divisors: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            1 <= divisors.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < divisors.len() ==> 1 <= #[trigger] divisors[i] <= 1_000_000_000,
        ensures
            result as int == Self::best_divisor_prefix(nums@, divisors@, divisors.len() as nat),
    {
    }
}

}
