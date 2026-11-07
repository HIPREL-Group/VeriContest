use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_digit_spec(n: nat) -> nat
        decreases n
    {
        if n < 10 {
            n
        } else {
            let prev = Self::max_digit_spec(n / 10);
            let d = n % 10;
            if d > prev { d } else { prev }
        }
    }

    pub open spec fn pair_value(nums: Seq<i32>, i: int, j: int) -> int {
        if Self::max_digit_spec(nums[i] as nat) == Self::max_digit_spec(nums[j] as nat) {
            nums[i] as int + nums[j] as int
        } else {
            -1
        }
    }

    pub open spec fn best_with_i_upto(nums: Seq<i32>, i: int, j_excl: int) -> int
        decreases if j_excl <= i + 1 { 0int } else { j_excl - i - 1 }
    {
        if j_excl <= i + 1 {
            -1
        } else {
            let prev = Self::best_with_i_upto(nums, i, j_excl - 1);
            let cur = Self::pair_value(nums, i, j_excl - 1);
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn best_prefix(nums: Seq<i32>, i_excl: int) -> int
        decreases if i_excl <= 0 { 0int } else { i_excl }
    {
        if i_excl <= 0 {
            -1
        } else {
            let prev = Self::best_prefix(nums, i_excl - 1);
            let cur = Self::best_with_i_upto(nums, i_excl - 1, nums.len() as int);
            if prev >= cur { prev } else { cur }
        }
    }

    pub fn max_sum(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
        ensures
            result as int == Self::best_prefix(nums@, nums.len() as int),
    {
    }
}

}
