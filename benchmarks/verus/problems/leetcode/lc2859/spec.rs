use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcount_steps(t: nat, rem: nat) -> nat
        decreases rem,
    {
        if rem == 0 {
            0
        } else {
            (t % 2) + Self::popcount_steps(t / 2, (rem - 1) as nat)
        }
    }

    pub open spec fn sum_selected_prefix(nums: Seq<i32>, k: int, upto: nat) -> int
        recommends
            upto <= nums.len(),
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::sum_selected_prefix(nums, k, (upto - 1) as nat)
                + if Self::popcount_steps((upto - 1) as nat, 10) as int == k {
                    nums[upto - 1] as int
                } else {
                    0
                }
        }
    }

    pub fn sum_indices_with_k_set_bits(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            0 <= k <= 10,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums@[i],
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums@[i] <= 100000,
        ensures
            result as int == (Self::sum_selected_prefix(nums@, k as int, nums.len() as nat) as i32) as int,
    {
    }
}

}
