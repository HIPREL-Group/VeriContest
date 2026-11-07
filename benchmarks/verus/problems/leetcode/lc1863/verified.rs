use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

pub open spec fn xor_sum_rec(nums: Seq<i32>, idx: int, current_xor: i32) -> int
    decreases nums.len() - idx,
{
    if idx >= nums.len() {
        current_xor as int
    } else {
        xor_sum_rec(nums, idx + 1, current_xor ^ nums[idx])
        + xor_sum_rec(nums, idx + 1, current_xor)
    }
}

proof fn lemma_pow2_positive(n: int)
    ensures pow2(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow2_positive(n - 1);
    }
}

proof fn lemma_pow2_monotone(a: int, b: int)
    requires 0 <= a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b - a,
{
    if a < b {
        lemma_pow2_monotone(a, b - 1);
        lemma_pow2_positive(b - 1);
    }
}

proof fn lemma_xor_bound(a: i32, b: i32)
    requires
        0 <= a <= 31,
        0 <= b <= 20,
    ensures
        0 <= (a ^ b) <= 31,
{
    assert(0 <= a ^ b <= 31) by(bit_vector)
        requires 0 <= a <= 31i32, 0 <= b <= 20i32;
}

impl Solution {
    pub fn subset_xor_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 12,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20,
        ensures
            result as int == xor_sum_rec(nums@, 0, 0i32),
    {
        Self::dfs(&nums, 0, 0)
    }

    fn dfs(nums: &Vec<i32>, idx: usize, current_xor: i32) -> (result: i32)
        requires
            idx <= nums.len() <= 12,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20,
            0 <= current_xor <= 31,
        ensures
            result as int == xor_sum_rec(nums@, idx as int, current_xor),
            0 <= result as int <= 31 * pow2((nums.len() - idx) as int),
        decreases nums.len() - idx,
    {
        if idx == nums.len() {
            return current_xor;
        }
        proof { lemma_xor_bound(current_xor, nums[idx as int]); }
        let include = Self::dfs(nums, idx + 1, current_xor ^ nums[idx]);
        let exclude = Self::dfs(nums, idx + 1, current_xor);
        proof {
            assert(pow2((nums.len() - idx) as int) == 2 * pow2((nums.len() - idx - 1) as int));
            lemma_pow2_monotone((nums.len() - idx) as int, 12);
            reveal_with_fuel(pow2, 14);
            assert(pow2(12) == 4096);
        }
        include + exclude
    }
}

}
