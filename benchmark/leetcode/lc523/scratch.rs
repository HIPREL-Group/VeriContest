use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

fn main() {}

verus! {
    pub open spec fn get_sum(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start, 
    {
        if start >= end {
            0
        } else {
            nums[start] + get_sum(nums, start + 1, end)
        }
    }

    proof fn lemma_get_sum_split(nums: Seq<i32>, a: int, b: int, c: int)
        requires 
            0 <= a <= b <= c <= nums.len()
        ensures
            get_sum(nums, a, c) == get_sum(nums, a, b) + get_sum(nums, b, c)
        decreases b - a
    {
        if a == b {
        } else {
            lemma_get_sum_split(nums, a + 1, b, c);
        }
    }
}
