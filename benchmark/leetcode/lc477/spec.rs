use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn hamming_distance_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let ones = x % 2;
            let new_acc = acc + ones;
            Solution::hamming_distance_spec_helper(x / 2, new_acc)
        }
    }

    pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
        Solution::hamming_distance_spec_helper(xor_result, 0)
    }

    pub open spec fn total_hamming_distance_spec(nums: Seq<i32>, i: nat, j: nat, acc: nat) -> nat
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
            acc
        } else if j >= nums.len() {
            Solution::total_hamming_distance_spec(nums, i + 1, i + 2, acc)
        } else {
            let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
            let dist = Solution::hamming_distance_spec(xor_val);
            Solution::total_hamming_distance_spec(nums, i, j + 1, acc + dist)
        }
    }

    pub fn total_hamming_distance(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
            i32::MIN <= Solution::total_hamming_distance_spec(nums@, 0, 1, 0) <= i32::MAX,
        ensures
            res == Solution::total_hamming_distance_spec(nums@, 0, 1, 0),
    {
    }
}

} 
