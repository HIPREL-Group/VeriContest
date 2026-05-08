use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn xor_all_spec(nums: Seq<i32>, idx: int) -> i32
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            nums[idx] ^ Self::xor_all_spec(nums, idx + 1)
        }
    }

    pub open spec fn xor_all_nums_spec(nums1: Seq<i32>, nums2: Seq<i32>) -> i32 {
        let x1 = if nums2.len() % 2 == 1 { Self::xor_all_spec(nums1, 0) } else { 0 };
        let x2 = if nums1.len() % 2 == 1 { Self::xor_all_spec(nums2, 0) } else { 0 };
        x1 ^ x2
    }

    fn xor_all_exec(nums: &Vec<i32>, idx: usize) -> (res: i32)
        requires
            idx <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res == Self::xor_all_spec(nums@, idx as int),
        decreases nums.len() - idx,
    {
        if idx >= nums.len() {
            0
        } else {
            nums[idx] ^ Self::xor_all_exec(nums, idx + 1)
        }
    }

    pub fn xor_all_nums(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: i32)
        requires
            1 <= nums1.len() <= 100_000,
            1 <= nums2.len() <= 100_000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1_000_000_000,
            forall |j: int| 0 <= j < nums2.len() ==> 0 <= #[trigger] nums2[j] <= 1_000_000_000,
        ensures
            result == Self::xor_all_nums_spec(nums1@, nums2@),
    {
        let x1: i32 = if nums2.len() % 2 == 1 { Self::xor_all_exec(&nums1, 0) } else { 0 };
        let x2: i32 = if nums1.len() % 2 == 1 { Self::xor_all_exec(&nums2, 0) } else { 0 };
        x1 ^ x2
    }
}

}
