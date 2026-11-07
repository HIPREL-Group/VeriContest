use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn prefix_xor(nums: Seq<i32>, len: int) -> i32
    decreases len,
{
    if len <= 0 {
        0i32
    } else {
        prefix_xor(nums, len - 1) ^ nums[len - 1]
    }
}

pub open spec fn mask_for(mb: i32) -> i32 {
    !(!0i32 << (mb as u32))
}

impl Solution {
    pub fn get_maximum_xor(nums: Vec<i32>, maximum_bit: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100_000,
            1 <= maximum_bit <= 20,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= mask_for(maximum_bit),
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==>
                0 <= #[trigger] result[i] <= mask_for(maximum_bit),
            forall |i: int| 0 <= i < result.len() ==>
                prefix_xor(nums@, (nums@.len() - i) as int) ^ #[trigger] result[i]
                    == mask_for(maximum_bit),
    {
    }
}

}
