use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn repeat_val(val: i32, count: int) -> Seq<i32>
        decreases count,
    {
        if count <= 0 {
            seq![]
        } else {
            Self::repeat_val(val, count - 1).push(val)
        }
    }

    pub open spec fn decompress_spec(nums: Seq<i32>, pair_idx: int) -> Seq<i32>
        decreases nums.len() - 2 * pair_idx,
    {
        if pair_idx >= nums.len() / 2 {
            seq![]
        } else {
            Self::repeat_val(nums[2 * pair_idx + 1], nums[2 * pair_idx] as int)
                + Self::decompress_spec(nums, pair_idx + 1)
        }
    }

    pub fn decompress_rl_elist(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 100,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result@ == Self::decompress_spec(nums@, 0),
    {
    }
}

} 
