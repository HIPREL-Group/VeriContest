use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_val(nums: Seq<i32>, i: int, j: int) -> int {
        (nums[i] - 1) * (nums[j] - 1)
    }

    pub fn max_product(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 500,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            exists |i: int, j: int| 0 <= i < j < nums.len()
                && res == Self::product_val(nums@, i, j),
            forall |i: int, j: int| 0 <= i < j < nums.len()
                ==> Self::product_val(nums@, i, j) <= res,
    {
    }
}

} 
