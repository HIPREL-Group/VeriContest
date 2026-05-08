use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains_int(nums: Seq<i32>, value: int) -> bool {
        exists |i: int| 0 <= i < nums.len() && nums[i] as int == value
    }

    pub fn missing_multiple(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            result > 0,
            result as int % k as int == 0,
            !Self::contains_int(nums@, result as int),
            forall |q: int| q >= 1 && !Self::contains_int(nums@, #[trigger] (k as int * q)) ==> result as int <= k as int * q,
    {
    }
}

}
