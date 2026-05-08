use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn find_closest_number(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            exists|idx: int| 0 <= idx < nums.len() && nums[idx] == res,
            forall|i: int|
                0 <= i < nums.len() ==> (if res >= 0 { res as int } else { -(res as int) })
                    <= (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) }),
            forall|i: int|
                0 <= i < nums.len() &&
                (if res >= 0 { res as int } else { -(res as int) })
                    == (if #[trigger] nums[i] >= 0 { nums[i] as int } else { -(nums[i] as int) })
                    ==> nums[i] <= res,
    {
    }
}

}
