use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn is_array_special(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (forall |i: int| 0 <= i && i + 1 < nums.len() ==> (#[trigger] nums[i]) % 2 != nums[i + 1] % 2),
    {
        let n = nums.len();
        let mut i: usize = 1;
        while i < n {
            if nums[i - 1] % 2 == nums[i] % 2 {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

}
