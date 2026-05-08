use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn all_equal(nums: Seq<i32>) -> bool {
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == nums[0]
    }

    pub fn min_operations(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        ensures
            0 <= res <= 1,
            Self::all_equal(nums@) ==> res == 0,
            !Self::all_equal(nums@) ==> res == 1,
    {
        let mut i: usize = 1;
        while i < nums.len() {
            if nums[i] != nums[0] {
                return 1;
            }
            i = i + 1;
        }
        0
    }
}

}
