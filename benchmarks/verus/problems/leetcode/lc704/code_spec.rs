use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub fn search(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            -10_000 < target < 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 < #[trigger] nums[i] < 10_000,
            forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            -1 <= res < nums.len(),
            res == -1 ==> (forall |i: int| 0 <= i < nums.len() ==> nums[i] != target),
            res != -1 ==> nums[res as int] == target,
    {
        let mut i1: usize = 0;
        let mut i2: usize = nums.len() - 1;

        while i1 != i2
        {
            let ix = i1 + (i2 - i1) / 2;
            if nums[ix] < target {
                i1 = ix + 1;
            } else {
                i2 = ix;
            }
        }

        if nums[i1] != target {
            -1
        }
        else {
            i1 as i32
        }
    }

}

}
