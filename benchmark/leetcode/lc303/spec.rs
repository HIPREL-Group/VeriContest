use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_prefix_sum(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(nums, k - 1) + nums[k - 1] as int
    }
}

pub struct NumArray {
    pub nums: Vec<i32>,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> (result: Self)
        requires
            1 <= nums.len() <= 10000,
            forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
        ensures
            result.nums@ == nums@,
    {
    }

    pub fn sum_range(&self, left: i32, right: i32) -> (result: i32)
        requires
            1 <= self.nums@.len() <= 10000,
            forall |i: int| 0 <= i < self.nums@.len() ==> -100000 <= #[trigger] self.nums@[i] <= 100000,
            0 <= left <= right < self.nums@.len() as int,
        ensures
            result as int == spec_prefix_sum(self.nums@, right as int + 1) - spec_prefix_sum(self.nums@, left as int),
    {
    }
}

}
