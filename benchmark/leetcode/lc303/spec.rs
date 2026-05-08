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
    pub prefix: Vec<i64>,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> (result: Self)
        requires
            1 <= nums.len() <= 10000,
            forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
        ensures
            result.prefix@.len() == nums.len() + 1,
            result.prefix@[0] == 0,
            forall |i: int| 0 <= i < nums.len() ==>
                result.prefix@[i + 1] == result.prefix@[i] + nums[i] as int,
    {
    }

    pub fn sum_range(&self, left: i32, right: i32) -> (result: i32)
        requires
            self.prefix@.len() >= 1,
            0 <= left <= right < (self.prefix@.len() - 1) as int,
            forall |i: int| 0 <= i < self.prefix@.len() ==>
                -1_000_000_000 <= (#[trigger] self.prefix@[i]) <= 1_000_000_000,
        ensures
            result as int == self.prefix@[right as int + 1] - self.prefix@[left as int],
    {
    }
}

}
