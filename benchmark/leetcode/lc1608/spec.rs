use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_geq(nums: Seq<i32>, x: int) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else if nums.last() >= x {
        1 + count_geq(nums.drop_last(), x)
    } else {
        count_geq(nums.drop_last(), x)
    }
}

impl Solution {
    pub fn special_array(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result == -1 || 1 <= result <= nums.len(),
            result >= 0 ==> count_geq(nums@, result as int) == result as int,
            result == -1 ==> forall |x: int| 1 <= x <= nums.len() ==> count_geq(nums@, x) != x,
    {
    }
}

}
