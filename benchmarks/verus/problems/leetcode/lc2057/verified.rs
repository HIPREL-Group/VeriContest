use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn smallest_equal(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 9,
        ensures
            result == -1 || 0 <= result < nums.len(),
            result >= 0 ==> nums[result as int] == result as int % 10,
            result >= 0 ==> forall |j: int| 0 <= j < result as int ==> nums[j] != j % 10,
            result == -1 ==> forall |j: int| 0 <= j < nums.len() ==> nums[j] != j % 10,
    {
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 9,
                0 <= i <= nums.len(),
                forall |j: int| 0 <= j < i ==> nums[j] != j % 10,
            decreases nums.len() - i,
        {
            if nums[i] == (i % 10) as i32 {
                proof {
                    assert(0 <= i < nums.len());
                    assert((i % 10) as int == i as int % 10);
                    assert(nums[i as int] == ((i % 10) as i32) as int);
                }
                return i as i32;
            }
            i = i + 1;
        }
        -1
    }
}

}
