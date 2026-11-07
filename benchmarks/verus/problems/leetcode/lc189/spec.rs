use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn rotated_index(i: int, k: int, n: int) -> int
        recommends n > 0
    {
        (n - k % n + i) % n
    }

    fn reverse_range(nums: &mut Vec<i32>, l: usize, r: usize)
        requires
            l <= r,
            r < old(nums).len(),
        ensures
            nums.len() == old(nums).len(),
            forall |j: int| 0 <= j < nums.len() && !(l as int <= j <= r as int) ==> nums[j] == old(nums)[j],
            forall |j: int| l as int <= j <= r as int ==> nums[j] == old(nums)[l as int + r as int - j],
    {
    }

    pub fn rotate(nums: &mut Vec<i32>, k: i32)
        requires
            1 <= old(nums).len() <= 100_000,
            0 <= k <= 100_000,
        ensures
            nums.len() == old(nums).len(),
            forall |i: int| 0 <= i < nums.len() ==> nums[i] == old(nums)[Self::rotated_index(i, k as int, nums.len() as int)],
    {
    }
}

} 
