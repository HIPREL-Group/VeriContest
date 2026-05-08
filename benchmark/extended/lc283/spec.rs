use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(), 
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub fn move_zeroes(nums: &mut Vec<i32>)
        requires
            1 <= (*old(nums)).len() <= 10_000,
            forall |i: int| 0 <= i < (*old(nums)).len() ==> 
                i32::MIN <= #[trigger] (*old(nums))[i] <= i32::MAX, 
        ensures
            nums.len() == old(nums).len(),
            forall |i: int, j: int|
                0 <= i < j < nums.len() && nums[j] != 0 ==> nums[i] != 0,
            forall |i: int|
                0 <= i < nums.len() && nums[i] == 0 ==>
                forall |j: int| i < j < nums.len() ==> nums[j] == 0,
            forall |v: i32| Self::count(nums@, v) == Self::count(old(nums)@, v),
            forall |i: int, j: int|
                0 <= i < j < old(nums).len() &&
                old(nums)[i] != 0 && old(nums)[j] != 0 ==>
                exists |i2: int, j2: int|
                    0 <= i2 < j2 < nums.len() &&
                    nums[i2] == old(nums)[i] &&
                    nums[j2] == old(nums)[j],
    {
        
    }
}

}
