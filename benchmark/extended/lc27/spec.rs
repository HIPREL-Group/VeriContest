use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_to(s: Seq<i32>, v: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else { (if s[end - 1] == v { 1int } else { 0int }) + Self::count_to(s, v, end - 1) }
    }

    pub fn remove_element(nums: &mut Vec<i32>, val: i32) -> (k: i32)
        requires
            0 <= old(nums).len() <= 100,
            forall |i: int| 0 <= i < old(nums).len() ==>
                0 <= #[trigger] old(nums)[i] <= 50,
            0 <= val <= 100,
        ensures
            0 <= k <= nums.len(),
            nums.len() == old(nums).len(),
            forall |i: int| 0 <= i < k as int ==> nums[i] != val,
            forall |v: i32| v != val ==>
                Self::count_to(nums@, v, k as int) ==
                    Self::count_to(old(nums)@, v, old(nums).len() as int),
    {

    }
}

}
