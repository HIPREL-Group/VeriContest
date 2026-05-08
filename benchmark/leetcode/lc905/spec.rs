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

    pub fn sort_array_by_parity(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 5000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 5000,
        ensures
            result.len() == nums.len(),
            forall |i: int, j: int| 0 <= i < j < result.len() && result[j] % 2 == 0
                ==> result[i] % 2 == 0,
            forall |v: i32| Self::count(result@, v) == Self::count(nums@, v),
    {

    }
}

}
