use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_covered(nums: Seq<Seq<i32>>, p: int, idx: int) -> bool
        decreases idx
    {
        if idx <= 0 { false }
        else {
            Self::is_covered(nums, p, idx - 1) || (nums[idx - 1][0] as int <= p && p <= nums[idx - 1][1] as int)
        }
    }

    pub open spec fn count_covered(nums: Seq<Seq<i32>>, p: int) -> int
        decreases p
    {
        if p <= 0 { 0 }
        else {
            Self::count_covered(nums, p - 1) + if Self::is_covered(nums, p, nums.len() as int) { 1int } else { 0int }
        }
    }

    pub fn number_of_points(nums: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums.deep_view()[i]).len() == 2,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= (#[trigger] nums.deep_view()[i])[0] <= nums.deep_view()[i][1] <= 100,
        ensures
            result as int == Self::count_covered(nums.deep_view(), 100),
    {
    }
}

}
