use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_value(nums: Seq<i32>, end: int, value: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_value(nums, end - 1, value)
                + if nums[end - 1] as int == value { 1int } else { 0int }
        }
    }

    pub open spec fn xor_twice_upto(nums: Seq<i32>, upto: int) -> i32
        decreases upto,
    {
        if upto <= 0 {
            0i32
        } else {
            Self::xor_twice_upto(nums, upto - 1)
                ^ if Self::count_value(nums, nums.len() as int, upto) == 2 { upto as i32 } else { 0i32 }
        }
    }

    pub open spec fn duplicate_numbers_xor_spec(nums: Seq<i32>) -> i32 {
        Self::xor_twice_upto(nums, 50)
    }

    pub fn duplicate_numbers_xor(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
            forall |v: int| 1 <= v <= 50 ==> 0 <= #[trigger] Self::count_value(nums@, nums.len() as int, v) <= 2,
        ensures
            result == Self::duplicate_numbers_xor_spec(nums@),
    {
    }
}

}
