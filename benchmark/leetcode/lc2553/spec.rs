use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digits_spec(num: int) -> Seq<i32>
        decreases num,
    {
        if num < 10 {
            seq![num as i32]
        } else {
            Self::digits_spec(num / 10).push((num % 10) as i32)
        }
    }

    pub open spec fn separate_prefix_spec(nums: Seq<i32>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            Seq::<i32>::empty()
        } else {
            Self::separate_prefix_spec(nums, end - 1) + Self::digits_spec(nums[end - 1] as int)
        }
    }

    pub open spec fn separate_spec(nums: Seq<i32>) -> Seq<i32> {
        Self::separate_prefix_spec(nums, nums.len() as int)
    }

    pub fn separate_digits(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
        ensures
            result@ == Self::separate_spec(nums@),
    {
    }
}

}
