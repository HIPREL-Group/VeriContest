use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_less_prefix(nums: Seq<i32>, target: i32, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        count_less_prefix(nums, target, (k - 1) as nat)
            + if nums[(k - 1) as int] < target { 1int } else { 0int }
    }
}

pub open spec fn count_eq_prefix(nums: Seq<i32>, target: i32, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        count_eq_prefix(nums, target, (k - 1) as nat)
            + if nums[(k - 1) as int] == target { 1int } else { 0int }
    }
}

impl Solution {
    pub fn target_indices(nums: Vec<i32>, target: i32) -> (result: Vec<i32>)
        requires
            nums.len() <= 2147483647usize,
        ensures
            result.len() as int == count_eq_prefix(nums@, target, nums.len() as nat),
            forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i]
                == (count_less_prefix(nums@, target, nums.len() as nat) + i) as i32,
    {
    }
}

}
