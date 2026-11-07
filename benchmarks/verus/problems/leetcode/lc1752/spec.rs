use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_descents_range(s: Seq<i32>, start: int) -> int
        decreases s.len() - start,
    {
        if start >= s.len() { 0 }
        else {
            let next: int = if start + 1 < s.len() { start + 1 } else { 0 };
            (if s[start] > s[next] { 1int } else { 0int })
                + Self::count_descents_range(s, start + 1)
        }
    }

    pub fn check(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result == (Self::count_descents_range(nums@, 0) <= 1),
    {

    }
}

}
