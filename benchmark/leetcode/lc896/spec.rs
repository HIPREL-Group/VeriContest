use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_inc_violations(s: Seq<i32>, start: int) -> int
        decreases s.len() - start,
    {
        if start + 1 >= s.len() {
            0
        } else {
            (if s[start] > s[start + 1] { 1int } else { 0int })
                + Self::count_inc_violations(s, start + 1)
        }
    }

    pub open spec fn count_dec_violations(s: Seq<i32>, start: int) -> int
        decreases s.len() - start,
    {
        if start + 1 >= s.len() {
            0
        } else {
            (if s[start] < s[start + 1] { 1int } else { 0int })
                + Self::count_dec_violations(s, start + 1)
        }
    }

    pub fn is_monotonic(nums: Vec<i32>) -> (result: bool)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
        ensures
            result == (Self::count_inc_violations(nums@, 0) == 0 || Self::count_dec_violations(nums@, 0) == 0),
    {
    }
}

}
