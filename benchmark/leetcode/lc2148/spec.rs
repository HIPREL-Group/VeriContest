use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_val(s: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 1 { s[0] as int }
        else {
            let rest = Self::min_val(s, end - 1);
            if (s[end - 1] as int) < rest { s[end - 1] as int } else { rest }
        }
    }

    pub open spec fn max_val(s: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 1 { s[0] as int }
        else {
            let rest = Self::max_val(s, end - 1);
            if (s[end - 1] as int) > rest { s[end - 1] as int } else { rest }
        }
    }

    pub open spec fn count_between(s: Seq<i32>, lo: int, hi: int, end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else {
            Self::count_between(s, lo, hi, end - 1) + if lo < (s[end - 1] as int) && (s[end - 1] as int) < hi { 1int } else { 0int }
        }
    }

    pub fn count_elements(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() <= 2147483647usize,
        ensures
            0 <= result <= nums.len() as i32,
            nums.len() <= 1 ==> result == 0,
            nums.len() > 1 ==> result as int == Self::count_between(nums@, Self::min_val(nums@, nums.len() as int), Self::max_val(nums@, nums.len() as int), nums.len() as int),
    {
    }
}

}
