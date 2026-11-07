use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] == v { 1int } else { 0int }) + Self::count_eq_range(s, v, lo + 1, hi)
        }
    }

    pub open spec fn count_sq_eq_range(s: Seq<i32>, v: i32, lo: int, hi: int) -> int
        recommends 0 <= lo, hi <= s.len()
        decreases hi - lo
    {
        if lo >= hi { 0 }
        else {
            (if s[lo] * s[lo] == v { 1int } else { 0int }) + Self::count_sq_eq_range(s, v, lo + 1, hi)
        }
    }

    pub fn sorted_squares(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
        ensures
            result.len() == nums.len(),
            forall |i: int, j: int| 0 <= i <= j < result.len() as int ==> result[i] <= result[j],
            forall |v: i32| Self::count_eq_range(result@, v, 0, result.len() as int)
                == Self::count_sq_eq_range(nums@, v, 0, nums.len() as int),
    {

    }
}

}
