use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn min_in_range(s: Seq<i32>, i: int, j: int) -> int
        decreases j - i,
    {
        if i >= j {
            s[i] as int
        } else {
            Self::spec_min(s[i] as int, Self::min_in_range(s, i + 1, j))
        }
    }

    pub open spec fn score_spec(s: Seq<i32>, i: int, j: int) -> int {
        Self::min_in_range(s, i, j) * (j - i + 1)
    }

    pub fn maximum_score(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20_000,
            0 <= k < nums.len() as i32,
        ensures
            exists|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() && result as int
                    == Self::score_spec(nums@, i, j),
            forall|i: int, j: int|
                0 <= i && i <= k as int && k as int <= j && j < nums@.len() ==> Self::score_spec(
                    nums@,
                    i,
                    j,
                ) <= result as int,
            result >= 1i32,
    {
    }
}

} 
