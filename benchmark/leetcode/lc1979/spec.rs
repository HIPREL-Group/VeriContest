use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_spec(s: Seq<i32>, hi: int) -> int
        decreases hi
    {
        if hi <= 1 { s[0] as int }
        else {
            let rest = Self::min_spec(s, hi - 1);
            if (s[hi - 1] as int) < rest { s[hi - 1] as int } else { rest }
        }
    }

    pub open spec fn max_spec(s: Seq<i32>, hi: int) -> int
        decreases hi
    {
        if hi <= 1 { s[0] as int }
        else {
            let rest = Self::max_spec(s, hi - 1);
            if (s[hi - 1] as int) > rest { s[hi - 1] as int } else { rest }
        }
    }

    pub open spec fn divides(d: int, n: int) -> bool
        recommends d > 0
    {
        n % d == 0
    }

    pub fn find_gcd(nums: Vec<i32>) -> (res: i32)
        requires
            2 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            res >= 1,
            Self::divides(res as int, Self::min_spec(nums@, nums.len() as int)),
            Self::divides(res as int, Self::max_spec(nums@, nums.len() as int)),
            forall |d: int| 1 <= d <= 1000
                && Self::divides(d, Self::min_spec(nums@, nums.len() as int))
                && Self::divides(d, Self::max_spec(nums@, nums.len() as int))
                ==> d <= res as int,
    {
    }
}

}
