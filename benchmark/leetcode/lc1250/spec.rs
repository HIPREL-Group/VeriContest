use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn gcd_spec(a: int, b: int) -> int
    decreases b,
{
    if b <= 0 { a } else { gcd_spec(b, a % b) }
}

pub open spec fn array_gcd(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else if n == 1 { s[0] as int }
    else { gcd_spec(array_gcd(s, n - 1), s[n - 1] as int) }
}

impl Solution {
    pub fn is_good_array(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            res == (array_gcd(nums@, nums@.len() as int) == 1),
    {
    }
}

}
