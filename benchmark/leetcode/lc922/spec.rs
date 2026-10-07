use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            Self::count(s.drop_last(), v) + if s.last() == v { 1int } else { 0int }
        }
    }

    pub open spec fn filter_even(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] % 2 == 0 {
            Self::filter_even(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_even(s, n - 1)
        }
    }

    pub open spec fn filter_odd(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] % 2 != 0 {
            Self::filter_odd(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_odd(s, n - 1)
        }
    }

    pub open spec fn interleave(a: Seq<i32>, b: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::interleave(a, b, n - 1).push(a[n - 1]).push(b[n - 1])
        }
    }

    pub fn sort_array_by_parity_ii(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 20000,
            nums.len() % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            Self::filter_even(nums@, nums.len() as int).len() == nums.len() as int / 2,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() && i % 2 == 0 ==> result[i] % 2 == 0,
            forall |i: int| 0 <= i < result.len() && i % 2 != 0 ==> result[i] % 2 != 0,
            forall |v: i32| Self::count(result@, v) == Self::count(nums@, v),
    {
    }
}

}
