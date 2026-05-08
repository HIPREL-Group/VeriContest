use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn filter_positive(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] > 0 {
            Self::filter_positive(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_positive(s, n - 1)
        }
    }

    pub open spec fn filter_negative(s: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else if s[n - 1] < 0 {
            Self::filter_negative(s, n - 1).push(s[n - 1])
        } else {
            Self::filter_negative(s, n - 1)
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

    pub fn rearrange_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 200_000,
            nums.len() % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
            forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
            Self::filter_positive(nums@, nums.len() as int).len() == nums.len() as int / 2,
        ensures
            result@ == Self::interleave(
                Self::filter_positive(nums@, nums.len() as int),
                Self::filter_negative(nums@, nums.len() as int),
                nums.len() as int / 2,
            ),
    {
        let mut pos: Vec<i32> = Vec::new();
        let mut neg: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
        {
            if nums[i] > 0 {
                pos.push(nums[i]);
            } else {
                neg.push(nums[i]);
            }
            i = i + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < pos.len()
        {
            result.push(pos[j]);
            result.push(neg[j]);
            j = j + 1;
        }
        result
    }
}

}
