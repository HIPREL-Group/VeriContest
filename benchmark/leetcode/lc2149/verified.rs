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

    proof fn filter_positive_len(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            Self::filter_positive(s, n).len() <= n,
        decreases n,
    {
        if n > 0 {
            Self::filter_positive_len(s, n - 1);
        }
    }

    proof fn filter_negative_len(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
        ensures
            Self::filter_negative(s, n).len() <= n,
        decreases n,
    {
        if n > 0 {
            Self::filter_negative_len(s, n - 1);
        }
    }

    proof fn filter_pos_neg_sum(s: Seq<i32>, n: int)
        requires
            0 <= n <= s.len(),
            forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] != 0,
        ensures
            Self::filter_positive(s, n).len() + Self::filter_negative(s, n).len() == n,
        decreases n,
    {
        if n > 0 {
            Self::filter_pos_neg_sum(s, n - 1);
        }
    }

    proof fn interleave_len(a: Seq<i32>, b: Seq<i32>, n: int)
        requires
            0 <= n,
        ensures
            Self::interleave(a, b, n).len() == 2 * n,
        decreases n,
    {
        if n > 0 {
            Self::interleave_len(a, b, n - 1);
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
            invariant
                0 <= i <= nums.len(),
                pos@ == Self::filter_positive(nums@, i as int),
                neg@ == Self::filter_negative(nums@, i as int),
                pos.len() + neg.len() == i,
                2 <= nums.len() <= 200_000,
                forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] != 0,
                forall |k: int| 0 <= k < nums.len() ==> -100_000 <= #[trigger] nums[k] <= 100_000,
            decreases nums.len() - i,
        {
            if nums[i] > 0 {
                pos.push(nums[i]);
            } else {
                proof {
                    assert(nums[i as int] != 0);
                    assert(nums[i as int] < 0);
                }
                neg.push(nums[i]);
            }
            i = i + 1;
        }

        proof {
            Self::filter_pos_neg_sum(nums@, nums.len() as int);
            assert(pos.len() == neg.len());
        }

        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < pos.len()
            invariant
                0 <= j <= pos.len(),
                pos@ == Self::filter_positive(nums@, nums.len() as int),
                neg@ == Self::filter_negative(nums@, nums.len() as int),
                pos.len() == neg.len(),
                pos.len() as int == nums.len() as int / 2,
                result@ == Self::interleave(pos@, neg@, j as int),
                result.len() == 2 * j,
            decreases pos.len() - j,
        {
            result.push(pos[j]);
            result.push(neg[j]);
            proof {
                assert(Self::interleave(pos@, neg@, (j + 1) as int)
                    == Self::interleave(pos@, neg@, j as int).push(pos@[j as int]).push(neg@[j as int]));
            }
            j = j + 1;
        }
        result
    }
}

}
