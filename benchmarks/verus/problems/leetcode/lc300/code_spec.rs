use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_lis_subseq(nums: Seq<i32>, idx_seq: Seq<int>) -> bool {
    idx_seq.len() >= 1
    && forall |j: int| 0 <= j < idx_seq.len() ==> 0 <= (#[trigger] idx_seq[j]) < nums.len()
    && forall |j: int| 0 <= j < idx_seq.len() - 1 ==>
        idx_seq[j] < idx_seq[j + 1] && (#[trigger] nums[idx_seq[j]]) < nums[idx_seq[j + 1]]
}

pub open spec fn has_lis_of_length(nums: Seq<i32>, k: int) -> bool {
    exists |idx_seq: Seq<int>|
        idx_seq.len() == k && (#[trigger] is_lis_subseq(nums, idx_seq))
}

spec fn max_lis_before(nums: Seq<i32>, i: int, bound: i32) -> nat
    decreases i, 0nat,
{
    if i <= 0 {
        0
    } else {
        let rest = max_lis_before(nums, i - 1, bound);
        if nums[i - 1] < bound {
            let cur = lis_ending_at(nums, i - 1);
            if cur > rest { cur } else { rest }
        } else {
            rest
        }
    }
}

spec fn lis_ending_at(nums: Seq<i32>, i: int) -> nat
    decreases i, 1nat,
{
    if i < 0 {
        0
    } else {
        1 + max_lis_before(nums, i, nums[i])
    }
}

impl Solution {
    pub fn length_of_lis(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 2500,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= (#[trigger] nums[i]) <= 10_000,
        ensures
            res >= 1,
            res <= nums.len() as int,
            has_lis_of_length(nums@, res as int),
            forall |k: int| k > res as int ==> !has_lis_of_length(nums@, k),
    {
        let n = nums.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            decreases n - i,
        {
            dp.push(1i32);
            i += 1;
        }
        i = 1;
        while i < n
        {
            let mut j: usize = 0;
            while j < i
            {
                if nums[j] < nums[i] {
                    if dp[j] + 1 > dp[i] {
                        dp[i] = dp[j] + 1;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        let mut best = dp[0];
        let mut k: usize = 1;
        while k < n
        {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }
        best
    }
}

}
