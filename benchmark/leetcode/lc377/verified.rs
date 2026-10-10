use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contribution(nums: Seq<i32>, target: nat, idx: nat) -> int
        decreases target, idx,
    {
        if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
            Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat)
        } else {
            0
        }
    }

    pub open spec fn prefix_count(nums: Seq<i32>, target: nat, end: nat) -> int
        decreases target, end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_count(nums, target, (end - 1) as nat)
                + Self::contribution(nums, target, (end - 1) as nat)
        }
    }

    pub open spec fn combination_count(nums: Seq<i32>, target: nat) -> int
        decreases target,
    {
        if target == 0 {
            1
        } else {
            Self::prefix_count(nums, target, nums.len() as nat)
        }
    }

    pub open spec fn capped(x: int) -> int {
        if x > 2147483648 { 2147483648 } else { x }
    }

    proof fn lemma_prefix_nonneg(nums: Seq<i32>, target: nat, end: nat)
        ensures
            0 <= Self::prefix_count(nums, target, end),
        decreases target, end,
    {
        if end > 0 {
            Self::lemma_prefix_nonneg(nums, target, (end - 1) as nat);
            let idx = (end - 1) as nat;
            assert(Self::prefix_count(nums, target, end)
                == Self::prefix_count(nums, target, (end - 1) as nat)
                    + Self::contribution(nums, target, idx));
            if idx < nums.len() as nat && 0 < nums[idx as int] as int <= target as int {
                Self::lemma_combination_nonneg(nums, ((target as int) - nums[idx as int] as int) as nat);
                assert(Self::contribution(nums, target, idx)
                    == Self::combination_count(nums, ((target as int) - nums[idx as int] as int) as nat));
                assert(0 <= Self::contribution(nums, target, idx));
            } else {
                assert(Self::contribution(nums, target, idx) == 0);
            }
        }
    }

    proof fn lemma_combination_nonneg(nums: Seq<i32>, target: nat)
        ensures
            0 <= Self::combination_count(nums, target),
        decreases target,
    {
        if target > 0 {
            Self::lemma_prefix_nonneg(nums, target, nums.len() as nat);
        }
    }

    proof fn lemma_capped_add(a: int, b: int)
        requires
            0 <= a,
            0 <= b,
        ensures
            Self::capped(Self::capped(a) + Self::capped(b)) == Self::capped(a + b),
    {
    }

    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
            1 <= target <= 1000,
            Self::combination_count(nums@, target as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, target as nat),
    {
        let t = target as usize;
        let mut dp: Vec<i64> = Vec::new();
        dp.push(1);
        proof {
            assert(dp@[0] as int == Self::capped(Self::combination_count(nums@, 0)));
        }
        let mut i: usize = 1;
        while i <= t
            invariant
                1 <= nums.len() <= 200,
                forall |p: int| 0 <= p < nums.len() ==> 1 <= #[trigger] nums[p] <= 1000,
                t == target as usize,
                1 <= target <= 1000,
                1 <= i <= t + 1,
                dp.len() == i,
                forall |k: int| 0 <= k < i ==> #[trigger] dp@[k] as int
                    == Self::capped(Self::combination_count(nums@, k as nat)),
            decreases t + 1 - i,
        {
            let mut total: i64 = 0;
            let mut j: usize = 0;
            while j < nums.len()
                invariant
                    1 <= nums.len() <= 200,
                    forall |p: int| 0 <= p < nums.len() ==> 1 <= #[trigger] nums[p] <= 1000,
                    1 <= i <= 1000,
                    dp.len() == i,
                    forall |k: int| 0 <= k < i ==> #[trigger] dp@[k] as int
                        == Self::capped(Self::combination_count(nums@, k as nat)),
                    0 <= j <= nums.len(),
                    total as int == Self::capped(Self::prefix_count(nums@, i as nat, j as nat)),
                decreases nums.len() - j,
            {
                let num = nums[j] as usize;
                proof {
                    Self::lemma_prefix_nonneg(nums@, i as nat, j as nat);
                    assert(Self::prefix_count(nums@, i as nat, (j + 1) as nat)
                        == Self::prefix_count(nums@, i as nat, j as nat)
                            + Self::contribution(nums@, i as nat, j as nat));
                    if num > i {
                        assert(Self::contribution(nums@, i as nat, j as nat) == 0);
                    }
                }
                if num <= i {
                    proof {
                        let sub = (i - num) as nat;
                        assert(Self::contribution(nums@, i as nat, j as nat)
                            == Self::combination_count(nums@, sub));
                        Self::lemma_combination_nonneg(nums@, sub);
                        Self::lemma_capped_add(Self::prefix_count(nums@, i as nat, j as nat),
                            Self::combination_count(nums@, sub));
                        assert(dp@[i - num] as int == Self::capped(Self::combination_count(nums@, sub)));
                    }
                    total = total + dp[i - num];
                    if total > 2147483648 {
                        total = 2147483648;
                    }
                }
                j += 1;
            }
            proof {
                assert(Self::combination_count(nums@, i as nat)
                    == Self::prefix_count(nums@, i as nat, nums.len() as nat));
            }
            dp.push(total);
            proof {
                assert forall |k: int| 0 <= k < i + 1 implies #[trigger] dp@[k] as int
                    == Self::capped(Self::combination_count(nums@, k as nat)) by {
                    if k == i as int {
                        assert(dp@[k] == total);
                    }
                }
            }
            i += 1;
        }
        proof {
            Self::lemma_combination_nonneg(nums@, target as nat);
            assert(dp@[t as int] as int == Self::capped(Self::combination_count(nums@, t as nat)));
        }
        dp[t] as i32
    }
}

}
