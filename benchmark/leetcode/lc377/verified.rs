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

    proof fn lemma_prefix_mono(nums: Seq<i32>, target: nat, small: nat, big: nat)
        requires
            small <= big <= nums.len() as nat,
        ensures
            Self::prefix_count(nums, target, small) <= Self::prefix_count(nums, target, big),
        decreases big - small,
    {
        if small < big {
            Self::lemma_prefix_mono(nums, target, small, (big - 1) as nat);
            let idx = (big - 1) as nat;
            assert(Self::prefix_count(nums, target, big)
                == Self::prefix_count(nums, target, (big - 1) as nat)
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

    proof fn lemma_prefix_bound_total(nums: Seq<i32>, target: nat, end: nat)
        requires
            target > 0,
            end <= nums.len() as nat,
        ensures
            Self::prefix_count(nums, target, end) <= Self::combination_count(nums, target),
    {
        Self::lemma_prefix_mono(nums, target, end, nums.len() as nat);
    }

    proof fn lemma_bound_for_subtarget(nums: Seq<i32>, target: int, t: int)
        requires
            0 <= t <= target,
            forall |u: int| 0 <= u <= target ==> #[trigger] Self::combination_count(nums, u as nat) <= i32::MAX,
        ensures
            Self::combination_count(nums, t as nat) <= i32::MAX,
    {
    }

    pub fn combination_sum4(nums: Vec<i32>, target: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
            1 <= target <= 1000,
            forall |t: int| 0 <= t <= target as int ==> #[trigger] Self::combination_count(nums@, t as nat) <= i32::MAX,
        ensures
            res as int == Self::combination_count(nums@, target as nat),
    {
        let target_usize = target as usize;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= target_usize
            invariant
                1 <= nums.len() <= 200,
                1 <= target <= 1000,
                target_usize == target as usize,
                0 <= k <= target_usize + 1,
                dp.len() == k,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
                forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
                forall |t: int| 0 <= t <= target as int ==> #[trigger] Self::combination_count(nums@, t as nat) <= i32::MAX,
                forall |i: int| 0 <= i < dp.len() ==> #[trigger] dp[i] == 0,
            decreases target_usize + 1 - k,
        {
            dp.push(0);
            k += 1;
        }
        let ghost dp0 = dp@;
        dp.set(0, 1);
        proof {
            assert(dp@ == dp0.update(0, 1));
            assert(dp[0] as int == Self::combination_count(nums@, 0));
            assert forall |i: int| 1 <= i < dp.len() implies #[trigger] dp[i] == 0 by {
                assert(dp[i] == dp0[i]);
            }
        }
        let mut i: usize = 1;
        while i <= target_usize
            invariant
                1 <= nums.len() <= 200,
                1 <= target <= 1000,
                target_usize == target as usize,
                dp.len() == target_usize + 1,
                1 <= i <= target_usize + 1,
                forall |p: int| 0 <= p < nums.len() ==> 1 <= #[trigger] nums[p] <= 1000,
                forall |p: int, q: int| 0 <= p < q < nums.len() ==> nums[p] != nums[q],
                forall |t: int| 0 <= t <= target as int ==> #[trigger] Self::combination_count(nums@, t as nat) <= i32::MAX,
                forall |j: int| 0 <= j < i ==> #[trigger] dp[j] as int == Self::combination_count(nums@, j as nat),
                forall |j: int| i <= j < dp.len() ==> #[trigger] dp[j] == 0,
            decreases target_usize + 1 - i,
        {
            let mut total: i32 = 0;
            let mut j: usize = 0;
            while j < nums.len()
                invariant
                    1 <= nums.len() <= 200,
                    1 <= target <= 1000,
                    target_usize == target as usize,
                    dp.len() == target_usize + 1,
                    1 <= i <= target_usize,
                    0 <= j <= nums.len(),
                    forall |p: int| 0 <= p < nums.len() ==> 1 <= #[trigger] nums[p] <= 1000,
                    forall |p: int, q: int| 0 <= p < q < nums.len() ==> nums[p] != nums[q],
                    forall |t: int| 0 <= t <= target as int ==> #[trigger] Self::combination_count(nums@, t as nat) <= i32::MAX,
                    forall |x: int| 0 <= x < i ==> #[trigger] dp[x] as int == Self::combination_count(nums@, x as nat),
                    forall |x: int| i <= x < dp.len() ==> #[trigger] dp[x] == 0,
                    total as int == Self::prefix_count(nums@, i as nat, j as nat),
                    0 <= Self::prefix_count(nums@, i as nat, j as nat) <= i32::MAX,
                decreases nums.len() - j,
            {
                let num = nums[j];
                if num <= i as i32 {
                    proof {
                        assert(1 <= num);
                        assert(0 < num as int <= i as int);
                        assert(i as int <= target as int);
                        assert((i - num as usize) as int == i as int - num as int);
                        assert(0 <= (i - num as usize) < i);
                        assert(dp[(i - num as usize) as int] as int
                            == Self::combination_count(nums@, (i - num as usize) as nat));
                        Self::lemma_prefix_bound_total(nums@, i as nat, (j + 1) as nat);
                        Self::lemma_bound_for_subtarget(nums@, target as int, i as int);
                        assert(Self::contribution(nums@, i as nat, j as nat)
                            == Self::combination_count(nums@, (i - num as usize) as nat));
                        assert(total as int + dp[i - num as usize] as int
                            == Self::prefix_count(nums@, i as nat, (j + 1) as nat));
                    }
                    total = total + dp[i - num as usize];
                } else {
                    proof {
                        assert(num > i as i32);
                        assert(Self::contribution(nums@, i as nat, j as nat) == 0);
                        assert(Self::prefix_count(nums@, i as nat, (j + 1) as nat)
                            == Self::prefix_count(nums@, i as nat, j as nat));
                    }
                }
                proof {
                    let next_j = (j + 1) as nat;
                    assert(total as int == Self::prefix_count(nums@, i as nat, next_j));
                    Self::lemma_prefix_nonneg(nums@, i as nat, next_j);
                    Self::lemma_prefix_bound_total(nums@, i as nat, next_j);
                    Self::lemma_bound_for_subtarget(nums@, target as int, i as int);
                    assert(0 <= Self::prefix_count(nums@, i as nat, next_j) <= i32::MAX);
                }
                j += 1;
            }
            proof {
                assert(j == nums.len());
                assert(total as int == Self::prefix_count(nums@, i as nat, nums.len() as nat));
                assert(total as int == Self::combination_count(nums@, i as nat));
            }
            let ghost prev_dp = dp@;
            dp.set(i, total);
            proof {
                assert(dp@ == prev_dp.update(i as int, total));
                assert forall |x: int| 0 <= x < (i + 1) as int implies
                    #[trigger] dp[x] as int == Self::combination_count(nums@, x as nat) by {
                    if x < i as int {
                        assert(dp[x] == prev_dp[x]);
                    } else {
                        assert(x == i as int);
                        assert(dp[x] == total);
                    }
                }
                assert forall |x: int| (i + 1) as int <= x < dp.len() implies #[trigger] dp[x] == 0 by {
                    assert(dp[x] == prev_dp[x]);
                }
            }
            i += 1;
        }
        dp[target_usize]
    }
}

}
