use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i32>, end: nat) -> int
        decreases end,
    {
        if end == 0 {
            0
        } else {
            Self::prefix_sum(nums, (end - 1) as nat) + nums[(end - 1) as int] as int
        }
    }

    pub open spec fn seq_sum(nums: Seq<i32>) -> int {
        Self::prefix_sum(nums, nums.len() as nat)
    }

    pub open spec fn can_achieve(nums: Seq<i32>, end: nat, target: int) -> bool
        decreases end,
    {
        if target < 0 {
            false
        } else if end == 0 {
            target == 0
        } else {
            Self::can_achieve(nums, (end - 1) as nat, target)
            || Self::can_achieve(nums, (end - 1) as nat, target - nums[(end - 1) as int] as int)
        }
    }

    proof fn lemma_prefix_sum_mono(nums: Seq<i32>, small: nat, big: nat)
        requires
            small <= big <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            Self::prefix_sum(nums, small) <= Self::prefix_sum(nums, big),
        decreases big - small,
    {
        if small < big {
            Self::lemma_prefix_sum_mono(nums, small, (big - 1) as nat);
        }
    }

    proof fn lemma_prefix_sum_bounds(nums: Seq<i32>, end: nat)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            0 <= Self::prefix_sum(nums, end) <= Self::seq_sum(nums),
    {
        Self::lemma_prefix_sum_mono(nums, 0, end);
        Self::lemma_prefix_sum_mono(nums, end, nums.len() as nat);
    }

    proof fn lemma_prefix_sum_upper(nums: Seq<i32>, end: nat)
        requires
            end <= nums.len() as nat,
            nums.len() <= 30,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            Self::prefix_sum(nums, end) <= 100 * end,
        decreases end,
    {
        if end > 0 {
            Self::lemma_prefix_sum_upper(nums, (end - 1) as nat);
        }
    }

    proof fn lemma_can_achieve_zero(nums: Seq<i32>, end: nat)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            Self::can_achieve(nums, end, 0),
        decreases end,
    {
        if end > 0 {
            Self::lemma_can_achieve_zero(nums, (end - 1) as nat);
        }
    }

    pub fn last_stone_weight_ii(stones: Vec<i32>) -> (result: i32)
        requires
            1 <= stones.len() <= 30,
            forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 100,
        ensures
            0 <= result,
            result as int <= Self::seq_sum(stones@),
            (Self::seq_sum(stones@) - result as int) % 2 == 0,
            Self::can_achieve(stones@, stones.len() as nat, (Self::seq_sum(stones@) - result as int) / 2),
            forall |t: int| 0 <= t <= Self::seq_sum(stones@) / 2 && Self::can_achieve(stones@, stones.len() as nat, t)
                ==> Self::seq_sum(stones@) - 2 * t >= result as int,
    {
        let n = stones.len();
        let mut total = 0i32;
        let mut i = 0usize;
        while i < n
            invariant
                n == stones.len(),
                1 <= stones.len() <= 30,
                forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 100,
                0 <= i <= n,
                total as int == Self::prefix_sum(stones@, i as nat),
                0 <= total <= 3000,
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_sum_bounds(stones@, (i + 1) as nat);
                Self::lemma_prefix_sum_upper(stones@, n as nat);
                assert(Self::prefix_sum(stones@, (i + 1) as nat)
                    == Self::prefix_sum(stones@, i as nat) + stones@[i as int] as int);
                assert(Self::prefix_sum(stones@, (i + 1) as nat) <= Self::seq_sum(stones@) <= 3000);
            }
            total = total + stones[i];
            i = i + 1;
        }

        proof {
            assert(total as int == Self::seq_sum(stones@));
        }

        let half = (total / 2) as usize;
        let dp_len = half + 1;

        let mut dp: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < dp_len
            invariant
                dp_len == half + 1,
                0 <= half <= 1500,
                0 <= k <= dp_len,
                dp.len() == k,
                forall |t: int| 0 <= t < dp.len() ==> (#[trigger] dp[t]) == false,
            decreases dp_len - k,
        {
            dp.push(false);
            k = k + 1;
        }

        let ghost init_dp = dp@;
        dp.set(0, true);
        proof {
            assert forall |t: int| 0 <= t < dp.len() implies
                (#[trigger] dp[t]) == Self::can_achieve(stones@, 0, t) by {
                if t == 0 {
                    assert(dp[t] == true);
                } else {
                    assert(dp[t] == init_dp[t]);
                    assert(dp[t] == false);
                }
            }
        }

        let mut idx: usize = 0;
        while idx < n
            invariant
                n == stones.len(),
                1 <= stones.len() <= 30,
                forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 100,
                total as int == Self::seq_sum(stones@),
                0 <= total <= 3000,
                half == (total / 2) as usize,
                dp_len == half + 1,
                0 <= idx <= n,
                dp.len() == dp_len,
                forall |t: int| 0 <= t < dp.len() ==>
                    (#[trigger] dp[t]) == Self::can_achieve(stones@, idx as nat, t),
            decreases n - idx,
        {
            let num = stones[idx] as usize;
            let mut s = dp_len;
            while s > 0
                invariant
                    n == stones.len(),
                    1 <= stones.len() <= 30,
                    forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 100,
                    0 <= idx < n,
                    num == stones[idx as int] as usize,
                    num as int == stones@[idx as int] as int,
                    1 <= num <= 100,
                    dp_len == half + 1,
                    dp.len() == dp_len,
                    0 <= s <= dp_len,
                    forall |t: int| 0 <= t < s as int ==>
                        (#[trigger] dp[t]) == Self::can_achieve(stones@, idx as nat, t),
                    forall |t: int| s as int <= t < dp.len() ==>
                        (#[trigger] dp[t]) == Self::can_achieve(stones@, (idx + 1) as nat, t),
                decreases s,
            {
                let cur = s - 1;
                if num <= cur {
                    let old_val = dp[cur];
                    let add_val = dp[cur - num];
                    let new_val = old_val || add_val;
                    let ghost prev_dp = dp@;
                    dp.set(cur, new_val);
                    proof {
                        assert(old_val == Self::can_achieve(stones@, idx as nat, cur as int));
                        assert(add_val == Self::can_achieve(stones@, idx as nat, (cur as int) - (num as int)));
                        assert(Self::can_achieve(stones@, (idx + 1) as nat, cur as int)
                            == (Self::can_achieve(stones@, idx as nat, cur as int)
                                || Self::can_achieve(stones@, idx as nat, (cur as int) - (stones@[idx as int] as int))));
                        assert(new_val == Self::can_achieve(stones@, (idx + 1) as nat, cur as int));
                        assert forall |t: int| 0 <= t < cur as int implies
                            (#[trigger] dp[t]) == Self::can_achieve(stones@, idx as nat, t) by {
                            assert(dp[t] == prev_dp[t]);
                        }
                        assert forall |t: int| cur as int <= t < dp.len() implies
                            (#[trigger] dp[t]) == Self::can_achieve(stones@, (idx + 1) as nat, t) by {
                            if t == cur as int {
                            } else {
                                assert(dp[t] == prev_dp[t]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert((cur as int) - (num as int) < 0);
                        assert(Self::can_achieve(stones@, idx as nat, (cur as int) - (stones@[idx as int] as int)) == false);
                        assert(Self::can_achieve(stones@, (idx + 1) as nat, cur as int)
                            == Self::can_achieve(stones@, idx as nat, cur as int));
                        assert(dp[cur as int] == Self::can_achieve(stones@, (idx + 1) as nat, cur as int));
                        assert forall |t: int| 0 <= t < cur as int implies
                            (#[trigger] dp[t]) == Self::can_achieve(stones@, idx as nat, t) by {}
                        assert forall |t: int| cur as int <= t < dp.len() implies
                            (#[trigger] dp[t]) == Self::can_achieve(stones@, (idx + 1) as nat, t) by {
                            if t == cur as int {
                            } else {
                            }
                        }
                    }
                }
                s = cur;
            }
            idx = idx + 1;
        }

        let mut j = half;
        while j > 0
            invariant
                0 <= j <= half,
                half < dp.len(),
                dp.len() == dp_len,
                dp_len == half + 1,
                n == stones.len(),
                total as int == Self::seq_sum(stones@),
                0 <= total <= 3000,
                half == (total / 2) as usize,
                forall |t: int| 0 <= t < dp.len() ==>
                    (#[trigger] dp[t]) == Self::can_achieve(stones@, n as nat, t),
                forall |t: int| (j as int) < t && t <= (half as int) ==>
                    !Self::can_achieve(stones@, n as nat, t),
            decreases j,
        {
            if dp[j] {
                proof {
                    assert(Self::can_achieve(stones@, n as nat, j as int));
                    assert(2 * (j as int) <= total as int) by(nonlinear_arith)
                        requires j as int <= total as int / 2;
                    assert((Self::seq_sum(stones@) - (total as int - 2 * (j as int))) == 2 * (j as int));
                    assert((Self::seq_sum(stones@) - (total as int - 2 * (j as int))) % 2 == 0);
                    assert((Self::seq_sum(stones@) - (total as int - 2 * (j as int))) / 2 == j as int);
                    assert forall |t: int| 0 <= t <= Self::seq_sum(stones@) / 2
                        && Self::can_achieve(stones@, n as nat, t)
                        implies Self::seq_sum(stones@) - 2 * t >= total as int - 2 * (j as int) by {
                        if t > j as int {
                            assert(t <= half as int);
                            assert(!Self::can_achieve(stones@, n as nat, t));
                        }
                    }
                }
                return total - 2 * (j as i32);
            }
            proof {
                assert(!dp[j as int]);
                assert(!Self::can_achieve(stones@, n as nat, j as int));
            }
            j = j - 1;
        }

        proof {
            Self::lemma_can_achieve_zero(stones@, n as nat);
            assert((Self::seq_sum(stones@) - total as int) == 0);
            assert((Self::seq_sum(stones@) - total as int) % 2 == 0);
            assert((Self::seq_sum(stones@) - total as int) / 2 == 0);
            assert(Self::can_achieve(stones@, n as nat, 0));
            assert forall |t: int| 0 <= t <= Self::seq_sum(stones@) / 2
                && Self::can_achieve(stones@, n as nat, t)
                implies Self::seq_sum(stones@) - 2 * t >= total as int by {
                if t > 0 {
                    assert(t <= half as int);
                    assert(!Self::can_achieve(stones@, n as nat, t));
                }
            }
        }
        total
    }
}

}
