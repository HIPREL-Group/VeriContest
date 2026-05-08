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

    pub open spec fn target_sum_count_prefix(nums: Seq<i32>, end: nat, target: int) -> int
        decreases end,
    {
        if end == 0 {
            if target == 0 { 1 } else { 0 }
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            Self::target_sum_count_prefix(nums, (end - 1) as nat, target - x)
                + Self::target_sum_count_prefix(nums, (end - 1) as nat, target + x)
        }
    }

    pub open spec fn target_sum_count(nums: Seq<i32>, target: int) -> int {
        Self::target_sum_count_prefix(nums, nums.len() as nat, target)
    }

    pub open spec fn subset_count_prefix(nums: Seq<i32>, goal: int, end: nat) -> int
        decreases end,
    {
        if goal < 0 {
            0
        } else if end == 0 {
            if goal == 0 { 1 } else { 0 }
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            Self::subset_count_prefix(nums, goal, (end - 1) as nat)
                + Self::subset_count_prefix(nums, goal - x, (end - 1) as nat)
        }
    }

    pub open spec fn two_pow(n: nat) -> int
        decreases n,
    {
        if n == 0 {
            1
        } else {
            2 * Self::two_pow((n - 1) as nat)
        }
    }

    proof fn lemma_prefix_sum_mono(nums: Seq<i32>, small: nat, big: nat)
        requires
            small <= big <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            Self::prefix_sum(nums, small) <= Self::prefix_sum(nums, big),
        decreases big - small,
    {
        if small < big {
            let prev = (big - 1) as nat;
            let idx = prev as int;
            Self::lemma_prefix_sum_mono(nums, small, prev);
            assert(Self::prefix_sum(nums, big) == Self::prefix_sum(nums, prev) + nums[idx] as int);
            assert(0 <= nums[idx]);
            assert(Self::prefix_sum(nums, prev) <= Self::prefix_sum(nums, big));
        }
    }

    proof fn lemma_prefix_sum_bounds(nums: Seq<i32>, end: nat)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            0 <= Self::prefix_sum(nums, end) <= Self::seq_sum(nums),
    {
        Self::lemma_prefix_sum_mono(nums, 0, end);
        Self::lemma_prefix_sum_mono(nums, end, nums.len() as nat);
        assert(Self::prefix_sum(nums, 0) == 0);
    }

    proof fn lemma_target_bad_parity(nums: Seq<i32>, end: nat, target: int)
        requires
            end <= nums.len() as nat,
            (Self::prefix_sum(nums, end) + target) % 2 != 0,
        ensures
            Self::target_sum_count_prefix(nums, end, target) == 0,
        decreases end,
    {
        if end == 0 {
            assert(target != 0);
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            let prev = (end - 1) as nat;
            assert(Self::prefix_sum(nums, end) == Self::prefix_sum(nums, prev) + x);
            assert((Self::prefix_sum(nums, prev) + (target - x)) % 2 != 0);
            assert((Self::prefix_sum(nums, prev) + (target + x)) % 2 != 0);
            Self::lemma_target_bad_parity(nums, prev, target - x);
            Self::lemma_target_bad_parity(nums, prev, target + x);
        }
    }

    proof fn lemma_target_out_of_range(nums: Seq<i32>, end: nat, target: int)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            target < -Self::prefix_sum(nums, end) || target > Self::prefix_sum(nums, end),
        ensures
            Self::target_sum_count_prefix(nums, end, target) == 0,
        decreases end,
    {
        if end == 0 {
            assert(target != 0);
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            let prev = (end - 1) as nat;
            assert(Self::prefix_sum(nums, end) == Self::prefix_sum(nums, prev) + x);
            assert(0 <= x);
            if target > Self::prefix_sum(nums, end) {
                assert(target - x > Self::prefix_sum(nums, prev));
                assert(target + x > Self::prefix_sum(nums, prev));
                Self::lemma_target_out_of_range(nums, prev, target - x);
                Self::lemma_target_out_of_range(nums, prev, target + x);
            } else {
                assert(target < -Self::prefix_sum(nums, end));
                assert(target - x < -Self::prefix_sum(nums, prev));
                assert(target + x < -Self::prefix_sum(nums, prev));
                Self::lemma_target_out_of_range(nums, prev, target - x);
                Self::lemma_target_out_of_range(nums, prev, target + x);
            }
        }
    }

    proof fn lemma_target_subset_equiv(nums: Seq<i32>, end: nat, goal: int)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            0 <= goal,
        ensures
            Self::subset_count_prefix(nums, goal, end)
                == Self::target_sum_count_prefix(nums, end, 2 * goal - Self::prefix_sum(nums, end)),
        decreases end,
    {
        if end == 0 {
            assert(Self::subset_count_prefix(nums, goal, 0) == if goal == 0 { 1int } else { 0int });
            assert(Self::target_sum_count_prefix(nums, 0, 2 * goal) == if 2 * goal == 0 { 1int } else { 0int });
            if goal == 0 {
                assert(2 * goal == 0);
            } else {
                assert(2 * goal != 0);
            }
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            let prev = (end - 1) as nat;
            assert(Self::prefix_sum(nums, end) == Self::prefix_sum(nums, prev) + x);
            assert(0 <= x);
            Self::lemma_target_subset_equiv(nums, prev, goal);
            if goal >= x {
                Self::lemma_target_subset_equiv(nums, prev, goal - x);
                assert(2 * goal - Self::prefix_sum(nums, end) + x == 2 * goal - Self::prefix_sum(nums, prev));
                assert(2 * goal - Self::prefix_sum(nums, end) - x == 2 * (goal - x) - Self::prefix_sum(nums, prev));
            } else {
                assert(goal - x < 0);
                assert(2 * goal - Self::prefix_sum(nums, end) - x < -Self::prefix_sum(nums, prev));
                Self::lemma_target_out_of_range(nums, prev, 2 * goal - Self::prefix_sum(nums, end) - x);
                assert(Self::subset_count_prefix(nums, goal - x, prev) == 0);
            }
        }
    }

    proof fn lemma_subset_too_large_zero(nums: Seq<i32>, goal: int, end: nat)
        requires
            end <= nums.len() as nat,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            goal > Self::prefix_sum(nums, end),
        ensures
            Self::subset_count_prefix(nums, goal, end) == 0,
        decreases end,
    {
        if end == 0 {
            assert(goal != 0);
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            let prev = (end - 1) as nat;
            assert(Self::prefix_sum(nums, end) == Self::prefix_sum(nums, prev) + x);
            assert(0 <= x);
            assert(goal > Self::prefix_sum(nums, prev));
            assert(goal - x > Self::prefix_sum(nums, prev));
            Self::lemma_subset_too_large_zero(nums, goal, prev);
            Self::lemma_subset_too_large_zero(nums, goal - x, prev);
        }
    }

    proof fn lemma_two_pow_positive(n: nat)
        ensures
            0 < Self::two_pow(n),
        decreases n,
    {
        if n > 0 {
            Self::lemma_two_pow_positive((n - 1) as nat);
            assert(Self::two_pow(n) == 2 * Self::two_pow((n - 1) as nat));
        }
    }

    proof fn lemma_subset_bound(nums: Seq<i32>, goal: int, end: nat)
        requires
            end <= nums.len() as nat,
        ensures
            0 <= Self::subset_count_prefix(nums, goal, end) <= Self::two_pow(end),
        decreases end,
    {
        Self::lemma_two_pow_positive(end);
        if goal < 0 {
            assert(Self::subset_count_prefix(nums, goal, end) == 0);
        } else if end == 0 {
        } else {
            let idx = (end - 1) as int;
            let x = nums[idx] as int;
            let prev = (end - 1) as nat;
            Self::lemma_subset_bound(nums, goal, prev);
            Self::lemma_subset_bound(nums, goal - x, prev);
            assert(Self::subset_count_prefix(nums, goal, end)
                == Self::subset_count_prefix(nums, goal, prev)
                    + Self::subset_count_prefix(nums, goal - x, prev));
            assert(Self::two_pow(end) == 2 * Self::two_pow(prev));
        }
    }

    proof fn lemma_two_pow_mono(small: nat, big: nat)
        requires
            small <= big,
        ensures
            Self::two_pow(small) <= Self::two_pow(big),
        decreases big - small,
    {
        if small < big {
            Self::lemma_two_pow_mono(small, (big - 1) as nat);
            assert(Self::two_pow(big) == 2 * Self::two_pow((big - 1) as nat));
            Self::lemma_two_pow_positive((big - 1) as nat);
            assert(Self::two_pow((big - 1) as nat) <= Self::two_pow(big));
        }
    }

    proof fn lemma_two_pow_le_20(n: nat)
        requires
            n <= 20,
        ensures
            Self::two_pow(n) <= 1_048_576,
    {
        Self::lemma_two_pow_mono(n, 20);
        assert(Self::two_pow(20) == 1_048_576) by (compute);
    }

    pub fn find_target_sum_ways(nums: Vec<i32>, target: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 20,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
            Self::seq_sum(nums@) <= 1000,
            -1000 <= target <= 1000,
        ensures
            result as int == Self::target_sum_count(nums@, target as int),
    {
        let n = nums.len();
        let mut total = 0i32;
        let mut i = 0usize;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 20,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1000,
                Self::seq_sum(nums@) <= 1000,
                0 <= i <= n,
                total as int == Self::prefix_sum(nums@, i as nat),
                0 <= total as int,
            decreases n - i,
        {
            proof {
                Self::lemma_prefix_sum_bounds(nums@, (i + 1) as nat);
                assert(0 <= nums[i as int] <= 1000);
                assert(Self::prefix_sum(nums@, (i + 1) as nat)
                    == Self::prefix_sum(nums@, i as nat) + nums[i as int] as int);
                assert(0 <= total as int + nums[i as int] as int <= 1000);
                assert(i32::MIN <= total as int + nums[i as int] as int <= i32::MAX);
            }
            total = total + nums[i];
            i += 1;
        }
        proof {
            assert(total as int == Self::prefix_sum(nums@, n as nat));
            assert(total as int == Self::seq_sum(nums@));
        }
        let transformed = total + target;
        if transformed < 0 {
            proof {
                assert((target as int) < -Self::prefix_sum(nums@, n as nat));
                Self::lemma_target_out_of_range(nums@, n as nat, target as int);
            }
            return 0;
        }
        if transformed % 2 != 0 {
            proof {
                Self::lemma_target_bad_parity(nums@, n as nat, target as int);
            }
            return 0;
        }
        let goal_i = transformed / 2;
        let goal = goal_i as usize;
        proof {
            assert(0 <= goal_i <= 1000);
            assert(goal as int == goal_i as int);
            assert(goal < usize::MAX);
        }
        if goal_i > total {
            proof {
                Self::lemma_target_subset_equiv(nums@, n as nat, goal_i as int);
                assert(target as int == 2 * goal_i as int - Self::prefix_sum(nums@, n as nat));
                assert((goal_i as int) > Self::prefix_sum(nums@, n as nat));
                Self::lemma_subset_too_large_zero(nums@, goal_i as int, n as nat);
            }
            return 0;
        }
        let goal_len = goal + 1;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < goal_len
            invariant
                goal_len == goal + 1,
                0 <= k <= goal_len,
                dp.len() == k,
                forall |t: int| 0 <= t < dp.len() ==> #[trigger] dp[t] == 0,
            decreases goal_len - k,
        {
            dp.push(0);
            k += 1;
        }
        let ghost old_dp = dp@;
        dp[0] = 1;
        proof {
            assert(dp@ == old_dp.update(0, 1));
            assert forall |t: int| 0 <= t < dp.len() implies #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, 0) by {
                if t == 0 {
                    assert(dp[t] == 1);
                } else {
                    assert(dp[t] == old_dp[t]);
                }
            }
        }
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 20,
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1000,
                Self::seq_sum(nums@) <= 1000,
                transformed % 2 == 0,
                transformed >= 0,
                goal_i == transformed / 2,
                goal as int == goal_i as int,
                goal_i <= total,
                total as int == Self::seq_sum(nums@),
                0 <= idx <= n,
                goal_len == goal + 1,
                dp.len() == goal_len,
                forall |t: int| 0 <= t < dp.len() ==> #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, idx as nat),
            decreases n - idx,
        {
            let num = nums[idx] as usize;
            let mut s = goal_len;
            while s > 0
                invariant
                    n == nums.len(),
                    1 <= nums.len() <= 20,
                    forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 1000,
                    0 <= idx < n,
                    num == nums[idx as int] as usize,
                    goal_len == goal + 1,
                    dp.len() == goal_len,
                    0 <= s <= goal_len,
                    forall |t: int| 0 <= t < s as int ==> #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, idx as nat),
                    forall |t: int| s as int <= t < dp.len() ==> #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, (idx + 1) as nat),
                decreases s,
            {
                let cur = s - 1;
                if num <= cur {
                    let old_value = dp[cur];
                    let add_value = dp[cur - num];
                    proof {
                        Self::lemma_subset_bound(nums@, cur as int, idx as nat);
                        Self::lemma_subset_bound(nums@, cur as int - num as int, idx as nat);
                        Self::lemma_two_pow_le_20(idx as nat);
                        assert(old_value as int == Self::subset_count_prefix(nums@, cur as int, idx as nat));
                        assert(add_value as int == Self::subset_count_prefix(nums@, cur as int - num as int, idx as nat));
                        assert((old_value as int) <= 1_048_576);
                        assert((add_value as int) <= 1_048_576);
                        assert(0 <= (old_value as int) + (add_value as int) <= 2_097_152);
                        assert(i32::MIN <= (old_value as int) + (add_value as int) <= i32::MAX);
                    }
                    let ghost prev_dp = dp@;
                    let value = old_value + add_value;
                    dp[cur] = old_value + add_value;
                    proof {
                        assert(dp@ == prev_dp.update(cur as int, value));
                        assert(value as int
                            == Self::subset_count_prefix(nums@, cur as int, idx as nat)
                                + Self::subset_count_prefix(nums@, cur as int - num as int, idx as nat));
                        assert(value as int == Self::subset_count_prefix(nums@, cur as int, (idx + 1) as nat));
                        assert forall |t: int| 0 <= t < cur as int implies #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, idx as nat) by {
                            assert(dp[t] == prev_dp[t]);
                        }
                        assert forall |t: int| cur as int <= t < dp.len() implies #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, (idx + 1) as nat) by {
                            if t == cur as int {
                                assert(dp[t] == value);
                            } else {
                                assert(dp[t] == prev_dp[t]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert((cur as int) - (num as int) < 0);
                        assert(Self::subset_count_prefix(nums@, cur as int - num as int, idx as nat) == 0);
                        assert(Self::subset_count_prefix(nums@, cur as int, (idx + 1) as nat)
                            == Self::subset_count_prefix(nums@, cur as int, idx as nat));
                        assert(dp[cur as int] as int == Self::subset_count_prefix(nums@, cur as int, (idx + 1) as nat));
                        assert forall |t: int| 0 <= t < cur as int implies #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, idx as nat) by {
                        }
                        assert forall |t: int| cur as int <= t < dp.len() implies #[trigger] dp[t] as int == Self::subset_count_prefix(nums@, t, (idx + 1) as nat) by {
                            if t == cur as int {
                            }
                        }
                    }
                }
                s = cur;
            }
            idx += 1;
        }
        proof {
            Self::lemma_target_subset_equiv(nums@, n as nat, goal as int);
            assert(target as int == 2 * goal as int - Self::prefix_sum(nums@, n as nat));
            assert(dp[goal as int] as int == Self::subset_count_prefix(nums@, goal as int, n as nat));
            assert(Self::target_sum_count(nums@, target as int) == Self::target_sum_count_prefix(nums@, n as nat, target as int));
        }
        dp[goal]
    }
}

}
