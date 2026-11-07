use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;















pub open spec fn optimal_score(nums: Seq<i32>, mults: Seq<i32>, n: int, m: int, op: int, left: int) -> int
    decreases m - op
{
    if op >= m {
        0
    } else {
        let right_idx = n - 1 - (op - left);
        let take_left = mults[op] as int * nums[left] as int
            + optimal_score(nums, mults, n, m, op + 1, left + 1);
        let take_right = mults[op] as int * nums[right_idx] as int
            + optimal_score(nums, mults, n, m, op + 1, left);
        if take_left >= take_right { take_left } else { take_right }
    }
}

proof fn optimal_score_bound(nums: Seq<i32>, mults: Seq<i32>, n: int, m: int, op: int, left: int)
    requires
        0 <= op <= m,
        0 <= left <= op,
        1 <= m <= 300,
        m <= n,
        nums.len() == n,
        mults.len() == m,
        forall|k: int| 0 <= k < n ==> -1000 <= #[trigger] nums[k] <= 1000,
        forall|k: int| 0 <= k < m ==> -1000 <= #[trigger] mults[k] <= 1000,
    ensures
        -((m - op) * 1_000_000) <= optimal_score(nums, mults, n, m, op, left) <= (m - op) * 1_000_000,
    decreases m - op
{
    if op < m {
        let right_idx = n - 1 - (op - left);
        optimal_score_bound(nums, mults, n, m, op + 1, left + 1);
        optimal_score_bound(nums, mults, n, m, op + 1, left);
        assert(0 <= right_idx < n);
        assert(-1_000_000 <= mults[op] as int * nums[left] as int <= 1_000_000)
            by(nonlinear_arith)
            requires -1000 <= mults[op] as int <= 1000, -1000 <= nums[left] as int <= 1000;
        assert(-1_000_000 <= mults[op] as int * nums[right_idx] as int <= 1_000_000)
            by(nonlinear_arith)
            requires -1000 <= mults[op] as int <= 1000, -1000 <= nums[right_idx] as int <= 1000;
    }
}

impl Solution {
    pub fn maximum_score(nums: Vec<i32>, multipliers: Vec<i32>) -> (result: i32)
        requires
            multipliers.len() >= 1,
            multipliers.len() <= 300,
            nums.len() >= multipliers.len(),
            nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
            forall|i: int| 0 <= i < multipliers.len() ==> -1000 <= #[trigger] multipliers[i] <= 1000,
        ensures
            result == optimal_score(nums@, multipliers@, nums@.len() as int, multipliers@.len() as int, 0, 0) as i32,
    {
        let n = nums.len();
        let m = multipliers.len();
        let ghost ns = nums@;
        let ghost ms = multipliers@;
        let ghost ni = n as int;
        let ghost mi = m as int;
        let mut dp: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= m
            invariant
                0 <= k <= m + 1,
                m <= 300,
                dp.len() == k,
                forall|idx: int| 0 <= idx < k as int ==> dp[idx] == 0i32,
            decreases m + 1 - k,
        {
            dp.push(0i32);
            k += 1;
        }
        let mut i: usize = m;
        while i > 0
            invariant
                0 <= i <= m,
                dp.len() == m + 1,
                ns == nums@,
                ms == multipliers@,
                ni == n as int,
                mi == m as int,
                1 <= mi <= 300,
                mi <= ni <= 100_000,
                n == ns.len(),
                m == ms.len(),
                n >= m,
                forall|k: int| 0 <= k < ni ==> -1000 <= #[trigger] ns[k] <= 1000,
                forall|k: int| 0 <= k < mi ==> -1000 <= #[trigger] ms[k] <= 1000,
                forall|j: int| 0 <= j <= i as int ==>
                    (#[trigger] dp[j]) as int == optimal_score(ns, ms, ni, mi, i as int, j),
            decreases i,
        {
            i -= 1;
            let mut j: usize = 0;
            while j <= i
                invariant
                    0 <= j <= i + 1,
                    0 <= i < m,
                    dp.len() == m + 1,
                    ns == nums@,
                    ms == multipliers@,
                    ni == n as int,
                    mi == m as int,
                    1 <= mi <= 300,
                    mi <= ni <= 100_000,
                    n == ns.len(),
                    m == ms.len(),
                    n >= m,
                    forall|k: int| 0 <= k < ni ==> -1000 <= #[trigger] ns[k] <= 1000,
                    forall|k: int| 0 <= k < mi ==> -1000 <= #[trigger] ms[k] <= 1000,
                    forall|k: int| 0 <= k < j as int ==>
                        (#[trigger] dp[k]) as int == optimal_score(ns, ms, ni, mi, i as int, k),
                    forall|k: int| j as int <= k <= i as int + 1 ==>
                        (#[trigger] dp[k]) as int == optimal_score(ns, ms, ni, mi, i as int + 1, k),
                decreases i + 1 - j,
            {
                let right_idx = n - 1 - (i - j);
                proof {
                    optimal_score_bound(ns, ms, ni, mi, i as int + 1, j as int + 1);
                    optimal_score_bound(ns, ms, ni, mi, i as int + 1, j as int);
                    assert(-1_000_000 <= ms[i as int] as int * ns[j as int] as int <= 1_000_000)
                        by(nonlinear_arith)
                        requires -1000 <= ms[i as int] as int <= 1000, -1000 <= ns[j as int] as int <= 1000;
                    assert(0 <= right_idx as int && right_idx < n);
                    assert(-1_000_000 <= ms[i as int] as int * ns[right_idx as int] as int <= 1_000_000)
                        by(nonlinear_arith)
                        requires -1000 <= ms[i as int] as int <= 1000, -1000 <= ns[right_idx as int] as int <= 1000;
                }
                let left_choice = multipliers[i] * nums[j] + dp[j + 1];
                let right_choice = multipliers[i] * nums[right_idx] + dp[j];
                let val = if left_choice > right_choice { left_choice } else { right_choice };
                dp.set(j, val);
                j += 1;
            }
        }
        dp[0]
    }
}

}

