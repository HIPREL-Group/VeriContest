use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn cost_to_reach(a: Seq<i64>, mid: int, target: int) -> int
        decreases a.len() - mid,
    {
        if mid >= a.len() {
            0int
        } else {
            let diff = if target > a[mid] { target - a[mid] } else { 0int };
            diff + Self::cost_to_reach(a, mid + 1, target)
        }
    }

    pub open spec fn spec_is_achievable(a: Seq<i64>, n: int, k: int, target: int) -> bool {
        Self::cost_to_reach(a, n / 2, target) <= k
    }

    pub open spec fn spec_sorted(a: Seq<i64>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
    }

    proof fn lemma_cost_nonneg(a: Seq<i64>, mid: int, target: int)
        ensures
            Self::cost_to_reach(a, mid, target) >= 0,
        decreases a.len() - mid,
    {
        if mid < a.len() {
            Self::lemma_cost_nonneg(a, mid + 1, target);
        }
    }

    proof fn lemma_cost_zero_sorted(a: Seq<i64>, mid: int, target: int)
        requires
            Self::spec_sorted(a),
            0 <= mid < a.len(),
            target <= a[mid],
        ensures
            Self::cost_to_reach(a, mid, target) == 0,
        decreases a.len() - mid,
    {
        reveal_with_fuel(Solution::cost_to_reach, 2);
        if mid + 1 < a.len() {
            assert(a[mid] <= a[mid + 1]);
            Self::lemma_cost_zero_sorted(a, mid + 1, target);
        }
    }

    proof fn lemma_cost_monotone(a: Seq<i64>, mid: int, t1: int, t2: int)
        requires
            t1 <= t2,
        ensures
            Self::cost_to_reach(a, mid, t1) <= Self::cost_to_reach(a, mid, t2),
        decreases a.len() - mid,
    {
        if mid < a.len() {
            Self::lemma_cost_monotone(a, mid + 1, t1, t2);
        }
    }

    proof fn lemma_cost_upper_bound(a: Seq<i64>, mid: int, target: int)
        requires
            0 <= mid <= a.len(),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 1,
            target >= 1,
        ensures
            Self::cost_to_reach(a, mid, target) <= (a.len() - mid) * target,
        decreases a.len() - mid,
    {
        if mid < a.len() {
            Self::lemma_cost_upper_bound(a, mid + 1, target);
            assert((a.len() - mid - 1) * target + target == (a.len() - mid) * target) by(nonlinear_arith)
                requires target >= 1;
        }
    }

    pub fn max_median(n: usize, k: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n <= 200000,
            n % 2 == 1,
            a.len() == n,
            1 <= k <= 1000000000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= 1000000000,
            Self::spec_sorted(a@),
        ensures
            forall|v: int| v <= res as int ==> Self::spec_is_achievable(a@, n as int, k as int, v),
            forall|v: int| v > res as int ==> !Self::spec_is_achievable(a@, n as int, k as int, v),
    {
        let m = n / 2;
        let mut lo: i64 = a[m];
        let mut hi: i64 = a[m] + k;
        proof {
            Self::lemma_cost_zero_sorted(a@, m as int, lo as int);
            Self::lemma_cost_nonneg(a@, (m + 1) as int, hi as int + 1);
        }
        while lo < hi
            invariant
                m == n / 2,
                a.len() == n,
                1 <= n <= 200000,
                n % 2 == 1,
                1 <= k <= 1000000000,
                forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a@[i] <= 1000000000,
                Self::spec_sorted(a@),
                1 <= lo <= hi,
                hi as int <= a@[m as int] as int + k as int,
                Self::spec_is_achievable(a@, n as int, k as int, lo as int),
                !Self::spec_is_achievable(a@, n as int, k as int, hi as int + 1),
            decreases hi - lo,
        {
            let mid_val: i64 = lo + (hi - lo + 1) / 2;
            let mut cost: i64 = 0;
            let mut i: usize = m;
            proof {
                Self::lemma_cost_nonneg(a@, m as int, mid_val as int);
                Self::lemma_cost_upper_bound(a@, m as int, mid_val as int);
                assert((n as int - m as int) * (mid_val as int) <= 400000000000000int) by(nonlinear_arith)
                    requires
                        0 <= n as int - m as int <= 200000,
                        1 <= mid_val as int <= 2000000000,
                ;
            }
            while i < n
                invariant
                    m <= i <= n,
                    m == n / 2,
                    a.len() == n,
                    1 <= n <= 200000,
                    1 <= k <= 1000000000,
                    1 <= mid_val,
                    mid_val as int <= a@[m as int] as int + k as int,
                    forall|j: int| 0 <= j < n ==> 1 <= #[trigger] a@[j] <= 1000000000,
                    0 <= cost,
                    cost as int + Self::cost_to_reach(a@, i as int, mid_val as int) == Self::cost_to_reach(a@, m as int, mid_val as int),
                    Self::cost_to_reach(a@, i as int, mid_val as int) >= 0,
                    Self::cost_to_reach(a@, m as int, mid_val as int) <= 400000000000000,
                decreases n - i,
            {
                proof {
                    Self::lemma_cost_nonneg(a@, (i + 1) as int, mid_val as int);
                }
                if mid_val > a[i] {
                    proof {
                        assert(Self::cost_to_reach(a@, i as int, mid_val as int) == (mid_val as int - a@[i as int] as int) + Self::cost_to_reach(a@, (i + 1) as int, mid_val as int));
                    }
                    cost = cost + (mid_val - a[i]);
                }
                i = i + 1;
            }
            if cost <= k {
                lo = mid_val;
            } else {
                hi = mid_val - 1;
            }
        }
        proof {
            assert forall|v: int| v <= lo as int implies Self::spec_is_achievable(a@, n as int, k as int, v) by {
                Self::lemma_cost_monotone(a@, (n / 2) as int, v, lo as int);
            }
            assert forall|v: int| v > lo as int implies !Self::spec_is_achievable(a@, n as int, k as int, v) by {
                Self::lemma_cost_monotone(a@, (n / 2) as int, lo as int + 1, v);
            }
        }
        lo
    }
}

}
