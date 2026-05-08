use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn dp_inf() -> i64 {
    300_000i64
}

pub open spec fn is_land_or_log(a: Seq<u8>, p: int) -> bool {
    p == 0 || p == a.len() + 1 || (1 <= p && p <= a.len() && a[p - 1] == 2u8)
}

pub open spec fn is_water(a: Seq<u8>, p: int) -> bool {
    1 <= p && p <= a.len() && a[p - 1] == 0u8
}

pub open spec fn is_croc(a: Seq<u8>, p: int) -> bool {
    1 <= p && p <= a.len() && a[p - 1] == 1u8
}

pub open spec fn land_cost(a: Seq<u8>, p: int) -> int {
    if is_water(a, p) { 1int } else { 0int }
}

pub open spec fn dp_min_pred(dp_prev: Seq<i64>, a: Seq<u8>, m: int, p: int, j_start: int, j_end: int) -> i64
    recommends
        dp_prev.len() == p,
        0 <= j_start <= j_end <= p,
        m >= 1,
    decreases j_end - j_start,
{
    if j_start >= j_end {
        dp_inf()
    } else {
        let prev = dp_min_pred(dp_prev, a, m, p, j_start + 1, j_end);
        let cur = dp_prev[j_start];
        let valid = if cur >= dp_inf() {
            false
        } else if is_land_or_log(a, j_start) {
            j_start + 1 <= p && p <= j_start + m
        } else if is_water(a, j_start) {
            p == j_start + 1
        } else {
            false
        };
        if valid {
            let cand = (cur as int + land_cost(a, p)) as i64;
            if cand < prev { cand } else { prev }
        } else {
            prev
        }
    }
}

pub open spec fn dp_at(dp_prev: Seq<i64>, a: Seq<u8>, m: int, p: int) -> i64
    recommends
        dp_prev.len() == p,
        0 <= p <= a.len() + 1,
        m >= 1,
{
    if p == 0 {
        0i64
    } else if is_croc(a, p) {
        dp_inf()
    } else {
        let lo = if p > m { p - m } else { 0int };
        dp_min_pred(dp_prev, a, m, p, lo, p)
    }
}

pub open spec fn compute_dp_upto(a: Seq<u8>, m: int, k_max: int) -> Seq<i64>
    recommends
        0 <= k_max <= a.len() + 1,
        m >= 1,
    decreases k_max,
{
    if k_max <= 0 {
        seq![0i64]
    } else {
        let prev = compute_dp_upto(a, m, k_max - 1);
        prev.push(dp_at(prev, a, m, k_max))
    }
}

pub open spec fn compute_dp(a: Seq<u8>, m: int) -> Seq<i64>
    recommends
        m >= 1,
{
    compute_dp_upto(a, m, a.len() as int + 1)
}


proof fn lemma_compute_dp_upto_len(a: Seq<u8>, m: int, k_max: int)
    requires
        0 <= k_max,
        m >= 1,
    ensures
        compute_dp_upto(a, m, k_max).len() == k_max + 1,
    decreases k_max,
{
    if k_max <= 0 {
    } else {
        lemma_compute_dp_upto_len(a, m, k_max - 1);
    }
}


proof fn lemma_compute_dp_upto_idx(a: Seq<u8>, m: int, k_max: int, idx: int)
    requires
        0 <= k_max,
        0 <= idx <= k_max,
        m >= 1,
    ensures
        compute_dp_upto(a, m, k_max)[idx] == compute_dp_upto(a, m, idx)[idx],
    decreases k_max - idx,
{
    if k_max == idx {
    } else {
        lemma_compute_dp_upto_idx(a, m, k_max - 1, idx);
        lemma_compute_dp_upto_len(a, m, k_max - 1);
    }
}

impl Solution {
    pub fn can_cross(a: Vec<u8>, m: usize, k: i64) -> (result: bool)
        requires
            1 <= a.len() <= 200_000,
            1 <= m <= 10,
            0 <= k <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 2,
        ensures
            ({
                let dp = compute_dp(a@, m as int);
                let final_dp = dp[a.len() as int + 1];
                result == (final_dp < dp_inf() && final_dp <= k)
            }),
    {
        let n = a.len();
        let inf: i64 = 300_000;
        let mut dp: Vec<i64> = Vec::with_capacity(n + 2);
        dp.push(0);
        proof {
            assert(dp@ == seq![0i64]);
            assert(compute_dp_upto(a@, m as int, 0) == seq![0i64]);
            assert(dp@ == compute_dp_upto(a@, m as int, 0));
        }
        let mut p: usize = 1;
        while p <= n + 1
            invariant
                1 <= p <= n + 2,
                n == a.len(),
                1 <= n <= 200_000,
                1 <= m <= 10,
                inf == 300_000i64,
                forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 2,
                dp.len() == p,
                dp@ == compute_dp_upto(a@, m as int, (p - 1) as int),
            decreases (n + 2) - p,
        {
            let val = if p <= n && a[p - 1] == 1 {
                inf
            } else {
                let lo: usize = if p > m { p - m } else { 0 };
                let mut best = inf;
                let mut jj: usize = p;
                while jj > lo
                    invariant
                        lo <= jj <= p,
                        n == a.len(),
                        1 <= n <= 200_000,
                        1 <= m <= 10,
                        1 <= p <= n + 1,
                        lo as int == if (p as int) > (m as int) { (p as int) - (m as int) } else { 0int },
                        inf == 300_000i64,
                        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 2,
                        dp.len() == p,
                        dp@ == compute_dp_upto(a@, m as int, (p - 1) as int),
                        best == dp_min_pred(dp@, a@, m as int, p as int, jj as int, p as int),
                    decreases jj,
                {
                    jj = jj - 1;
                    proof {
                        reveal_with_fuel(dp_min_pred, 2);
                    }
                    let djv = dp[jj];
                    if djv < inf {
                        let valid = if jj == 0 || jj == n + 1 || (1 <= jj && jj <= n && a[jj - 1] == 2) {
                            jj + 1 <= p && p <= jj + m
                        } else if 1 <= jj && jj <= n && a[jj - 1] == 0 {
                            p == jj + 1
                        } else {
                            false
                        };
                        if valid {
                            let cost: i64 = if p >= 1 && p <= n && a[p - 1] == 0 { 1 } else { 0 };
                            let cand = djv + cost;
                            if cand < best {
                                best = cand;
                            }
                        }
                    }
                }
                proof {
                    assert(jj == lo);
                    assert(best == dp_min_pred(dp@, a@, m as int, p as int, lo as int, p as int));
                    if !(p as int <= a@.len() as int && a@[(p - 1) as int] == 1u8) {
                        assert(!is_croc(a@, p as int));
                        assert(dp_at(dp@, a@, m as int, p as int) == dp_min_pred(dp@, a@, m as int, p as int, lo as int, p as int));
                    }
                }
                best
            };
            proof {
                if p <= n && a[p - 1] == 1 {
                    assert(is_croc(a@, p as int));
                    assert(dp_at(dp@, a@, m as int, p as int) == dp_inf());
                    assert(val == dp_inf());
                } else {
                    assert(!is_croc(a@, p as int));
                    assert(val == dp_at(dp@, a@, m as int, p as int));
                }
            }
            dp.push(val);
            proof {
                reveal_with_fuel(compute_dp_upto, 2);
                let dp_old = compute_dp_upto(a@, m as int, (p - 1) as int);
                assert(compute_dp_upto(a@, m as int, p as int) == dp_old.push(dp_at(dp_old, a@, m as int, p as int)));
                assert(dp@ == compute_dp_upto(a@, m as int, p as int));
            }
            p = p + 1;
        }
        proof {
            assert(p == n + 2);
            assert(dp@ == compute_dp_upto(a@, m as int, (n + 1) as int));
            assert(compute_dp(a@, m as int) == compute_dp_upto(a@, m as int, n as int + 1));
            lemma_compute_dp_upto_len(a@, m as int, n as int + 1);
            assert(dp@.len() == n + 2);
        }
        dp[n + 1] < inf && dp[n + 1] <= k
    }
}

}
