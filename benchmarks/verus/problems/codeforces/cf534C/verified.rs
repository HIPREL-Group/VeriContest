use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sum_maxima(maxima: Seq<i64>, end: int) -> int
    recommends 0 <= end <= maxima.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_maxima(maxima, end - 1) + maxima[end - 1] as int
    }
}

pub open spec fn other_sum_possible(maxima: Seq<i64>, i: int, rem: int) -> bool
    recommends 0 <= i < maxima.len(),
{
    maxima.len() - 1 <= rem <= sum_maxima(maxima, maxima.len() as int) - maxima[i] as int
}

pub open spec fn die_value_possible(maxima: Seq<i64>, total: int, i: int, x: int) -> bool
    recommends 0 <= i < maxima.len(),
{
    1 <= x <= maxima[i] as int && other_sum_possible(maxima, i, total - x)
}

pub open spec fn feasible_low(maxima: Seq<i64>, total: int, i: int) -> int
    recommends 0 <= i < maxima.len(),
{
    let raw = total - (sum_maxima(maxima, maxima.len() as int) - maxima[i] as int);
    if raw < 1 { 1 } else { raw }
}

pub open spec fn feasible_high(maxima: Seq<i64>, total: int, i: int) -> int
    recommends 0 <= i < maxima.len(),
{
    let raw = total - (maxima.len() as int - 1);
    if raw > maxima[i] as int { maxima[i] as int } else { raw }
}

pub open spec fn impossible_count_upto(maxima: Seq<i64>, total: int, i: int, limit: int) -> int
    recommends 0 <= i < maxima.len(), 0 <= limit <= maxima[i] as int,
    decreases limit,
{
    if limit <= 0 {
        0
    } else {
        impossible_count_upto(maxima, total, i, limit - 1)
            + if die_value_possible(maxima, total, i, limit) { 0int } else { 1int }
    }
}

pub open spec fn impossible_count(maxima: Seq<i64>, total: int, i: int) -> int
    recommends 0 <= i < maxima.len(),
{
    impossible_count_upto(maxima, total, i, maxima[i] as int)
}

pub open spec fn outside_interval_prefix(limit: int, lo: int, hi: int) -> int
    recommends 0 <= limit,
    decreases limit,
{
    if limit <= 0 {
        0
    } else {
        outside_interval_prefix(limit - 1, lo, hi)
            + if lo <= limit && limit <= hi { 0int } else { 1int }
    }
}

pub open spec fn outside_interval_count(limit: int, lo: int, hi: int) -> int
    recommends 0 <= limit, 1 <= lo, 1 <= hi,
{
    if hi < lo {
        limit
    } else if limit < lo {
        limit
    } else if limit <= hi {
        lo - 1
    } else {
        lo - 1 + (limit - hi)
    }
}

proof fn lemma_sum_maxima_step(maxima: Seq<i64>, end: int)
    requires
        0 <= end < maxima.len(),
    ensures
        sum_maxima(maxima, end + 1) == sum_maxima(maxima, end) + maxima[end] as int,
{
    reveal_with_fuel(sum_maxima, 2);
}

proof fn lemma_sum_maxima_bound(maxima: Seq<i64>, end: int)
    requires
        0 <= end <= maxima.len(),
        forall|i: int| 0 <= i < maxima.len() ==> 1 <= #[trigger] maxima[i] <= 1_000_000,
    ensures
        0 <= sum_maxima(maxima, end) <= end * 1_000_000,
    decreases end,
{
    if end <= 0 {
        reveal_with_fuel(sum_maxima, 1);
    } else {
        lemma_sum_maxima_bound(maxima, end - 1);
        reveal_with_fuel(sum_maxima, 2);
    }
}

proof fn lemma_feasible_bounds(maxima: Seq<i64>, total: int, i: int)
    requires
        1 <= maxima.len() <= 200_000,
        forall|j: int| 0 <= j < maxima.len() ==> 1 <= #[trigger] maxima[j] <= 1_000_000,
        maxima.len() <= total <= sum_maxima(maxima, maxima.len() as int),
        0 <= i < maxima.len(),
    ensures
        1 <= feasible_low(maxima, total, i) <= maxima[i] as int,
        1 <= feasible_high(maxima, total, i) <= maxima[i] as int,
{
    let sum_all = sum_maxima(maxima, maxima.len() as int);
    let raw_low = total - (sum_all - maxima[i] as int);
    let raw_high = total - (maxima.len() as int - 1);
    assert(raw_low <= maxima[i] as int) by {
        assert(total <= sum_all);
    }
    assert(1 <= raw_high) by {
        assert(maxima.len() <= total);
    }
    if raw_low < 1 {
        assert(feasible_low(maxima, total, i) == 1);
    } else {
        assert(feasible_low(maxima, total, i) == raw_low);
    }
    if raw_high > maxima[i] as int {
        assert(feasible_high(maxima, total, i) == maxima[i] as int);
    } else {
        assert(feasible_high(maxima, total, i) == raw_high);
    }
}

proof fn lemma_value_possible_interval(maxima: Seq<i64>, total: int, i: int, x: int)
    requires
        1 <= maxima.len() <= 200_000,
        forall|j: int| 0 <= j < maxima.len() ==> 1 <= #[trigger] maxima[j] <= 1_000_000,
        maxima.len() <= total <= sum_maxima(maxima, maxima.len() as int),
        0 <= i < maxima.len(),
        1 <= x <= maxima[i] as int,
    ensures
        die_value_possible(maxima, total, i, x) <==> feasible_low(maxima, total, i) <= x <= feasible_high(maxima, total, i),
{
    let sum_all = sum_maxima(maxima, maxima.len() as int);
    let raw_low = total - (sum_all - maxima[i] as int);
    let raw_high = total - (maxima.len() as int - 1);
    lemma_feasible_bounds(maxima, total, i);
    assert(die_value_possible(maxima, total, i, x) ==> feasible_low(maxima, total, i) <= x <= feasible_high(maxima, total, i)) by {
        if die_value_possible(maxima, total, i, x) {
            assert(other_sum_possible(maxima, i, total - x));
            assert(raw_low <= x) by {
                assert(total - x <= sum_all - maxima[i] as int);
                assert(raw_low == total - (sum_all - maxima[i] as int));
            }
            assert(x <= raw_high) by {
                assert(maxima.len() as int - 1 <= total - x);
                assert(raw_high == total - (maxima.len() as int - 1));
            }
            if raw_low < 1 {
                assert(feasible_low(maxima, total, i) == 1);
            } else {
                assert(feasible_low(maxima, total, i) == raw_low);
            }
            if raw_high > maxima[i] as int {
                assert(feasible_high(maxima, total, i) == maxima[i] as int);
            } else {
                assert(feasible_high(maxima, total, i) == raw_high);
            }
        }
    }
    assert(feasible_low(maxima, total, i) <= x <= feasible_high(maxima, total, i) ==> die_value_possible(maxima, total, i, x)) by {
        if feasible_low(maxima, total, i) <= x <= feasible_high(maxima, total, i) {
            if raw_low < 1 {
                assert(feasible_low(maxima, total, i) == 1);
                assert(raw_low <= 1);
                assert(raw_low <= x);
            } else {
                assert(feasible_low(maxima, total, i) == raw_low);
                assert(raw_low <= x);
            }
            if raw_high > maxima[i] as int {
                assert(feasible_high(maxima, total, i) == maxima[i] as int);
                assert(x <= maxima[i] as int);
                assert(x <= raw_high);
            } else {
                assert(feasible_high(maxima, total, i) == raw_high);
                assert(x <= raw_high);
            }
            assert(maxima.len() as int - 1 <= total - x) by {
                assert(x <= raw_high);
                assert(raw_high == total - (maxima.len() as int - 1));
            }
            assert(total - x <= sum_all - maxima[i] as int) by {
                assert(raw_low <= x);
                assert(raw_low == total - (sum_all - maxima[i] as int));
            }
        }
    }
}

proof fn lemma_impossible_count_interval(maxima: Seq<i64>, total: int, i: int, limit: int)
    requires
        1 <= maxima.len() <= 200_000,
        forall|j: int| 0 <= j < maxima.len() ==> 1 <= #[trigger] maxima[j] <= 1_000_000,
        maxima.len() <= total <= sum_maxima(maxima, maxima.len() as int),
        0 <= i < maxima.len(),
        0 <= limit <= maxima[i] as int,
    ensures
        impossible_count_upto(maxima, total, i, limit)
            == outside_interval_prefix(limit, feasible_low(maxima, total, i), feasible_high(maxima, total, i)),
    decreases limit,
{
    if limit <= 0 {
        reveal_with_fuel(impossible_count_upto, 1);
        reveal_with_fuel(outside_interval_prefix, 1);
    } else {
        lemma_impossible_count_interval(maxima, total, i, limit - 1);
        lemma_value_possible_interval(maxima, total, i, limit);
        reveal_with_fuel(impossible_count_upto, 2);
        reveal_with_fuel(outside_interval_prefix, 2);
    }
}

proof fn lemma_outside_interval_prefix_closed_form(limit: int, lo: int, hi: int)
    requires
        0 <= limit,
        1 <= lo,
        1 <= hi,
    ensures
        outside_interval_prefix(limit, lo, hi) == outside_interval_count(limit, lo, hi),
    decreases limit,
{
    if limit <= 0 {
        reveal_with_fuel(outside_interval_prefix, 1);
    } else {
        lemma_outside_interval_prefix_closed_form(limit - 1, lo, hi);
        reveal_with_fuel(outside_interval_prefix, 2);
        if hi < lo {
            assert(outside_interval_count(limit - 1, lo, hi) == limit - 1);
            assert(outside_interval_count(limit, lo, hi) == limit);
        } else if limit < lo {
            assert(outside_interval_count(limit - 1, lo, hi) == limit - 1);
            assert(outside_interval_count(limit, lo, hi) == limit);
        } else if limit == lo {
            assert(outside_interval_count(limit - 1, lo, hi) == limit - 1);
            assert(outside_interval_count(limit, lo, hi) == lo - 1);
        } else if limit <= hi {
            assert(outside_interval_count(limit - 1, lo, hi) == lo - 1);
            assert(outside_interval_count(limit, lo, hi) == lo - 1);
        } else if limit == hi + 1 {
            assert(outside_interval_count(limit - 1, lo, hi) == lo - 1);
            assert(outside_interval_count(limit, lo, hi) == lo - 1 + (limit - hi));
        } else {
            assert(hi + 1 < limit);
            assert(outside_interval_count(limit - 1, lo, hi) == lo - 1 + (limit - 1 - hi));
            assert(outside_interval_count(limit, lo, hi) == lo - 1 + (limit - hi));
        }
    }
}

impl Solution {
    pub fn impossible_face_counts(total: i64, maxima: Vec<i64>) -> (res: Vec<i64>)
        requires
            1 <= maxima.len() <= 200_000,
            forall|i: int| 0 <= i < maxima.len() ==> 1 <= #[trigger] maxima[i] <= 1_000_000,
            maxima.len() as int <= total as int <= sum_maxima(maxima@, maxima.len() as int),
        ensures
            res.len() == maxima.len(),
            forall|i: int| 0 <= i < res.len() ==> res[i] as int == impossible_count(maxima@, total as int, i),
    {
        let n = maxima.len();
        let mut sum_all = 0i64;
        let mut i = 0usize;
        while i < n
            invariant
                1 <= maxima.len() <= 200_000,
                forall|j: int| 0 <= j < maxima.len() ==> 1 <= #[trigger] maxima[j] <= 1_000_000,
                maxima.len() as int <= total as int <= sum_maxima(maxima@, maxima.len() as int),
                n == maxima.len(),
                0 <= i <= n,
                sum_all as int == sum_maxima(maxima@, i as int),
                0 <= sum_all as int <= i as int * 1_000_000,
            decreases n - i,
        {
            proof {
                lemma_sum_maxima_step(maxima@, i as int);
                lemma_sum_maxima_bound(maxima@, i as int + 1);
                assert(sum_maxima(maxima@, i as int + 1) == sum_maxima(maxima@, i as int) + maxima[i as int] as int);
            }
            sum_all += maxima[i];
            i += 1;
        }
        proof {
            assert(sum_all as int == sum_maxima(maxima@, n as int));
        }
        let mut res = Vec::new();
        i = 0;
        while i < n
            invariant
                1 <= maxima.len() <= 200_000,
                forall|j: int| 0 <= j < maxima.len() ==> 1 <= #[trigger] maxima[j] <= 1_000_000,
                maxima.len() as int <= total as int <= sum_maxima(maxima@, maxima.len() as int),
                n == maxima.len(),
                sum_all as int == sum_maxima(maxima@, n as int),
                i <= n,
                res.len() == i,
                forall|k: int| 0 <= k < i as int ==> res[k] as int == impossible_count(maxima@, total as int, k),
            decreases n - i,
        {
            let mut lo = total - (sum_all - maxima[i]);
            if lo < 1 {
                lo = 1;
            }
            let mut hi = total - (n as i64 - 1);
            if hi > maxima[i] {
                hi = maxima[i];
            }
            let bad = if hi < lo {
                maxima[i]
            } else if hi == maxima[i] {
                lo - 1
            } else {
                lo - 1 + maxima[i] - hi
            };
            proof {
                let lo_spec = feasible_low(maxima@, total as int, i as int);
                let hi_spec = feasible_high(maxima@, total as int, i as int);
                lemma_feasible_bounds(maxima@, total as int, i as int);
                lemma_impossible_count_interval(maxima@, total as int, i as int, maxima[i as int] as int);
                lemma_outside_interval_prefix_closed_form(maxima[i as int] as int, lo_spec, hi_spec);
                assert(lo as int == lo_spec) by {
                    let raw_low = total as int - (sum_maxima(maxima@, n as int) - maxima[i as int] as int);
                    if raw_low < 1 {
                        assert(lo == 1);
                        assert(lo_spec == 1);
                    } else {
                        assert(lo == raw_low as i64);
                        assert(lo_spec == raw_low);
                    }
                }
                assert(hi as int == hi_spec) by {
                    let raw_high = total as int - (n as int - 1);
                    if raw_high > maxima[i as int] as int {
                        assert(hi == maxima[i as int]);
                        assert(hi_spec == maxima[i as int] as int);
                    } else {
                        assert(hi == raw_high as i64);
                        assert(hi_spec == raw_high);
                    }
                }
                assert(lo_spec <= maxima[i as int] as int);
                assert(hi_spec <= maxima[i as int] as int);
                assert(bad as int == outside_interval_count(maxima[i as int] as int, lo_spec, hi_spec)) by {
                    if hi_spec < lo_spec {
                        assert(bad == maxima[i as int]);
                    } else if hi_spec == maxima[i as int] as int {
                        assert(bad == lo - 1);
                        assert(outside_interval_count(maxima[i as int] as int, lo_spec, hi_spec) == lo_spec - 1);
                    } else {
                        assert(hi_spec < maxima[i as int] as int);
                        assert(bad == lo - 1 + maxima[i as int] - hi);
                        assert(outside_interval_count(maxima[i as int] as int, lo_spec, hi_spec)
                            == lo_spec - 1 + (maxima[i as int] as int - hi_spec));
                    }
                }
                assert(impossible_count(maxima@, total as int, i as int)
                    == impossible_count_upto(maxima@, total as int, i as int, maxima[i as int] as int));
                assert(impossible_count(maxima@, total as int, i as int)
                    == outside_interval_prefix(maxima[i as int] as int, lo_spec, hi_spec));
                assert(impossible_count(maxima@, total as int, i as int)
                    == outside_interval_count(maxima[i as int] as int, lo_spec, hi_spec));
            }
            let ghost old_res = res@;
            res.push(bad);
            i += 1;
            proof {
                assert(res@ == old_res.push(bad));
                assert forall|k: int| 0 <= k < i as int implies res[k] as int == impossible_count(maxima@, total as int, k) by {
                    if k == i as int - 1 {
                        assert(res[k] == bad);
                    } else {
                        assert(k < i as int - 1);
                        assert(res[k] == old_res[k]);
                    }
                }
            }
        }
        res
    }
}

}
