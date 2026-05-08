use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_prefix_sum(seq: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= seq.len(),
    decreases
        k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(seq, k - 1) + seq[k - 1] as int
    }
}

pub open spec fn spec_feasible(sum_time: int, min_s: Seq<i32>, max_s: Seq<i32>, d: int) -> bool {
    spec_prefix_sum(min_s, d) <= sum_time && sum_time <= spec_prefix_sum(max_s, d)
}

pub open spec fn spec_greedy_rem(
    k: int,
    init_rem: int,
    min_s: Seq<i32>,
    max_s: Seq<i32>,
    d: int,
) -> int
    recommends
        0 <= k <= d,
        d <= min_s.len(),
        d <= max_s.len(),
    decreases k,
{
    if k <= 0 {
        init_rem
    } else {
        let prev_rem = spec_greedy_rem(k - 1, init_rem, min_s, max_s, d);
        let cap = max_s[k - 1] as int - min_s[k - 1] as int;
        let add = if prev_rem > cap {
            cap
        } else {
            prev_rem
        };
        prev_rem - add
    }
}

pub open spec fn spec_slack_sum(min_s: Seq<i32>, max_s: Seq<i32>, d: int) -> int
    recommends
        0 <= d <= min_s.len() && d <= max_s.len(),
    decreases d,
{
    if d <= 0 {
        0
    } else {
        spec_slack_sum(min_s, max_s, d - 1) + (max_s[d - 1] as int - min_s[d - 1] as int)
    }
}

proof fn lemma_slack_sum_equals_max_minus_min(min_s: Seq<i32>, max_s: Seq<i32>, d: int)
    requires
        0 <= d <= min_s.len(),
        d <= max_s.len(),
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
    ensures
        spec_slack_sum(min_s, max_s, d) == spec_prefix_sum(max_s, d) - spec_prefix_sum(min_s, d),
    decreases d,
{
    if d == 0 {
        assert(spec_slack_sum(min_s, max_s, 0) == 0);
        assert(spec_prefix_sum(max_s, 0) == 0);
        assert(spec_prefix_sum(min_s, 0) == 0);
    } else {
        assert((min_s[d - 1] as int) <= (max_s[d - 1] as int));
        lemma_slack_sum_equals_max_minus_min(min_s, max_s, d - 1);
        lemma_prefix_sum_step(min_s, d);
        lemma_prefix_sum_step(max_s, d);
        assert(spec_slack_sum(min_s, max_s, d) == spec_slack_sum(min_s, max_s, d - 1)
            + (max_s[d - 1] as int - min_s[d - 1] as int));
        assert(spec_prefix_sum(max_s, d) - spec_prefix_sum(min_s, d) == spec_prefix_sum(max_s, d - 1)
            - spec_prefix_sum(min_s, d - 1) + (max_s[d - 1] as int - min_s[d - 1] as int));
    }
}

proof fn lemma_feasible_implies_remainder_le_slack(
    sum_time: int,
    min_s: Seq<i32>,
    max_s: Seq<i32>,
    d: int,
)
    requires
        0 <= d <= min_s.len(),
        d <= max_s.len(),
        spec_feasible(sum_time, min_s, max_s, d),
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
    ensures
        sum_time - spec_prefix_sum(min_s, d) <= spec_slack_sum(min_s, max_s, d),
{
    lemma_slack_sum_equals_max_minus_min(min_s, max_s, d);
    assert(spec_feasible(sum_time, min_s, max_s, d));
    assert(spec_prefix_sum(min_s, d) <= sum_time);
    assert(sum_time <= spec_prefix_sum(max_s, d));
    assert(
        sum_time - spec_prefix_sum(min_s, d) <= spec_prefix_sum(max_s, d) - spec_prefix_sum(min_s, d)
    );
    assert(
        sum_time - spec_prefix_sum(min_s, d) <= spec_slack_sum(min_s, max_s, d)
    );
}

proof fn lemma_slack_sum_monotone(min_s: Seq<i32>, max_s: Seq<i32>, k: int, d: int)
    requires
        0 <= k <= d,
        d <= min_s.len(),
        d <= max_s.len(),
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
    ensures
        spec_slack_sum(min_s, max_s, k) <= spec_slack_sum(min_s, max_s, d),
    decreases d - k,
{
    if k == d {
        assert(spec_slack_sum(min_s, max_s, k) <= spec_slack_sum(min_s, max_s, d));
    } else {
        assert(k < d);
        lemma_slack_sum_monotone(min_s, max_s, k, d - 1);
        assert((min_s[d - 1] as int) <= (max_s[d - 1] as int));
        lemma_slack_sum_step_suffix(min_s, max_s, d);
        assert(spec_slack_sum(min_s, max_s, d) == spec_slack_sum(min_s, max_s, d - 1)
            + (max_s[d - 1] as int - min_s[d - 1] as int));
        assert(spec_slack_sum(min_s, max_s, d - 1) >= spec_slack_sum(min_s, max_s, k));
        assert(max_s[d - 1] as int - min_s[d - 1] as int >= 0);
        assert(spec_slack_sum(min_s, max_s, d) >= spec_slack_sum(min_s, max_s, d - 1));
        assert(spec_slack_sum(min_s, max_s, d) >= spec_slack_sum(min_s, max_s, k));
    }
}

proof fn lemma_slack_sum_step_suffix(min_s: Seq<i32>, max_s: Seq<i32>, k: int)
    requires
        0 < k <= min_s.len(),
        k <= max_s.len(),
        forall |ii: int| 0 <= ii < k ==> (min_s[ii] as int) <= (max_s[ii] as int),
    ensures
        spec_slack_sum(min_s, max_s, k)
            == spec_slack_sum(min_s, max_s, k - 1) + (max_s[k - 1] as int - min_s[k - 1] as int),
    decreases k,
{
    if k == 1 {
        assert(spec_slack_sum(min_s, max_s, 0) == 0);
        assert(spec_slack_sum(min_s, max_s, 1) == spec_slack_sum(min_s, max_s, 0)
            + (max_s[0] as int - min_s[0] as int));
    } else {
        assert((min_s[k - 1] as int) <= (max_s[k - 1] as int));
        lemma_slack_sum_step_suffix(min_s, max_s, k - 1);
        assert(spec_slack_sum(min_s, max_s, k) == spec_slack_sum(min_s, max_s, k - 1)
            + (max_s[k - 1] as int - min_s[k - 1] as int));
    }
}

proof fn lemma_greedy_rem_nonneg(
    k: int,
    init_rem: int,
    min_s: Seq<i32>,
    max_s: Seq<i32>,
    d: int,
)
    requires
        0 <= k <= d,
        1 <= d <= min_s.len(),
        d <= max_s.len(),
        0 <= init_rem,
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
    ensures
        spec_greedy_rem(k, init_rem, min_s, max_s, d) >= 0,
    decreases k,
{
    if k == 0 {
        assert(spec_greedy_rem(0, init_rem, min_s, max_s, d) == init_rem);
    } else {
        assert(0 < k <= d);
        assert((k - 1) < d);
        lemma_greedy_rem_nonneg(k - 1, init_rem, min_s, max_s, d);
        let prev = spec_greedy_rem(k - 1, init_rem, min_s, max_s, d);
        let cap = max_s[k - 1] as int - min_s[k - 1] as int;
        assert(prev >= 0);
        assert(cap >= 0);
        assert(spec_greedy_rem(k, init_rem, min_s, max_s, d) == prev - if prev > cap {
            cap
        } else {
            prev
        });
        assert(if prev > cap {
            prev - cap
        } else {
            0
        } >= 0);
    }
}

proof fn lemma_greedy_rem_suffix_bound(
    k: int,
    init_rem: int,
    min_s: Seq<i32>,
    max_s: Seq<i32>,
    d: int,
)
    requires
        0 <= k <= d,
        1 <= d <= min_s.len(),
        d <= max_s.len(),
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
        0 <= init_rem <= spec_slack_sum(min_s, max_s, d),
    ensures
        spec_greedy_rem(k, init_rem, min_s, max_s, d)
            <= spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k),
    decreases k,
{
    if k == 0 {
        assert(spec_greedy_rem(0, init_rem, min_s, max_s, d) == init_rem);
        assert(spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, 0) == spec_slack_sum(min_s, max_s, d));
    } else {
        assert(0 < k <= d);
        lemma_greedy_rem_suffix_bound(k - 1, init_rem, min_s, max_s, d);
        let prev = spec_greedy_rem(k - 1, init_rem, min_s, max_s, d);
        let cap = max_s[k - 1] as int - min_s[k - 1] as int;
        assert((min_s[k - 1] as int) <= (max_s[k - 1] as int));
        assert(prev <= spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k - 1));
        lemma_slack_sum_step_suffix(min_s, max_s, k);
        assert(spec_slack_sum(min_s, max_s, k) == spec_slack_sum(min_s, max_s, k - 1) + cap);
        assert(
            spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k - 1)
                == (spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k)) + cap
        );
        assert(spec_greedy_rem(k, init_rem, min_s, max_s, d) == prev - if prev > cap {
            cap
        } else {
            prev
        });
        if prev > cap {
            assert(spec_greedy_rem(k, init_rem, min_s, max_s, d) == prev - cap);
            assert(prev <= (spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k)) + cap);
            assert(prev - cap <= spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k));
        } else {
            assert(spec_greedy_rem(k, init_rem, min_s, max_s, d) == 0);
            lemma_slack_sum_monotone(min_s, max_s, k, d);
            assert(0 <= spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, k));
        }
    }
}

proof fn lemma_feasible_greedy_rem_zero(
    sum_time: int,
    init_rem: int,
    min_s: Seq<i32>,
    max_s: Seq<i32>,
    d: int,
)
    requires
        1 <= d <= min_s.len(),
        d <= max_s.len(),
        forall |ii: int| 0 <= ii < d ==> (min_s[ii] as int) <= (max_s[ii] as int),
        init_rem == sum_time - spec_prefix_sum(min_s, d),
        spec_feasible(sum_time, min_s, max_s, d),
    ensures
        spec_greedy_rem(d, init_rem, min_s, max_s, d) == 0,
{
    lemma_feasible_implies_remainder_le_slack(sum_time, min_s, max_s, d);
    assert(0 <= init_rem);
    assert(init_rem <= spec_slack_sum(min_s, max_s, d));
    lemma_greedy_rem_suffix_bound(d, init_rem, min_s, max_s, d);
    assert(
        spec_greedy_rem(d, init_rem, min_s, max_s, d)
            <= spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, d)
    );
    assert(spec_slack_sum(min_s, max_s, d) - spec_slack_sum(min_s, max_s, d) == 0);
    assert(spec_greedy_rem(d, init_rem, min_s, max_s, d) <= 0);
    lemma_greedy_rem_nonneg(d, init_rem, min_s, max_s, d);
    assert(spec_greedy_rem(d, init_rem, min_s, max_s, d) >= 0);
    assert(spec_greedy_rem(d, init_rem, min_s, max_s, d) == 0);
}

proof fn lemma_prefix_sum_nonneg(seq: Seq<i32>, k: int)
    requires
        0 <= k <= seq.len(),
        forall |i: int| 0 <= i < k ==> (seq[i] as int) >= 0,
    ensures
        spec_prefix_sum(seq, k) >= 0,
    decreases k,
{
    if k == 0 {
        assert(spec_prefix_sum(seq, 0) == 0);
    } else {
        lemma_prefix_sum_nonneg(seq, k - 1);
        lemma_prefix_sum_step(seq, k);
        assert((seq[k - 1] as int) >= 0);
        assert(spec_prefix_sum(seq, k) == spec_prefix_sum(seq, k - 1) + seq[k - 1] as int);
        assert(spec_prefix_sum(seq, k - 1) >= 0);
    }
}

proof fn lemma_prefix_sum_step(seq: Seq<i32>, k: int)
    requires
        0 < k <= seq.len(),
    ensures
        spec_prefix_sum(seq, k) == spec_prefix_sum(seq, k - 1) + seq[k - 1] as int,
{
    assert(spec_prefix_sum(seq, k) == spec_prefix_sum(seq, k - 1) + seq[k - 1] as int);
}

proof fn lemma_prefix_sum_prefix_unchanged_at(seq: Seq<i32>, k: int, m: int, v: i32)
    requires
        0 <= k <= m < seq.len(),
    ensures
        spec_prefix_sum(seq.update(m, v), k) == spec_prefix_sum(seq, k),
    decreases
        k,
{
    if k == 0 {
        assert(spec_prefix_sum(seq.update(m, v), 0) == 0);
        assert(spec_prefix_sum(seq, 0) == 0);
    } else {
        lemma_prefix_sum_prefix_unchanged_at(seq, k - 1, m, v);
        lemma_prefix_sum_step(seq.update(m, v), k);
        lemma_prefix_sum_step(seq, k);
        assert(spec_prefix_sum(seq.update(m, v), k) == spec_prefix_sum(seq.update(m, v), k - 1)
            + seq.update(m, v)[k - 1] as int);
        assert(spec_prefix_sum(seq.update(m, v), k - 1) == spec_prefix_sum(seq, k - 1));
        assert(seq.update(m, v)[k - 1] == seq[k - 1]);
        assert(spec_prefix_sum(seq, k) == spec_prefix_sum(seq, k - 1) + seq[k - 1] as int);
    }
}

proof fn lemma_prefix_sum_at_update(seq: Seq<i32>, k: int, v: i32)
    requires
        0 <= k < seq.len(),
    ensures
        spec_prefix_sum(seq.update(k, v), k + 1) == spec_prefix_sum(seq, k) + v as int,
{
    lemma_prefix_sum_prefix_unchanged_at(seq, k, k, v);
    lemma_prefix_sum_step(seq.update(k, v), k + 1);
    assert(spec_prefix_sum(seq.update(k, v), k + 1) == spec_prefix_sum(seq.update(k, v), k)
        + seq.update(k, v)[k] as int);
    assert(seq.update(k, v)[k] == v);
    assert(spec_prefix_sum(seq.update(k, v), k + 1) == spec_prefix_sum(seq, k) + v as int);
}

impl Solution {
    pub fn before_exam_schedule(
        d: usize,
        sum_time: i32,
        min_t: Vec<i32>,
        max_t: Vec<i32>,
    ) -> (res: (bool, Vec<i32>))
        requires
            (d as int) >= 1 && (d as int) <= 30,
            d == min_t.len(),
            d == max_t.len(),
            0 <= sum_time <= 240,
            forall |i: int|
                0 <= i < d as int ==> 0 <= (#[trigger] min_t@[i] as int) && (min_t@[i] as int) <= (max_t@[i] as int)
                    && (max_t@[i] as int) <= 8,
        ensures
            res.0 == spec_feasible(sum_time as int, min_t@, max_t@, d as int),
            !res.0 ==> res.1.len() == 0,
            res.0 ==> res.1.len() == d,
            res.0 ==> spec_prefix_sum(res.1@, d as int) == (sum_time as int),
            res.0 ==> forall |i: int|
                0 <= i < d as int ==> (min_t@[i] as int) <= (#[trigger] res.1@[i] as int)
                    && (res.1@[i] as int) <= (max_t@[i] as int),
    {
        proof {
            assert(forall |i: int|
                0 <= i < d as int ==> 0 <= (#[trigger] min_t@[i] as int) && (min_t@[i] as int) <= (max_t@[i] as int)
                    && (max_t@[i] as int) <= 8);
            assert((d as int) >= 1 && (d as int) <= 30);
        }
        let mut sum_min: i32 = 0;
        let mut i: usize = 0;
        while i < d
            invariant
                i <= d,
                (d as int) >= 1 && (d as int) <= 30,
                d == min_t.len(),
                d == max_t.len(),
                forall |ii: int|
                    0 <= ii < d as int ==> 0 <= (#[trigger] min_t@[ii] as int) && (min_t@[ii] as int) <= (max_t@[ii] as int)
                        && (max_t@[ii] as int) <= 8,
                (sum_min as int) == spec_prefix_sum(min_t@, i as int),
                (sum_min as int) <= (i as int) * 8,
            decreases d - i,
        {
            proof {
                assert(i < d);
                assert(0 <= (i as int) && (i as int) < (d as int));
                assert(0 <= (min_t@[i as int] as int));
                assert((min_t@[i as int] as int) <= (max_t@[i as int] as int));
                assert((max_t@[i as int] as int) <= 8);
                assert(d == min_t.len());
                assert(i < min_t.len());
                assert(0 < (i + 1) as int <= min_t@.len());
                lemma_prefix_sum_step(min_t@, (i + 1) as int);
                assert((sum_min as int) + (min_t@[i as int] as int) <= (i as int) * 8 + 8);
                assert((sum_min as int) + (min_t@[i as int] as int) <= (d as int) * 8);
                assert((d as int) * 8 <= 240);
            }
            sum_min = sum_min + min_t[i];
            i = i + 1;
            proof {
                assert((sum_min as int) == spec_prefix_sum(min_t@, i as int));
                assert((sum_min as int) <= (i as int) * 8);
            }
        }
        proof {
            assert((sum_min as int) == spec_prefix_sum(min_t@, d as int));
        }
        let mut sum_max: i32 = 0;
        i = 0;
        while i < d
            invariant
                i <= d,
                (d as int) >= 1 && (d as int) <= 30,
                d == min_t.len(),
                d == max_t.len(),
                forall |ii: int|
                    0 <= ii < d as int ==> 0 <= (#[trigger] min_t@[ii] as int) && (min_t@[ii] as int) <= (max_t@[ii] as int)
                        && (max_t@[ii] as int) <= 8,
                (sum_max as int) == spec_prefix_sum(max_t@, i as int),
                (sum_max as int) <= (i as int) * 8,
            decreases d - i,
        {
            proof {
                assert(i < d);
                assert(0 <= (i as int) && (i as int) < (d as int));
                assert(0 <= (min_t@[i as int] as int));
                assert((min_t@[i as int] as int) <= (max_t@[i as int] as int));
                assert((max_t@[i as int] as int) <= 8);
                assert(d == max_t.len());
                assert(i < max_t.len());
                assert(0 < (i + 1) as int <= max_t@.len());
                lemma_prefix_sum_step(max_t@, (i + 1) as int);
                assert((sum_max as int) + (max_t@[i as int] as int) <= (i as int) * 8 + 8);
                assert((sum_max as int) + (max_t@[i as int] as int) <= (d as int) * 8);
                assert((d as int) * 8 <= 240);
            }
            sum_max = sum_max + max_t[i];
            i = i + 1;
            proof {
                assert((sum_max as int) == spec_prefix_sum(max_t@, i as int));
                assert((sum_max as int) <= (i as int) * 8);
            }
        }
        proof {
            assert((sum_max as int) == spec_prefix_sum(max_t@, d as int));
        }
        if sum_time < sum_min || sum_time > sum_max {
            proof {
                assert((sum_min as int) == spec_prefix_sum(min_t@, d as int));
                assert((sum_max as int) == spec_prefix_sum(max_t@, d as int));
                if sum_time < sum_min {
                    assert((sum_time as int) < spec_prefix_sum(min_t@, d as int));
                } else {
                    assert(sum_time > sum_max);
                    assert((sum_time as int) > spec_prefix_sum(max_t@, d as int));
                }
                assert(!spec_feasible(sum_time as int, min_t@, max_t@, d as int));
            }
            return (false, Vec::new());
        }
        proof {
            assert((sum_min as int) <= (sum_time as int));
            assert((sum_time as int) <= (sum_max as int));
            assert((sum_time as int) - (sum_min as int) >= 0);
            assert((sum_min as int) == spec_prefix_sum(min_t@, d as int));
            assert(forall |i: int|
                0 <= i < d as int ==> 0 <= (#[trigger] min_t@[i] as int) && (min_t@[i] as int) <= (max_t@[i] as int)
                    && (max_t@[i] as int) <= 8);
            lemma_prefix_sum_nonneg(min_t@, d as int);
            assert((sum_min as int) <= (d as int) * 8);
            assert((sum_min as int) <= 240);
            assert((sum_time as int) >= 0 && (sum_time as int) <= 240);
        }
        let mut rem: i32 = sum_time - sum_min;
        let initial_rem: i32 = rem;
        let mut applied: i32 = 0;
        let mut sched: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < d
            invariant
                j <= d,
                (d as int) >= 1 && (d as int) <= 30,
                d == min_t.len(),
                sched.len() == j,
                forall |t: int|
                    0 <= t < (j as int) ==> sched@[t] == min_t@[t],
            decreases d - j,
        {
            proof {
                assert(j < d);
                assert(j < min_t.len());
            }
            sched.push(min_t[j]);
            j = j + 1;
        }
        proof {
            assert(sched@ == min_t@);
            assert(spec_prefix_sum(sched@, 0) == 0);
            assert(spec_prefix_sum(min_t@, 0) == 0);
            assert((initial_rem as int) == (sum_time as int) - (sum_min as int));
            assert(0 <= rem);
            assert((rem as int) == (sum_time as int) - spec_prefix_sum(min_t@, d as int));
            assert((rem as int) == spec_greedy_rem(0, (initial_rem as int), min_t@, max_t@, d as int));
        }
        let mut k: usize = 0;
        while k < d
            invariant
                k <= d,
                (d as int) >= 1 && (d as int) <= 30,
                d == min_t.len(),
                d == max_t.len(),
                forall |ii: int|
                    0 <= ii < d as int ==> 0 <= (#[trigger] min_t@[ii] as int) && (min_t@[ii] as int) <= (max_t@[ii] as int)
                        && (max_t@[ii] as int) <= 8,
                sched.len() == d,
                0 <= rem,
                (rem as int) == spec_greedy_rem(k as int, (initial_rem as int), min_t@, max_t@, d as int),
                applied + rem == initial_rem,
                spec_prefix_sum(sched@, k as int) == spec_prefix_sum(min_t@, k as int) + (applied as int),
                (rem as int) == (sum_time as int) - spec_prefix_sum(min_t@, d as int)
                    + spec_prefix_sum(min_t@, k as int) - spec_prefix_sum(sched@, k as int),
                forall |t: int|
                    0 <= t < (k as int) ==> (min_t@[t] as int) <= (sched@[t] as int)
                        && (sched@[t] as int) <= (max_t@[t] as int),
                forall |t: int|
                    (k as int) <= t < (d as int) ==> sched@[t] == min_t@[t],
            decreases d - k,
        {
            proof {
                assert(k < d);
                assert(0 <= (k as int) && (k as int) < (d as int));
                assert(0 <= (min_t@[k as int] as int));
                assert((min_t@[k as int] as int) <= (max_t@[k as int] as int));
                assert((max_t@[k as int] as int) <= 8);
                assert(k < max_t.len());
                assert(k < min_t.len());
            }
            let cap: i32 = max_t[k] - min_t[k];
            let add: i32 = if rem > cap { cap } else { rem };
            proof {
                assert((min_t@[k as int] as int) + (add as int) <= (max_t@[k as int] as int));
                assert((min_t@[k as int] as int) <= (min_t@[k as int] as int) + (add as int));
                assert(add <= rem);
                assert(rem - add >= 0);
            }
            let new_val: i32 = min_t[k] + add;
            let ghost old_sched = sched@;
            sched.set(k, new_val);
            proof {
                assert(sched@ == old_sched.update(k as int, new_val));
                lemma_prefix_sum_at_update(old_sched, k as int, new_val);
                assert(spec_prefix_sum(sched@, (k + 1) as int)
                    == spec_prefix_sum(old_sched, k as int) + (new_val as int));
                assert(spec_prefix_sum(sched@, (k + 1) as int)
                    == spec_prefix_sum(old_sched, k as int) + (min_t@[k as int] as int) + (add as int));
                assert(
                    spec_prefix_sum(sched@, (k + 1) as int) == spec_prefix_sum(min_t@, (k + 1) as int)
                        + (applied as int) + (add as int)
                );
            }
            proof {
                assert((applied as int) + (add as int) <= (initial_rem as int));
            }
            applied = applied + add;
            rem = rem - add;
            k = k + 1;
            proof {
                assert((rem as int) == spec_greedy_rem(k as int, (initial_rem as int), min_t@, max_t@, d as int));
            }
        }
        proof {
            assert(k == d);
            assert((rem as int) == spec_greedy_rem(d as int, (initial_rem as int), min_t@, max_t@, d as int));
            assert forall|dd: int| 0 <= dd < d as int implies (min_t@[dd] as int) <= (max_t@[dd] as int) by {
                assert(forall |i: int|
                    0 <= i < d as int ==> 0 <= (#[trigger] min_t@[i] as int) && (min_t@[i] as int) <= (max_t@[i] as int)
                        && (max_t@[i] as int) <= 8);
            };
            lemma_feasible_greedy_rem_zero(
                sum_time as int,
                (initial_rem as int),
                min_t@,
                max_t@,
                d as int,
            );
            assert(spec_greedy_rem(d as int, (initial_rem as int), min_t@, max_t@, d as int) == 0);
            assert(rem == 0);
            assert(applied + rem == initial_rem);
            assert(spec_prefix_sum(sched@, d as int) == spec_prefix_sum(min_t@, d as int) + (applied as int));
            assert(spec_prefix_sum(min_t@, d as int) == (sum_min as int));
            assert((initial_rem as int) == (sum_time as int) - (sum_min as int));
            assert(spec_prefix_sum(sched@, d as int) == (sum_time as int));
            assert(spec_feasible(sum_time as int, min_t@, max_t@, d as int));
        }
        (true, sched)
    }
}

}
