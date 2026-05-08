use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_eq_prefix(a: Seq<i32>, i: int, v: i32) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        count_eq_prefix(a, i - 1, v) + (if a[i - 1] == v { 1int } else { 0int })
    }
}

pub open spec fn nonleg_count_prefix(a: Seq<i32>, leg: int, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        nonleg_count_prefix(a, leg, end - 1)
            + (if a[end - 1] as int != leg { 1int } else { 0int })
    }
}

pub open spec fn leg_scan_upto_v(a: Seq<i32>, upto: int) -> int
    recommends 0 <= upto <= 9,
{
    let r1 = if count_eq_prefix(a, 6, 1) >= 4 { 1int } else { 0int };
    let r2 = if count_eq_prefix(a, 6, 2) >= 4 { 2 } else { r1 };
    let r3 = if count_eq_prefix(a, 6, 3) >= 4 { 3 } else { r2 };
    let r4 = if count_eq_prefix(a, 6, 4) >= 4 { 4 } else { r3 };
    let r5 = if count_eq_prefix(a, 6, 5) >= 4 { 5 } else { r4 };
    let r6 = if count_eq_prefix(a, 6, 6) >= 4 { 6 } else { r5 };
    let r7 = if count_eq_prefix(a, 6, 7) >= 4 { 7 } else { r6 };
    let r8 = if count_eq_prefix(a, 6, 8) >= 4 { 8 } else { r7 };
    let r9 = if count_eq_prefix(a, 6, 9) >= 4 { 9 } else { r8 };
    if upto == 0 {
        0
    } else if upto == 1 {
        r1
    } else if upto == 2 {
        r2
    } else if upto == 3 {
        r3
    } else if upto == 4 {
        r4
    } else if upto == 5 {
        r5
    } else if upto == 6 {
        r6
    } else if upto == 7 {
        r7
    } else if upto == 8 {
        r8
    } else {
        r9
    }
}

pub open spec fn leg_length_if_any(a: Seq<i32>) -> int {
    leg_scan_upto_v(a, 9)
}

pub open spec fn remaining_two_equal(a: Seq<i32>, leg: int) -> bool {
    exists|i: int, j: int|
        0 <= i < j < 6
        && #[trigger] a[i] as int != leg
        && #[trigger] a[j] as int != leg
        && (forall|k: int|
            0 <= k < 6 && k != i && k != j ==> #[trigger] a[k] as int == leg)
        && a[i] == a[j]
}

pub open spec fn classify_with_leg(a: Seq<i32>, leg: int) -> int
    recommends
        1 <= leg <= 9,
{
    let c = count_eq_prefix(a, 6, leg as i32);
    if c == 6 {
        2
    } else if c == 5 {
        1
    } else {
        if remaining_two_equal(a, leg) {
            2
        } else {
            1
        }
    }
}

pub open spec fn expected_animal(a: Seq<i32>) -> int {
    let leg = leg_length_if_any(a);
    if leg == 0 {
        0
    } else {
        classify_with_leg(a, leg)
    }
}

proof fn lemma_count_prefix_succ(sticks: Seq<i32>, i: int, v: i32)
    requires
        0 <= i < sticks.len(),
    ensures
        count_eq_prefix(sticks, i + 1, v) == count_eq_prefix(sticks, i, v)
            + (if sticks[i] == v { 1int } else { 0int }),
{
    assert(i + 1 > 0);
}

proof fn lemma_count_eq_prefix_le_len(sticks: Seq<i32>, n: int, v: i32)
    requires
        0 <= n <= sticks.len(),
    ensures
        count_eq_prefix(sticks, n, v) <= n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_count_eq_prefix_le_len(sticks, n - 1, v);
        lemma_count_prefix_succ(sticks, n - 1, v);
        assert(count_eq_prefix(sticks, n, v) <= n);
    }
}

proof fn lemma_nonleg_prefix_succ(sticks: Seq<i32>, leg: int, end: int)
    requires
        0 <= end < sticks.len(),
    ensures
        nonleg_count_prefix(sticks, leg, end + 1) == nonleg_count_prefix(sticks, leg, end)
            + (if sticks[end] as int != leg { 1int } else { 0int }),
{
}

proof fn lemma_nonleg_prefix_le_end(sticks: Seq<i32>, leg: int, e: int)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        0 <= e <= 6,
    ensures
        nonleg_count_prefix(sticks, leg, e) <= nonleg_count_prefix(sticks, leg, 6),
    decreases 6 - e,
{
    if e >= 6 {
        assert(e == 6);
    } else {
        lemma_nonleg_prefix_le_end(sticks, leg, e + 1);
        lemma_nonleg_prefix_succ(sticks, leg, e);
        assert(nonleg_count_prefix(sticks, leg, e) <= nonleg_count_prefix(sticks, leg, e + 1));
    }
}

proof fn lemma_leg_eq_iff_not_nonleg(sticks: Seq<i32>, leg: int, idx: int)
    requires
        0 <= idx < sticks.len(),
        1 <= leg <= 9,
    ensures
        (sticks[idx] == leg as i32) == (sticks[idx] as int == leg),
{
    assert(leg as i32 as int == leg);
}

proof fn lemma_split_at_n(sticks: Seq<i32>, leg: int, n: int)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        0 <= n <= 6,
    ensures
        count_eq_prefix(sticks, n, leg as i32) + nonleg_count_prefix(sticks, leg, n) == n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_split_at_n(sticks, leg, n - 1);
        lemma_count_prefix_succ(sticks, n - 1, leg as i32);
        lemma_nonleg_prefix_succ(sticks, leg, n - 1);
        lemma_leg_eq_iff_not_nonleg(sticks, leg, n - 1);
        assert(count_eq_prefix(sticks, n, leg as i32) == count_eq_prefix(sticks, n - 1, leg as i32) + (if sticks[n - 1] == leg as i32 { 1int } else { 0int }));
        assert(nonleg_count_prefix(sticks, leg, n) == nonleg_count_prefix(sticks, leg, n - 1) + (if sticks[n - 1] as int != leg { 1int } else { 0int }));
        assert((if sticks[n - 1] == leg as i32 { 1int } else { 0int }) + (if sticks[n - 1] as int != leg { 1int } else { 0int }) == 1);
    }
}

proof fn lemma_nonleg_two_when_c4(sticks: Seq<i32>, leg: int)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        count_eq_prefix(sticks, 6, leg as i32) == 4,
    ensures
        nonleg_count_prefix(sticks, leg, 6) == 2,
{
    lemma_split_at_n(sticks, leg, 6);
}

proof fn lemma_nonleg_eq_sum6(sticks: Seq<i32>, leg: int)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
    ensures
        nonleg_count_prefix(sticks, leg, 6)
            == (if sticks[0] as int != leg { 1int } else { 0int })
                + (if sticks[1] as int != leg { 1int } else { 0int })
                + (if sticks[2] as int != leg { 1int } else { 0int })
                + (if sticks[3] as int != leg { 1int } else { 0int })
                + (if sticks[4] as int != leg { 1int } else { 0int })
                + (if sticks[5] as int != leg { 1int } else { 0int }),
{
    assert(nonleg_count_prefix(sticks, leg, 0) == 0);
    lemma_nonleg_prefix_succ(sticks, leg, 0);
    lemma_nonleg_prefix_succ(sticks, leg, 1);
    lemma_nonleg_prefix_succ(sticks, leg, 2);
    lemma_nonleg_prefix_succ(sticks, leg, 3);
    lemma_nonleg_prefix_succ(sticks, leg, 4);
    lemma_nonleg_prefix_succ(sticks, leg, 5);
}

proof fn lemma_nonleg_ge3_if_three(sticks: Seq<i32>, leg: int, i0: int, i1: int, k: int)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        0 <= i0 < i1 < 6,
        0 <= k < 6,
        k != i0,
        k != i1,
        sticks[i0] as int != leg,
        sticks[i1] as int != leg,
        sticks[k] as int != leg,
    ensures
        nonleg_count_prefix(sticks, leg, 6) >= 3,
{
    lemma_nonleg_eq_sum6(sticks, leg);
    let s = (if sticks[0] as int != leg { 1int } else { 0int })
        + (if sticks[1] as int != leg { 1int } else { 0int })
        + (if sticks[2] as int != leg { 1int } else { 0int })
        + (if sticks[3] as int != leg { 1int } else { 0int })
        + (if sticks[4] as int != leg { 1int } else { 0int })
        + (if sticks[5] as int != leg { 1int } else { 0int });
    assert(s == nonleg_count_prefix(sticks, leg, 6));
    assert((if sticks[i0] as int != leg { 1int } else { 0int }) == 1);
    assert((if sticks[i1] as int != leg { 1int } else { 0int }) == 1);
    assert((if sticks[k] as int != leg { 1int } else { 0int }) == 1);
    assert(s >= 3);
}

proof fn lemma_rest_are_leg(
    sticks: Seq<i32>,
    leg: int,
    i0: int,
    i1: int,
)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        count_eq_prefix(sticks, 6, leg as i32) == 4,
        0 <= i0 < i1 < 6,
        sticks[i0] as int != leg,
        sticks[i1] as int != leg,
    ensures
        forall|k: int|
            0 <= k < 6 && k != i0 && k != i1 ==> sticks[k] as int == leg,
{
    assert forall|k: int|
        0 <= k < 6 && k != i0 && k != i1 implies sticks[k] as int == leg
    by {
        if 0 <= k < 6 && k != i0 && k != i1 {
            if sticks[k] as int != leg {
                lemma_nonleg_ge3_if_three(sticks, leg, i0, i1, k);
                lemma_nonleg_two_when_c4(sticks, leg);
                assert(nonleg_count_prefix(sticks, leg, 6) == 2);
                assert(false);
            }
        }
    };
}

proof fn lemma_unique_nonleg_pair(
    sticks: Seq<i32>,
    leg: int,
    i0: int,
    i1: int,
)
    requires
        sticks.len() == 6,
        0 <= i0 < i1 < 6,
        sticks[i0] as int != leg,
        sticks[i1] as int != leg,
        forall|k: int|
            0 <= k < 6 && k != i0 && k != i1 ==> sticks[k] as int == leg,
    ensures
        forall|p: int, q: int|
            (0 <= p < q < 6 && sticks[p] as int != leg && sticks[q] as int != leg
                && (forall|k: int|
                    0 <= k < 6 && k != p && k != q ==> sticks[k] as int == leg))
                ==> p == i0 && q == i1,
{
    assert forall|p: int, q: int|
        (0 <= p < q < 6 && sticks[p] as int != leg && sticks[q] as int != leg
            && (forall|k: int|
                0 <= k < 6 && k != p && k != q ==> sticks[k] as int == leg))
            implies p == i0 && q == i1
    by {
        if 0 <= p < q < 6 && sticks[p] as int != leg && sticks[q] as int != leg
            && (forall|k: int|
                0 <= k < 6 && k != p && k != q ==> sticks[k] as int == leg)
        {
            assert(p == i0 || p == i1);
            assert(q == i0 || q == i1);
            assert(p < q);
            assert(i0 < i1);
            if p == i1 {
                assert(q > i1);
                assert(sticks[q] as int != leg);
                lemma_rest_are_leg(sticks, leg, i0, i1);
                assert(sticks[q] as int == leg);
                assert(false);
            }
            assert(p == i0);
            if q == i0 {
                assert(false);
            }
            assert(q == i1);
        }
    };
}

proof fn lemma_remaining_iff_xy(
    sticks: Seq<i32>,
    leg: int,
    i0: int,
    i1: int,
    x: i32,
    y: i32,
)
    requires
        sticks.len() == 6,
        1 <= leg <= 9,
        0 <= i0 < i1 < 6,
        x == sticks[i0],
        y == sticks[i1],
        sticks[i0] as int != leg,
        sticks[i1] as int != leg,
        forall|k: int|
            0 <= k < 6 && k != i0 && k != i1 ==> sticks[k] as int == leg,
    ensures
        remaining_two_equal(sticks, leg) == (x == y),
{
    lemma_unique_nonleg_pair(sticks, leg, i0, i1);
    if x == y {
        assert(remaining_two_equal(sticks, leg)) by {
            assert(exists|i: int, j: int|
                0 <= i < j < 6
                && sticks[i] as int != leg
                && sticks[j] as int != leg
                && (forall|k: int|
                    0 <= k < 6 && k != i && k != j ==> sticks[k] as int == leg)
                && sticks[i] == sticks[j]) by {
                let i = i0;
                let j = i1;
            };
        };
    } else {
        assert(!remaining_two_equal(sticks, leg)) by {
            assert forall|p: int, q: int|
                !(0 <= p < q < 6 && sticks[p] as int != leg && sticks[q] as int != leg
                    && (forall|k: int|
                        0 <= k < 6 && k != p && k != q ==> sticks[k] as int == leg)
                    && sticks[p] == sticks[q])
            by {
                if 0 <= p < q < 6 && sticks[p] as int != leg && sticks[q] as int != leg
                    && (forall|k: int|
                        0 <= k < 6 && k != p && k != q ==> sticks[k] as int == leg)
                    && sticks[p] == sticks[q]
                {
                    lemma_unique_nonleg_pair(sticks, leg, i0, i1);
                    assert(p == i0 && q == i1);
                    assert(sticks[p] == sticks[q]);
                    assert(x == y);
                    assert(false);
                }
            };
        };
    }
}

proof fn lemma_cnt_inv_after_step(
    sticks: Seq<i32>,
    i: int,
    idx: int,
    prev: Seq<i32>,
    post: Seq<i32>,
)
    requires
        sticks.len() == 6,
        0 <= i < 6,
        1 <= idx <= 9,
        prev.len() == 10,
        post.len() == 10,
        sticks[i] == idx as i32,
        forall|vv: int| 1 <= vv <= 9 ==> prev[vv] == count_eq_prefix(sticks, i, vv as i32),
        forall|vv: int| 1 <= vv <= 9 ==> post[vv] == prev[vv] + (if vv == idx { 1int } else { 0int }),
    ensures
        forall|vv: int| 1 <= vv <= 9 ==> post[vv] == count_eq_prefix(sticks, i + 1, vv as i32),
{
    assert forall|vv: int| 1 <= vv <= 9 implies post[vv] == count_eq_prefix(sticks, i + 1, vv as i32) by {
        lemma_count_prefix_succ(sticks, i, vv as i32);
        if vv == idx {
            assert(sticks[i] == vv as i32);
            assert(post[vv] == prev[vv] + 1);
            assert(count_eq_prefix(sticks, i + 1, vv as i32) == count_eq_prefix(sticks, i, vv as i32) + 1);
        } else {
            assert(!(vv == idx));
            assert(post[vv] == prev[vv]);
            assert(count_eq_prefix(sticks, i + 1, vv as i32) == count_eq_prefix(sticks, i, vv as i32));
        }
    };
}

pub struct Solution;

impl Solution {
    pub fn animal_type(sticks: Vec<i32>) -> (res: i32)
        requires
            sticks.len() == 6,
            forall|i: int| 0 <= i < 6 ==> 1 <= #[trigger] sticks@[i] as int <= 9,
        ensures
            res == expected_animal(sticks@),
    {
        let mut cnt = Vec::new();
        let mut zi = 0usize;
        while zi < 10
            invariant
                zi <= 10,
                cnt.len() == zi,
                forall|k: int| 0 <= k < zi ==> #[trigger] cnt@[k] == 0,
            decreases 10 - zi,
        {
            cnt.push(0i32);
            zi += 1;
        }
        proof {
            assert(cnt.len() == 10);
        }
        let mut i = 0usize;
        while i < 6
            invariant
                sticks.len() == 6,
                cnt.len() == 10,
                forall|ii: int| 0 <= ii < 6 ==> 1 <= #[trigger] sticks@[ii] as int <= 9,
                0 <= i <= 6,
                forall|vv: int|
                    1 <= vv <= 9 ==> #[trigger] cnt@[vv] == count_eq_prefix(sticks@, i as int, vv as i32),
            decreases 6 - i,
        {
            let idx = sticks[i] as usize;
            proof {
                assert(1 <= idx <= 9);
            }
            let ghost prev = cnt@;
            proof {
                assert(cnt@[idx as int] == count_eq_prefix(sticks@, i as int, idx as i32));
                lemma_count_eq_prefix_le_len(sticks@, i as int, idx as i32);
                assert(count_eq_prefix(sticks@, i as int, idx as i32) <= i as int);
            }
            cnt.set(idx, cnt[idx] + 1);
            proof {
                assert forall|vv: int| 1 <= vv <= 9 implies
                    cnt@[vv] == prev[vv] + (if vv == idx as int { 1int } else { 0int }) by {
                    if vv == idx as int {
                        assert(cnt@[vv] == prev[vv] + 1);
                    } else {
                        assert(cnt@[vv] == prev[vv]);
                    }
                };
                lemma_cnt_inv_after_step(sticks@, i as int, idx as int, prev, cnt@);
            }
            i += 1;
        }
        proof {
            assert(i == 6);
        }
        let mut leg = 0i32;
        let mut v = 1i32;
        while v <= 9
            invariant
                sticks.len() == 6,
                cnt.len() == 10,
                forall|vv: int| 1 <= vv <= 9 ==> #[trigger] cnt@[vv] == count_eq_prefix(sticks@, 6, vv as i32),
                1 <= v <= 10,
                leg as int == leg_scan_upto_v(sticks@, (v - 1) as int),
            decreases 10 - v,
        {
            let old_leg = leg;
            proof {
                assert(leg as int == leg_scan_upto_v(sticks@, (v - 1) as int));
                assert(count_eq_prefix(sticks@, 6, v as i32) == cnt@[v as int]);
            }
            if cnt[v as usize] >= 4 {
                leg = v;
            }
            proof {
                assert(leg_scan_upto_v(sticks@, v as int) == if cnt@[v as int] >= 4 {
                    v as int
                } else {
                    leg_scan_upto_v(sticks@, (v - 1) as int)
                });
                if cnt@[v as int] >= 4 {
                    assert(leg == v);
                    assert(leg as int == leg_scan_upto_v(sticks@, v as int));
                } else {
                    assert(leg == old_leg);
                    assert(leg as int == leg_scan_upto_v(sticks@, v as int));
                }
            }
            v += 1;
        }
        proof {
            assert(v == 10);
            assert(leg as int == leg_scan_upto_v(sticks@, 9));
            assert(leg as int == leg_length_if_any(sticks@));
        }
        if leg == 0 {
            proof {
                assert(leg_length_if_any(sticks@) == 0);
                assert(expected_animal(sticks@) == 0);
            }
            return 0;
        }
        let c = cnt[leg as usize];
        proof {
            assert(1 <= leg <= 9);
            assert(c == cnt@[leg as int]);
            assert(c == count_eq_prefix(sticks@, 6, leg as i32));
            assert(leg as int == leg_length_if_any(sticks@));
        }
        if c == 6 {
            proof {
                assert(classify_with_leg(sticks@, leg as int) == 2);
                assert(expected_animal(sticks@) == 2);
            }
            return 2;
        }
        if c == 5 {
            proof {
                assert(classify_with_leg(sticks@, leg as int) == 1);
                assert(expected_animal(sticks@) == 1);
            }
            return 1;
        }
        proof {
            assert(c == cnt@[leg as int]);
            assert(cnt@[leg as int] == count_eq_prefix(sticks@, 6, leg as i32));
            lemma_count_eq_prefix_le_len(sticks@, 6, leg as i32);
            assert(count_eq_prefix(sticks@, 6, leg as i32) <= 6);
            assert(count_eq_prefix(sticks@, 6, leg as i32) >= 4);
            assert(c != 6);
            assert(c != 5);
            assert(c == 4);
            assert(count_eq_prefix(sticks@, 6, leg as i32) == 4);
            lemma_nonleg_two_when_c4(sticks@, leg as int);
        }
        let mut ii = 0usize;
        let mut x = 0i32;
        let mut y = 0i32;
        let mut nrem = 0usize;
        let mut i0 = 6usize;
        let mut i1 = 6usize;
        while ii < 6
            invariant
                sticks.len() == 6,
                cnt.len() == 10,
                forall|idx: int| 0 <= idx < 6 ==> 1 <= #[trigger] sticks@[idx] as int <= 9,
                1 <= leg <= 9,
                cnt@[leg as int] == count_eq_prefix(sticks@, 6, leg as i32),
                c == 4,
                count_eq_prefix(sticks@, 6, leg as i32) == 4,
                0 <= ii <= 6,
                nrem as int == nonleg_count_prefix(sticks@, leg as int, ii as int),
                nrem <= 2,
                (nrem >= 1) ==> (i0 < 6 && x == sticks@[i0 as int]),
                (nrem >= 2) ==> (i1 < 6 && i0 < i1 && y == sticks@[i1 as int]),
                (nrem >= 1) ==> (sticks@[i0 as int] as int != leg as int),
                (nrem >= 2) ==> (sticks@[i1 as int] as int != leg as int),
                (nrem == 0) ==> (forall|k: int|
                    0 <= k < ii as int ==> #[trigger] sticks@[k] as int == leg as int),
                (nrem == 1) ==> (i0 < ii),
                (nrem == 1) ==> (forall|k: int|
                    0 <= k < ii as int && k != i0 as int ==> #[trigger] sticks@[k] as int == leg as int),
                (nrem == 2) ==> (forall|k: int|
                    0 <= k < ii as int && k != i0 as int && k != i1 as int ==> #[trigger] sticks@[k] as int == leg as int),
                (nrem == 2) ==> (i1 < ii),
                (nrem == 2 && ii < 6) ==> (sticks@[ii as int] as int == leg as int),
            decreases 6 - ii,
        {
            if sticks[ii] != leg {
                proof {
                    lemma_nonleg_prefix_succ(sticks@, leg as int, ii as int);
                    lemma_leg_eq_iff_not_nonleg(sticks@, leg as int, ii as int);
                }
                if nrem == 0 {
                    i0 = ii;
                    x = sticks[ii];
                    proof {
                        assert(i0 < 6);
                        assert(x == sticks@[i0 as int]);
                        assert(sticks@[i0 as int] as int != leg as int);
                    }
                } else {
                    proof {
                        assert(nrem == 1);
                        assert(i0 < ii);
                    }
                    i1 = ii;
                    y = sticks[ii];
                    proof {
                        assert(i0 < i1);
                        assert(y == sticks@[i1 as int]);
                        assert(sticks@[i1 as int] as int != leg as int);
                        lemma_rest_are_leg(sticks@, leg as int, i0 as int, i1 as int);
                        if (i1 + 1) < 6 {
                            assert(sticks@[(i1 + 1) as int] as int == leg as int);
                        }
                    }
                }
                nrem += 1;
            } else {
                proof {
                    lemma_nonleg_prefix_succ(sticks@, leg as int, ii as int);
                    lemma_leg_eq_iff_not_nonleg(sticks@, leg as int, ii as int);
                    if nrem == 2 {
                        assert(i1 < ii);
                        lemma_rest_are_leg(sticks@, leg as int, i0 as int, i1 as int);
                        if (ii + 1) < 6 {
                            assert(ii as int + 1 != i0 as int);
                            assert(ii as int + 1 != i1 as int);
                            assert(sticks@[(ii + 1) as int] as int == leg as int);
                        }
                    }
                }
            }
            ii += 1;
        }
        proof {
            assert(ii == 6);
            assert(nrem as int == nonleg_count_prefix(sticks@, leg as int, 6));
            lemma_nonleg_two_when_c4(sticks@, leg as int);
            assert(nrem == 2);
            assert(i0 < 6 && i1 < 6);
            assert(i0 < i1);
            lemma_rest_are_leg(sticks@, leg as int, i0 as int, i1 as int);
        }
        proof {
            lemma_remaining_iff_xy(sticks@, leg as int, i0 as int, i1 as int, x, y);
            assert(classify_with_leg(sticks@, leg as int) == if x == y { 2int } else { 1int });
            assert(expected_animal(sticks@) == if x == y { 2int } else { 1int });
        }
        if x == y {
            2
        } else {
            1
        }
    }
}

}
