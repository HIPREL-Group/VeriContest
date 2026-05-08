use vstd::prelude::*;
use vstd::seq_lib::lemma_seq_contains_after_push;

fn main() {}

verus! {

pub open spec fn spec_sum(a: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_sum(a, n - 1) + a[n - 1] as int
    }
}

pub open spec fn spec_count_eq(a: Seq<i32>, n: int, v: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        spec_count_eq(a, n - 1, v) + (if a[n - 1] as int == v {
            1int
        } else {
            0int
        })
    }
}

pub open spec fn is_nice(a: Seq<i32>, n: int, j: int) -> bool {
    0 <= j && j < n && (
        {
            let s = spec_sum(a, n);
            let t = s - a[j] as int;
            t % 2 == 0 && {
                let need = t / 2;
                let cnt = spec_count_eq(a, n, need);
                (a[j] as int == need && cnt >= 2) || (a[j] as int != need && cnt >= 1)
            }
        }
    )
}

pub open spec fn output_has_index(res: Seq<i32>, jb: int) -> bool {
    res.contains(jb as i32)
}

pub open spec fn res_indices_pairwise_distinct(res: Seq<i32>) -> bool {
    forall|i: int, k: int|
        0 <= i && i < k && k < res.len() as int
        ==> #[trigger] res[i] != #[trigger] res[k]
}

pub open spec fn is_nice_1idx(a: Seq<i32>, n: int, jb: int) -> bool {
    is_nice(a, n, jb - 1)
}

proof fn lemma_spec_sum_step(a: Seq<i32>, i: int)
    requires
        0 <= i && i < a.len(),
    ensures
        spec_sum(a, i + 1) == spec_sum(a, i) + a[i] as int,
{
}

proof fn lemma_spec_count_step(a: Seq<i32>, i: int, v: int)
    requires
        0 <= i && i < a.len(),
    ensures
        spec_count_eq(a, i + 1, v) == spec_count_eq(a, i, v) + (if a[i] as int == v {
            1int
        } else {
            0int
        }),
{
}

proof fn lemma_spec_count_le_i(a: Seq<i32>, i: int, v: int)
    requires
        0 <= i <= a.len(),
    ensures
        spec_count_eq(a, i, v) <= i,
    decreases i,
{
    if i == 0 {
    } else {
        lemma_spec_count_le_i(a, i - 1, v);
        lemma_spec_count_step(a, i - 1, v);
        assert(spec_count_eq(a, i, v) <= (i - 1) + 1);
    }
}

proof fn lemma_spec_sum_range_lower(a: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= a.len(),
        forall|k: int| lo <= k && k < hi ==> a[k] as int >= 1,
    ensures
        spec_sum(a, hi) - spec_sum(a, lo) >= hi - lo,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        lemma_spec_sum_range_lower(a, lo, hi - 1);
    }
}

proof fn lemma_spec_sum_range_upper(a: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= a.len(),
        forall|k: int| lo <= k && k < hi ==> a[k] as int <= 1_000_000,
    ensures
        spec_sum(a, hi) - spec_sum(a, lo) <= (hi - lo) * 1_000_000,
    decreases hi - lo,
{
    if lo >= hi {
    } else {
        lemma_spec_sum_range_upper(a, lo, hi - 1);
    }
}

proof fn lemma_count_eq_zero_large_v(a: Seq<i32>, n: int, v: int)
    requires
        0 <= n <= a.len(),
        forall|k: int| 0 <= k && k < n ==> a[k] as int <= 1_000_000,
        v > 1_000_000,
    ensures
        spec_count_eq(a, n, v) == 0,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_count_eq_zero_large_v(a, n - 1, v);
        assert(a[n - 1] as int != v);
    }
}

proof fn lemma_count_eq_zero_small_v(a: Seq<i32>, n: int, v: int)
    requires
        0 <= n <= a.len(),
        forall|k: int| 0 <= k && k < n ==> a[k] as int >= 1,
        v < 1,
    ensures
        spec_count_eq(a, n, v) == 0,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_count_eq_zero_small_v(a, n - 1, v);
        assert(a[n - 1] as int != v);
    }
}

proof fn lemma_nice_when_need_in_range(
    a: Seq<i32>,
    n: int,
    j: int,
    s_int: int,
    aj: i64,
    t: i64,
    need: i64,
    c: i32,
)
    requires
        0 <= j && j < n,
        n == a.len(),
        s_int == spec_sum(a, n),
        t as int == s_int - aj as int,
        aj == a[j] as int,
        t % 2 == 0,
        need == t / 2,
        1 <= need && need <= 1_000_000,
        c == spec_count_eq(a, n, need as int),
    ensures
        is_nice(a, n, j) <==> ((aj == need && c >= 2) || (aj != need && c >= 1)),
{
    assert((s_int - a[j] as int) == t as int);
    assert((s_int - a[j] as int) / 2 == need as int);
    let need_i = need as int;
    assert(spec_count_eq(a, n, need_i) == c);
    assert(a[j] as int == need_i <==> aj == need);
}

proof fn lemma_remainder_sum_bounds(a: Seq<i32>, n: int, j: int)
    requires
        0 <= j && j < n,
        n == a.len(),
        2 <= n,
        forall|k: int| 0 <= k && k < n ==> a[k] as int >= 1 && a[k] as int <= 1_000_000,
    ensures
        spec_sum(a, n) - a[j] as int >= (n - 1) as int,
        spec_sum(a, n) - a[j] as int <= ((n - 1) as int) * 1_000_000,
{
    lemma_spec_sum_step(a, j);
    lemma_spec_sum_range_lower(a, 0, j);
    lemma_spec_sum_range_lower(a, j + 1, n);
    lemma_spec_sum_range_upper(a, 0, j);
    lemma_spec_sum_range_upper(a, j + 1, n);
}

proof fn lemma_i64_sum_add_safe(s: i64, ai: i32, i: int, n: int, a: Seq<i32>)
    requires
        0 <= i,
        i < n,
        n <= 200_000,
        n == a.len(),
        s as int == spec_sum(a, i),
        s as int <= i * 1_000_000,
        a.index(i as int) == ai,
        1 <= ai as int && ai as int <= 1_000_000,
    ensures
        (s + ai as i64) as int == spec_sum(a, i + 1),
        (s + ai as i64) as int <= (i + 1) * 1_000_000,
{
    lemma_spec_sum_step(a, i);
    assert((s + ai as i64) as int == spec_sum(a, i + 1));
    assert((s + ai as i64) as int <= (i + 1) * 1_000_000);
}

proof fn lemma_inv_after_push(
    a: Seq<i32>,
    n: int,
    j: int,
    old_res: Seq<i32>,
    new_res: Seq<i32>,
)
    requires
        0 <= j && j < n,
        n <= 200_000,
        new_res == old_res.push((j + 1) as i32),
        is_nice_1idx(a, n, j + 1),
        forall|jb: int| 1 <= jb && jb <= j && #[trigger] is_nice_1idx(a, n, jb) ==> output_has_index(old_res, jb),
        forall|jb: int| 1 <= jb && jb <= j && #[trigger] output_has_index(old_res, jb) ==> is_nice_1idx(a, n, jb),
        res_indices_pairwise_distinct(old_res),
        forall|t: int| 0 <= t && t < old_res.len() ==> #[trigger] old_res[t] as int <= j,
    ensures
        forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] is_nice_1idx(a, n, jb) ==> output_has_index(new_res, jb),
        forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] output_has_index(new_res, jb) ==> is_nice_1idx(a, n, jb),
        res_indices_pairwise_distinct(new_res),
{
    assert forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] is_nice_1idx(a, n, jb) implies output_has_index(new_res, jb) by {
        lemma_seq_contains_after_push(old_res, (j + 1) as i32, jb as i32);
        if jb == j + 1 {
            assert(jb as i32 == (j + 1) as i32);
            assert(new_res.contains(jb as i32));
        } else {
            assert(jb <= j);
            assert(output_has_index(old_res, jb));
            assert(new_res.contains(jb as i32) <==> old_res.contains(jb as i32));
        }
    }
    assert forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] output_has_index(new_res, jb) implies is_nice_1idx(a, n, jb) by {
        lemma_seq_contains_after_push(old_res, (j + 1) as i32, jb as i32);
        if jb == j + 1 {
            assert(is_nice_1idx(a, n, j + 1));
        } else {
            assert(jb <= j);
            assert(new_res.contains(jb as i32) <==> old_res.contains(jb as i32));
            assert(output_has_index(old_res, jb));
            assert(is_nice_1idx(a, n, jb));
        }
    }
    assert forall|p: int, q: int|
        0 <= p && p < q && q < new_res.len() as int
        implies new_res[p] != new_res[q]
    by {
        if q < new_res.len() - 1 {
            assert(p < new_res.len() - 1);
            assert(new_res[p] == old_res[p]);
            assert(new_res[q] == old_res[q]);
            assert(res_indices_pairwise_distinct(old_res));
            assert(old_res[p] != old_res[q]);
        } else {
            assert(q == new_res.len() - 1);
            assert(new_res[q] == (j + 1) as i32);
            assert(p < old_res.len() as int);
            assert(new_res[p] == old_res[p]);
            assert(old_res[p] as int <= j);
            assert((j + 1) as int == j + 1);
            assert(old_res[p] as int != (j + 1) as int);
        }
    }
    assert(res_indices_pairwise_distinct(new_res));
}

proof fn lemma_inv_after_nopush(a: Seq<i32>, n: int, j: int, res: Seq<i32>)
    requires
        0 <= j && j < n,
        n <= 200_000,
        !is_nice_1idx(a, n, j + 1),
        forall|jb: int| 1 <= jb && jb <= j && #[trigger] is_nice_1idx(a, n, jb) ==> output_has_index(res, jb),
        forall|jb: int| 1 <= jb && jb <= j && #[trigger] output_has_index(res, jb) ==> is_nice_1idx(a, n, jb),
        forall|t: int| 0 <= t && t < res.len() ==> #[trigger] res[t] as int <= j,
        res_indices_pairwise_distinct(res),
    ensures
        forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] is_nice_1idx(a, n, jb) ==> output_has_index(res, jb),
        forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] output_has_index(res, jb) ==> is_nice_1idx(a, n, jb),
        res_indices_pairwise_distinct(res),
{
    assert forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] is_nice_1idx(a, n, jb) implies output_has_index(res, jb) by {
        if jb == j + 1 {
            assert(!is_nice_1idx(a, n, j + 1));
        } else {
            assert(1 <= jb && jb <= j);
        }
    }
    assert forall|jb: int| 1 <= jb && jb <= j + 1 && #[trigger] output_has_index(res, jb) implies is_nice_1idx(a, n, jb) by {
        if jb == j + 1 {
            assert forall|idx: int| 0 <= idx && idx < res.len() implies res[idx] != (j + 1) as i32 by {
                assert(res[idx] as int <= j);
            }
            assert(!res.contains((j + 1) as i32));
        } else {
            assert(1 <= jb && jb <= j);
        }
    }
    assert(res_indices_pairwise_distinct(res));
}

proof fn lemma_i64_sub_t_safe(s: i64, aj: i64, s_int: int, aj_int: int)
    requires
        s as int == s_int,
        aj == aj_int,
        0 <= s_int - aj_int,
        s_int <= 200_000 * 1_000_000,
        1 <= aj_int <= 1_000_000,
    ensures
        (s - aj) as int == s_int - aj_int,
{
    assert((s - aj) as int == s_int - aj_int);
}

proof fn lemma_not_nice_odd_t(a: Seq<i32>, n: int, j: int, t: i64)
    requires
        0 <= j && j < n,
        n == a.len(),
        t % 2 != 0,
        t as int == spec_sum(a, n) - a[j] as int,
    ensures
        !is_nice(a, n, j),
{
    assert((spec_sum(a, n) - a[j] as int) % 2 != 0);
}

proof fn lemma_not_nice_need_oob(
    a: Seq<i32>,
    n: int,
    j: int,
    need: i64,
    t: i64,
)
    requires
        0 <= j && j < n,
        n == a.len(),
        t % 2 == 0,
        need == t / 2,
        t as int == spec_sum(a, n) - a[j] as int,
        forall|k: int| 0 <= k && k < n ==> 1 <= a[k] && a[k] <= 1_000_000,
        need < 1 || need > 1_000_000,
    ensures
        !is_nice(a, n, j),
{
    if need < 1 {
        lemma_count_eq_zero_small_v(a, n, need as int);
        assert(spec_count_eq(a, n, need as int) == 0);
        assert(!is_nice(a, n, j));
    } else {
        lemma_count_eq_zero_large_v(a, n, need as int);
        assert(spec_count_eq(a, n, need as int) == 0);
        assert(!is_nice(a, n, j));
    }
}

pub struct Solution;

impl Solution {
    pub fn nice_indices(n: usize, a: Vec<i32>) -> (res: Vec<i32>)
        requires
            2 <= n && n <= 200_000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= #[trigger] a@[i] && a@[i] <= 1_000_000,
        ensures
            forall|jb: int| 1 <= jb && jb <= n as int ==> (
                is_nice(a@, n as int, jb - 1) <==> output_has_index(res@, jb)
            ),
            forall|t: int| 0 <= t && t < res.len() ==> 1 <= #[trigger] res[t] && res[t] <= n as int,
            res_indices_pairwise_distinct(res@),
    {
        let mut freq: Vec<i32> = Vec::new();
        let mut fi: usize = 0;
        while fi < 1_000_000 + 1
            invariant
                freq.len() == fi,
                fi <= 1_000_000 + 1,
                forall|k: int| 0 <= k && k < fi as int ==> freq@[k] == 0i32,
            decreases 1_000_000 + 1 - fi
        {
            freq.push(0i32);
            fi += 1;
        }
        proof {
            assert(freq.len() == 1_000_000 + 1);
            assert forall|v: int| 1 <= v && v <= 1_000_000 implies #[trigger] freq@[v] == spec_count_eq(a@, 0, v) by {
                assert(spec_count_eq(a@, 0, v) == 0);
                assert(freq@[v] == 0i32);
            }
        }
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                2 <= n && n <= 200_000,
                forall|k: int| 0 <= k && k < n ==> 1 <= #[trigger] a@[k] && a@[k] <= 1_000_000,
                i <= n,
                freq.len() == 1_000_000 + 1,
                s as int == spec_sum(a@, i as int),
                s as int <= (i as int) * 1_000_000,
                forall|v: int|
                    1 <= v && v <= 1_000_000 ==> #[trigger] freq@[v] == spec_count_eq(a@, i as int, v),
            decreases n - i
        {
            let v = a[i] as usize;
            proof {
                assert(i < n);
                assert((i as int) < (a.len() as int));
                lemma_spec_sum_step(a@, i as int);
            }
            let oldc = freq[v];
            let ghost old_freq = freq@;
            proof {
                assert(1 <= a@[i as int] as int && a@[i as int] as int <= 1_000_000);
                assert(1 <= v && v <= 1_000_000);
                assert(oldc == spec_count_eq(a@, i as int, v as int));
                lemma_spec_count_le_i(a@, i as int, v as int);
                assert((oldc as int) <= i as int);
                assert((oldc + 1) as int <= (i + 1) as int);
                assert(i as int <= n as int);
                assert((oldc + 1) as int <= 200_000);
            }
            freq[v] = freq[v] + 1;
            proof {
                lemma_spec_count_step(a@, i as int, v as int);
                assert((freq@[v as int]) as int == (oldc + 1) as int);
                assert((oldc + 1) as int == spec_count_eq(a@, i as int, v as int) + (if a@[i as int] as int == v as int {
                    1int
                } else {
                    0int
                }));
                assert(a@[i as int] as int == v as int);
                assert(forall|w: int|
                    1 <= w && w <= 1_000_000 && w != v as int ==> spec_count_eq(a@, (i + 1) as int, w) == spec_count_eq(
                        a@,
                        i as int,
                        w,
                    ));
                assert forall|w: int| 1 <= w && w <= 1_000_000 implies freq@[w] == spec_count_eq(
                    a@,
                    (i + 1) as int,
                    w,
                ) by {
                    if w == v as int {
                        assert(freq@[w] == oldc + 1);
                    } else {
                        assert(freq@[w] == old_freq[w]);
                        assert(spec_count_eq(a@, (i + 1) as int, w) == spec_count_eq(a@, i as int, w));
                    }
                }
            }
            let ai = a[i];
            proof {
                lemma_i64_sum_add_safe(s, ai, i as int, n as int, a@);
            }
            s = s + a[i] as i64;
            i += 1;
        }
        proof {
            assert(s as int == spec_sum(a@, n as int));
        }
        let ghost s_int = s as int;
        let mut res: Vec<i32> = Vec::new();
        proof {
            assert(res_indices_pairwise_distinct(res@));
        }
        let mut j: usize = 0;
        while j < n
            invariant
                n == a.len(),
                2 <= n && n <= 200_000,
                forall|k: int| 0 <= k && k < n ==> 1 <= #[trigger] a@[k] && a@[k] <= 1_000_000,
                j <= n,
                s_int == spec_sum(a@, n as int),
                (s as int) == s_int,
                freq.len() == 1_000_000 + 1,
                forall|v: int|
                    1 <= v && v <= 1_000_000 ==> #[trigger] freq@[v] == spec_count_eq(a@, n as int, v),
                forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] is_nice_1idx(a@, n as int, jb) ==> output_has_index(res@, jb),
                forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] output_has_index(res@, jb) ==> is_nice_1idx(a@, n as int, jb),
                forall|t: int| 0 <= t && t < res.len() ==> 1 <= #[trigger] res[t] && res[t] <= j as int,
                res_indices_pairwise_distinct(res@),
            decreases n - j
        {
            let aj = a[j] as i64;
            proof {
                lemma_remainder_sum_bounds(a@, n as int, j as int);
                lemma_i64_sub_t_safe(s, aj, s_int, a@[j as int] as int);
            }
            let t = s - aj;
            if t % 2 == 0 {
                let need = t / 2;
                if need >= 1 && need <= 1_000_000 as i64 {
                    let need_u = need as usize;
                    let c = freq[need_u];
                    proof {
                        assert(c == spec_count_eq(a@, n as int, need as int));
                        lemma_nice_when_need_in_range(
                            a@,
                            n as int,
                            j as int,
                            s_int,
                            aj,
                            t,
                            need,
                            c,
                        );
                    }
                    if aj == need {
                        if c >= 2 {
                            let ghost old_res = res@;
                            proof {
                                assert forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] is_nice_1idx(a@, n as int, jb) implies output_has_index(old_res, jb) by { }
                                assert forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] output_has_index(old_res, jb) implies is_nice_1idx(a@, n as int, jb) by { }
                                assert(res_indices_pairwise_distinct(old_res));
                                assert forall|tt: int| 0 <= tt && tt < old_res.len() implies old_res[tt] as int <= j as int by {
                                    assert(tt < res.len());
                                }
                            }
                            res.push((j + 1) as i32);
                            proof {
                                assert(res@ == old_res.push((j + 1) as i32));
                                lemma_nice_when_need_in_range(
                                    a@,
                                    n as int,
                                    j as int,
                                    s_int,
                                    aj,
                                    t,
                                    need,
                                    c,
                                );
                                assert(is_nice_1idx(a@, n as int, (j + 1) as int));
                                lemma_inv_after_push(a@, n as int, j as int, old_res, res@);
                            }
                        } else {
                            proof {
                                lemma_nice_when_need_in_range(
                                    a@,
                                    n as int,
                                    j as int,
                                    s_int,
                                    aj,
                                    t,
                                    need,
                                    c,
                                );
                                assert(!is_nice_1idx(a@, n as int, (j + 1) as int));
                                assert(res_indices_pairwise_distinct(res@));
                                lemma_inv_after_nopush(a@, n as int, j as int, res@);
                            }
                        }
                    } else {
                        if c >= 1 {
                            let ghost old_res = res@;
                            proof {
                                assert forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] is_nice_1idx(a@, n as int, jb) implies output_has_index(old_res, jb) by { }
                                assert forall|jb: int| 1 <= jb && jb <= j as int && #[trigger] output_has_index(old_res, jb) implies is_nice_1idx(a@, n as int, jb) by { }
                                assert(res_indices_pairwise_distinct(old_res));
                                assert forall|tt: int| 0 <= tt && tt < old_res.len() implies old_res[tt] as int <= j as int by {
                                    assert(tt < res.len());
                                }
                            }
                            res.push((j + 1) as i32);
                            proof {
                                assert(res@ == old_res.push((j + 1) as i32));
                                lemma_nice_when_need_in_range(
                                    a@,
                                    n as int,
                                    j as int,
                                    s_int,
                                    aj,
                                    t,
                                    need,
                                    c,
                                );
                                assert(is_nice_1idx(a@, n as int, (j + 1) as int));
                                lemma_inv_after_push(a@, n as int, j as int, old_res, res@);
                            }
                        } else {
                            proof {
                                lemma_nice_when_need_in_range(
                                    a@,
                                    n as int,
                                    j as int,
                                    s_int,
                                    aj,
                                    t,
                                    need,
                                    c,
                                );
                                assert(!is_nice_1idx(a@, n as int, (j + 1) as int));
                                assert(res_indices_pairwise_distinct(res@));
                                lemma_inv_after_nopush(a@, n as int, j as int, res@);
                            }
                        }
                    }
                } else {
                    proof {
                        lemma_not_nice_need_oob(a@, n as int, j as int, need, t);
                        assert(!is_nice_1idx(a@, n as int, (j + 1) as int));
                        assert(res_indices_pairwise_distinct(res@));
                        lemma_inv_after_nopush(a@, n as int, j as int, res@);
                    }
                }
            } else {
                proof {
                    lemma_not_nice_odd_t(a@, n as int, j as int, t);
                    assert(!is_nice_1idx(a@, n as int, (j + 1) as int));
                    assert(res_indices_pairwise_distinct(res@));
                    lemma_inv_after_nopush(a@, n as int, j as int, res@);
                }
            }
            j += 1;
        }
        proof {
            assert forall|jb: int| 1 <= jb && jb <= n as int implies
                is_nice(a@, n as int, jb - 1) <==> output_has_index(res@, jb)
            by {
                assert(is_nice_1idx(a@, n as int, jb) == is_nice(a@, n as int, jb - 1));
            }
            assert(res_indices_pairwise_distinct(res@));
        }
        res
    }
}

}
