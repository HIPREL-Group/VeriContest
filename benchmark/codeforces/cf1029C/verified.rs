use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_l_prefix(l: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        l[0] as int
    } else {
        let m = max_l_prefix(l, len - 1);
        let v = l[len - 1] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_suffix(l: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        l[j] as int
    } else {
        let m = max_l_suffix(l, j + 1, n);
        let v = l[j] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_prefix(r: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        r[0] as int
    } else {
        let m = min_r_prefix(r, len - 1);
        let v = r[len - 1] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_suffix(r: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        r[j] as int
    } else {
        let m = min_r_suffix(r, j + 1, n);
        let v = r[j] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_excluding(l: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        max_l_suffix(l, 1, n)
    } else if k == n - 1 {
        max_l_prefix(l, n - 1)
    } else {
        let a = max_l_prefix(l, k);
        let b = max_l_suffix(l, k + 1, n);
        if a > b {
            a
        } else {
            b
        }
    }
}

pub open spec fn min_r_excluding(r: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        min_r_suffix(r, 1, n)
    } else if k == n - 1 {
        min_r_prefix(r, n - 1)
    } else {
        let a = min_r_prefix(r, k);
        let b = min_r_suffix(r, k + 1, n);
        if a < b {
            a
        } else {
            b
        }
    }
}

pub open spec fn intersection_len_excluding(l: Seq<i64>, r: Seq<i64>, n: int, k: int) -> int {
    let ml = max_l_excluding(l, n, k);
    let mr = min_r_excluding(r, n, k);
    if ml > mr {
        0int
    } else {
        mr - ml
    }
}

proof fn lemma_max_l_prefix_step(l: Seq<i64>, len: int)
    requires
        2 <= len <= l.len(),
    ensures
        max_l_prefix(l, len)
            == if l[len - 1] as int > max_l_prefix(l, len - 1) {
                l[len - 1] as int
            } else {
                max_l_prefix(l, len - 1)
            },
{
}

proof fn lemma_min_r_prefix_step(r: Seq<i64>, len: int)
    requires
        2 <= len <= r.len(),
    ensures
        min_r_prefix(r, len)
            == if min_r_prefix(r, len - 1) > r[len - 1] as int {
                r[len - 1] as int
            } else {
                min_r_prefix(r, len - 1)
            },
{
}

proof fn lemma_max_l_suffix_step(l: Seq<i64>, j: int, n: int)
    requires
        j + 2 <= n <= l.len(),
    ensures
        max_l_suffix(l, j, n)
            == if l[j] as int > max_l_suffix(l, j + 1, n) {
                l[j] as int
            } else {
                max_l_suffix(l, j + 1, n)
            },
{
}

proof fn lemma_min_r_suffix_step(r: Seq<i64>, j: int, n: int)
    requires
        j + 2 <= n <= r.len(),
    ensures
        min_r_suffix(r, j, n)
            == if min_r_suffix(r, j + 1, n) > r[j] as int {
                r[j] as int
            } else {
                min_r_suffix(r, j + 1, n)
            },
{
}

proof fn lemma_ml_mr_match_spec(
    l: Seq<i64>,
    r: Seq<i64>,
    n: int,
    pre_l: Seq<i64>,
    suf_l: Seq<i64>,
    pre_r: Seq<i64>,
    suf_r: Seq<i64>,
    kk: int,
) requires
    2 <= n <= l.len(),
    l.len() == r.len(),
    pre_l.len() == n,
    suf_l.len() == n,
    pre_r.len() == n,
    suf_r.len() == n,
    forall|j: int|
        0 <= j < n ==> #[trigger] pre_l[j] as int == max_l_prefix(l, j + 1),
    forall|j: int|
        0 <= j < n ==> #[trigger] suf_l[j] as int == max_l_suffix(l, j, n),
    forall|j: int|
        0 <= j < n ==> #[trigger] pre_r[j] as int == min_r_prefix(r, j + 1),
    forall|j: int|
        0 <= j < n ==> #[trigger] suf_r[j] as int == min_r_suffix(r, j, n),
    0 <= kk < n,
ensures
    ({
        let ml = if kk == 0 {
            suf_l[1] as int
        } else if kk == n - 1 {
            pre_l[kk - 1] as int
        } else {
            let a = pre_l[kk - 1] as int;
            let b = suf_l[kk + 1] as int;
            if a > b {
                a
            } else {
                b
            }
        };
        let mr = if kk == 0 {
            suf_r[1] as int
        } else if kk == n - 1 {
            pre_r[kk - 1] as int
        } else {
            let a = pre_r[kk - 1] as int;
            let b = suf_r[kk + 1] as int;
            if a < b {
                a
            } else {
                b
            }
        };
        &&& ml == max_l_excluding(l, n, kk)
        &&& mr == min_r_excluding(r, n, kk)
    }),
{
    if kk == 0 {
        assert(suf_l[1] as int == max_l_suffix(l, 1, n));
        assert(suf_r[1] as int == min_r_suffix(r, 1, n));
    } else if kk == n - 1 {
        assert(pre_l[kk - 1] as int == max_l_prefix(l, n - 1));
        assert(pre_r[kk - 1] as int == min_r_prefix(r, n - 1));
    } else {
        assert(pre_l[kk - 1] as int == max_l_prefix(l, kk));
        assert(suf_l[kk + 1] as int == max_l_suffix(l, kk + 1, n));
        assert(pre_r[kk - 1] as int == min_r_prefix(r, kk));
        assert(suf_r[kk + 1] as int == min_r_suffix(r, kk + 1, n));
    }
}

proof fn lemma_max_l_excluding_nonneg(l: Seq<i64>, n: int, k: int)
    requires
        2 <= n <= l.len(),
        forall|i: int|
            0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= 1_000_000_000,
        0 <= k < n,
    ensures
        max_l_excluding(l, n, k) >= 0,
{
}

proof fn lemma_cand_eq_intersection(
    l: Seq<i64>,
    r: Seq<i64>,
    n: int,
    ml: i64,
    mr: i64,
    kk: int,
) requires
    2 <= n <= l.len(),
    l.len() == r.len(),
    0 <= kk < n,
    ml as int == max_l_excluding(l, n, kk),
    mr as int == min_r_excluding(r, n, kk),
ensures
    intersection_len_excluding(l, r, n, kk)
        == (if ml as int > mr as int {
            0int
        } else {
            mr as int - ml as int
        }),
{
    let ml_i = ml as int;
    let mr_i = mr as int;
    assert(ml_i == max_l_excluding(l, n, kk));
    assert(mr_i == min_r_excluding(r, n, kk));
    if ml_i > mr_i {
        assert(intersection_len_excluding(l, r, n, kk) == 0int);
    } else {
        assert(intersection_len_excluding(l, r, n, kk) == mr_i - ml_i);
    }
}

impl Solution {
    pub fn maximal_intersection_len(l: Vec<i64>, r: Vec<i64>) -> (result: i64)
        requires
            2 <= l.len() <= 300_000,
            l.len() == r.len(),
            forall|i: int|
                0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000,
        ensures
            result >= 0,
            forall|k: int|
                0 <= k < l.len() ==> intersection_len_excluding(l@, r@, l.len() as int, k) <= result as int,
            exists|k: int|
                0 <= k < l.len() && intersection_len_excluding(l@, r@, l.len() as int, k) == result as int,
    {
        let n = l.len();
        let ghost n_i = n as int;
        proof {
            assert(l.len() == n);
            assert(r.len() == n);
            assert(n >= 2);
            assert(n_i >= 2);
            assert(n_i == l@.len());
        }
        let mut pre_l: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                n >= 2,
                l.len() == n,
                pre_l.len() == i,
                forall|j: int|
                    0 <= j < i as int ==> #[trigger] pre_l[j as int] as int == max_l_prefix(l@, j + 1),
            decreases n - i,
        {
            proof {
                assert(i < n);
                assert(i < l.len());
            }
            if i == 0 {
                pre_l.push(l[i]);
                assert(pre_l[i as int] as int == max_l_prefix(l@, 1));
                proof {
                    assert(0 < l.len());
                    assert(max_l_prefix(l@, 1) == l@[0] as int);
                }
            } else {
                let pl = pre_l[i - 1];
                let li = l[i];
                let m = if li > pl { li } else { pl };
                pre_l.push(m);
                proof {
                    lemma_max_l_prefix_step(l@, (i + 1) as int);
                    assert(max_l_prefix(l@, i as int + 1) == m as int);
                }
                assert(pre_l[i as int] as int == max_l_prefix(l@, i + 1));
            }
            i = i + 1;
        }
        assert(forall|j: int| 0 <= j < n_i ==> pre_l[j as int] as int == max_l_prefix(l@, j + 1));
        let mut suf_l: Vec<i64> = Vec::new();
        let mut z = 0usize;
        while z < n
            invariant
                z <= n,
                l.len() == n,
                suf_l.len() == z,
            decreases n - z,
        {
            suf_l.push(0i64);
            z = z + 1;
        }
        let mut i2 = n;
        while i2 > 0
            invariant
                i2 <= n,
                n >= 2,
                n_i == l@.len(),
                l.len() == n,
                suf_l.len() == n,
                forall|j: int|
                    i2 <= j < n ==> #[trigger] suf_l[j as int] as int == max_l_suffix(l@, j, n_i),
            decreases i2,
        {
            i2 = i2 - 1;
            let idx = i2;
            proof {
                assert(idx < n);
                assert(idx < l.len());
            }
            if idx + 1 == n {
                suf_l.set(idx, l[idx]);
                proof {
                    assert(idx + 1 == n);
                    assert(idx == n - 1);
                    reveal_with_fuel(max_l_suffix, 10);
                    assert(max_l_suffix(l@, idx as int, n_i) == l@[idx as int] as int);
                }
                assert(suf_l[idx as int] as int == max_l_suffix(l@, idx as int, n_i));
            } else {
                let sl = suf_l[idx + 1];
                let li = l[idx];
                suf_l.set(idx, if li > sl { li } else { sl });
                proof {
                    assert(idx + 1 < n);
                    assert(n_i == l@.len());
                    assert(idx as int + 2 <= n_i);
                    lemma_max_l_suffix_step(l@, idx as int, n_i);
                }
                assert(suf_l[idx as int] as int == max_l_suffix(l@, idx as int, n_i));
            }
        }
        assert(forall|j: int| 0 <= j < n_i ==> suf_l[j as int] as int == max_l_suffix(l@, j, n_i));
        let mut pre_r: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n
            invariant
                j <= n,
                r.len() == n,
                pre_r.len() == j,
                forall|t: int|
                    0 <= t < j as int ==> #[trigger] pre_r[t as int] as int == min_r_prefix(r@, t + 1),
            decreases n - j,
        {
            proof {
                assert(j < n);
                assert(j < r.len());
            }
            if j == 0 {
                pre_r.push(r[j]);
                proof {
                    assert(min_r_prefix(r@, 1) == r@[0] as int);
                }
                assert(pre_r[j as int] as int == min_r_prefix(r@, j + 1));
            } else {
                let pr = pre_r[j - 1];
                let rj = r[j];
                let m = if rj < pr { rj } else { pr };
                pre_r.push(m);
                proof {
                    lemma_min_r_prefix_step(r@, (j + 1) as int);
                    assert(min_r_prefix(r@, j as int + 1) == m as int);
                }
                assert(pre_r[j as int] as int == min_r_prefix(r@, j + 1));
            }
            j = j + 1;
        }
        assert(forall|t: int| 0 <= t < n_i ==> pre_r[t as int] as int == min_r_prefix(r@, t + 1));
        let mut suf_r: Vec<i64> = Vec::new();
        let mut w = 0usize;
        while w < n
            invariant
                w <= n,
                r.len() == n,
                suf_r.len() == w,
            decreases n - w,
        {
            suf_r.push(0i64);
            w = w + 1;
        }
        let mut i3 = n;
        while i3 > 0
            invariant
                i3 <= n,
                n >= 2,
                n_i == r@.len(),
                r.len() == n,
                suf_r.len() == n,
                forall|j: int|
                    i3 <= j < n ==> #[trigger] suf_r[j as int] as int == min_r_suffix(r@, j, n_i),
            decreases i3,
        {
            i3 = i3 - 1;
            let idx = i3;
            proof {
                assert(idx < n);
                assert(idx < r.len());
            }
            if idx + 1 == n {
                suf_r.set(idx, r[idx]);
                proof {
                    assert(idx + 1 == n);
                    assert(idx == n - 1);
                    reveal_with_fuel(min_r_suffix, 10);
                    assert(min_r_suffix(r@, idx as int, n_i) == r@[idx as int] as int);
                }
                assert(suf_r[idx as int] as int == min_r_suffix(r@, idx as int, n_i));
            } else {
                let sr = suf_r[idx + 1];
                let rj = r[idx];
                suf_r.set(idx, if rj < sr { rj } else { sr });
                proof {
                    assert(idx + 1 < n);
                    assert(n_i == r@.len());
                    assert(idx as int + 2 <= n_i);
                    lemma_min_r_suffix_step(r@, idx as int, n_i);
                }
                assert(suf_r[idx as int] as int == min_r_suffix(r@, idx as int, n_i));
            }
        }
        assert(forall|j: int| 0 <= j < n_i ==> suf_r[j as int] as int == min_r_suffix(r@, j, n_i));
        proof {
            assert(forall|i: int|
                0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000);
        }
        let mut ans = 0i64;
        let mut witness = 0usize;
        let mut k = 0usize;
        while k < n
            invariant
                k <= n,
                n >= 2,
                n_i >= 2,
                n_i == l@.len(),
                n_i == r@.len(),
                l.len() == n,
                r.len() == n,
                pre_l.len() == n,
                suf_l.len() == n,
                pre_r.len() == n,
                suf_r.len() == n,
                forall|j: int|
                    0 <= j < n_i ==> #[trigger] pre_l[j as int] as int == max_l_prefix(l@, j + 1),
                forall|j: int|
                    0 <= j < n_i ==> #[trigger] suf_l[j as int] as int == max_l_suffix(l@, j, n_i),
                forall|j: int|
                    0 <= j < n_i ==> #[trigger] pre_r[j as int] as int == min_r_prefix(r@, j + 1),
                forall|j: int|
                    0 <= j < n_i ==> #[trigger] suf_r[j as int] as int == min_r_suffix(r@, j, n_i),
                forall|i: int|
                    0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000,
                witness < n,
                k == 0usize || intersection_len_excluding(l@, r@, n_i, witness as int) == ans as int,
                forall|t: int|
                    0 <= t < k as int ==> #[trigger] intersection_len_excluding(l@, r@, n_i, t) <= ans as int,
            decreases n - k,
        {
            proof {
                assert(k < n);
                assert(n >= 2);
                assert(1 < n);
                assert(k < pre_l.len());
                assert(k < suf_l.len());
            }
            let ghost kk = k as int;
            let ml = if k == 0 {
                suf_l[1]
            } else if k + 1 == n {
                pre_l[k - 1]
            } else {
                let a = pre_l[k - 1];
                let b = suf_l[k + 1];
                if a > b {
                    a
                } else {
                    b
                }
            };
            let mr = if k == 0 {
                suf_r[1]
            } else if k + 1 == n {
                pre_r[k - 1]
            } else {
                let a = pre_r[k - 1];
                let b = suf_r[k + 1];
                if a < b {
                    a
                } else {
                    b
                }
            };
            let cand = if ml > mr {
                0i64
            } else {
                proof {
                    assert(forall|i: int|
                        0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000);
                    assert(ml <= mr);
                    lemma_ml_mr_match_spec(
                        l@,
                        r@,
                        n_i,
                        pre_l@,
                        suf_l@,
                        pre_r@,
                        suf_r@,
                        kk,
                    );
                    lemma_max_l_excluding_nonneg(l@, n_i, kk);
                    assert(ml as int == max_l_excluding(l@, n_i, kk));
                    assert(mr as int == min_r_excluding(r@, n_i, kk));
                    assert((ml as int) >= 0);
                    assert((mr as int) <= 1_000_000_000);
                    assert(mr.checked_sub(ml).is_some());
                }
                mr.checked_sub(ml).unwrap()
            };
            proof {
                assert(2 <= n_i);
                assert(n_i == l@.len());
                assert(pre_l@.len() == n_i);
                assert(n_i <= l@.len());
                assert(forall|j: int|
                    0 <= j < n_i ==> #[trigger] pre_l@[j] as int == max_l_prefix(l@, j + 1));
                lemma_ml_mr_match_spec(
                    l@,
                    r@,
                    n_i,
                    pre_l@,
                    suf_l@,
                    pre_r@,
                    suf_r@,
                    kk,
                );
                lemma_cand_eq_intersection(l@, r@, n_i, ml, mr, kk);
                assert(cand as int == intersection_len_excluding(l@, r@, n_i, kk));
            }
            if k == 0 {
                ans = cand;
                witness = k;
            } else if cand > ans {
                ans = cand;
                witness = k;
            } else {
            }
            proof {
                assert forall|t: int|
                    0 <= t < (k + 1) as int implies intersection_len_excluding(l@, r@, n_i, t) <= ans as int by {
                    assert forall|t: int|
                        0 <= t < k as int implies intersection_len_excluding(l@, r@, n_i, t) <= ans as int by {
                        };
                    assert(intersection_len_excluding(l@, r@, n_i, kk) <= ans as int);
                }
                assert(intersection_len_excluding(l@, r@, n_i, witness as int) == ans as int);
            }
            k = k + 1;
        }
        proof {
            assert(forall|t: int|
                0 <= t < n_i ==> intersection_len_excluding(l@, r@, n_i, t) <= ans as int);
            assert(exists|t: int|
                t == witness as int && intersection_len_excluding(l@, r@, n_i, t) == ans as int);
        }
        ans
    }
}

}
