use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn feasible_teams(c: int, m: int, x: int, t: int) -> bool {
    0 <= t && t <= c && t <= m && 3 * t <= c + m + x
}

pub open spec fn min3(c: int, m: int, cap: int) -> int {
    if c <= m {
        if c <= cap {
            c
        } else {
            cap
        }
    } else {
        if m <= cap {
            m
        } else {
            cap
        }
    }
}

proof fn lemma_div_by_3_bounds(n: int)
    requires
        0 <= n,
    ensures
        3 * (n / 3) <= n,
        n < 3 * ((n / 3) + 1),
{
}

proof fn lemma_feasible_implies_t_leq_cap(c: int, m: int, x: int, t: int)
    requires
        feasible_teams(c, m, x, t),
    ensures
        t <= (c + m + x) / 3,
{
    let s = c + m + x;
    lemma_div_by_3_bounds(s);
    assert(3 * t <= s);
    assert(t <= s / 3) by {
        if t > s / 3 {
            assert(t >= s / 3 + 1);
            assert(3 * t >= 3 * (s / 3 + 1));
            assert(3 * (s / 3 + 1) > s);
            assert(false);
        }
    }
}

proof fn lemma_t_leq_each_implies_leq_min3(t: int, c: int, m: int, cap: int)
    requires
        t <= c,
        t <= m,
        t <= cap,
    ensures
        t <= min3(c, m, cap),
{
    let w = min3(c, m, cap);
    if c <= m {
        if c <= cap {
            assert(w == c);
            assert(t <= w);
        } else {
            assert(w == cap);
            assert(t <= cap);
            assert(t <= w);
        }
    } else {
        if m <= cap {
            assert(w == m);
            assert(t <= w);
        } else {
            assert(w == cap);
            assert(t <= cap);
            assert(t <= w);
        }
    }
}

proof fn lemma_impl_matches_min3(c: int, m: int, cap: int, r: int)
    requires
        r == if m < c {
            if cap < m {
                cap
            } else {
                m
            }
        } else {
            if cap < c {
                cap
            } else {
                c
            }
        },
    ensures
        r == min3(c, m, cap),
{
    if m < c {
        assert((c <= m) == false);
        assert(min3(c, m, cap) == if m <= cap { m } else { cap });
        if cap < m {
            assert(r == cap);
            assert(min3(c, m, cap) == cap);
        } else {
            assert(r == m);
            assert(min3(c, m, cap) == m);
        }
    } else {
        assert(m >= c);
        assert(min3(c, m, cap) == if c <= cap { c } else { cap });
        if cap < c {
            assert(r == cap);
            assert(min3(c, m, cap) == cap);
        } else {
            assert(r == c);
            assert(min3(c, m, cap) == c);
        }
    }
}

impl Solution {
    pub fn max_perfect_teams(c: i64, m: i64, x: i64) -> (res: i64)
        requires
            0 <= c <= 100_000_000,
            0 <= m <= 100_000_000,
            0 <= x <= 100_000_000,
        ensures
            feasible_teams(c as int, m as int, x as int, res as int),
            forall|t: int|
                #[trigger] feasible_teams(c as int, m as int, x as int, t) ==> t <= res as int,
    {
        let s = c + m + x;
        let cap = s / 3;
        let mut r = c;
        if m < r {
            r = m;
        }
        if cap < r {
            r = cap;
        }
        proof {
            let ci = c as int;
            let mi = m as int;
            let xi = x as int;
            let si = ci + mi + xi;
            let capi = si / 3;
            lemma_div_by_3_bounds(si);
            assert(s as int == si);
            assert(cap as int == capi);
            assert(r as int == if mi < ci {
                if capi < mi {
                    capi
                } else {
                    mi
                }
            } else {
                if capi < ci {
                    capi
                } else {
                    ci
                }
            });
            lemma_impl_matches_min3(ci, mi, capi, r as int);
            assert(r as int == min3(ci, mi, capi));
            assert(feasible_teams(ci, mi, xi, r as int)) by {
                assert((r as int) <= ci);
                assert((r as int) <= mi);
                assert((r as int) <= capi);
                assert(3 * (r as int) <= 3 * capi);
                assert(3 * capi <= si);
                assert(3 * (r as int) <= si);
            }
            assert forall|t: int| feasible_teams(ci, mi, xi, t) implies t <= r as int by {
                if feasible_teams(ci, mi, xi, t) {
                    lemma_feasible_implies_t_leq_cap(ci, mi, xi, t);
                    assert(t <= ci);
                    assert(t <= mi);
                    assert(t <= capi);
                    lemma_t_leq_each_implies_leq_min3(t, ci, mi, capi);
                    assert(t <= min3(ci, mi, capi));
                    assert(t <= r as int);
                }
            }
        }
        r
    }
}

}
