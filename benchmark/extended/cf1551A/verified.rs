use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_abs_i(x: int) -> int {
    if x < 0 {
        -x
    } else {
        x
    }
}

pub open spec fn spec_abs_diff(c1: int, c2: int) -> int {
    if c1 >= c2 {
        c1 - c2
    } else {
        c2 - c1
    }
}

pub open spec fn spec_feasible(c1: int, c2: int, n: int) -> bool {
    c1 >= 0 && c2 >= 0 && c1 + 2 * c2 == n
}

pub open spec fn spec_k_feasible(k: int, n: int) -> bool {
    0 <= k && 2 * k <= n
}

pub open spec fn spec_abs_triple(n: int, k: int) -> int {
    spec_abs_i(n - 3 * k)
}

pub open spec fn spec_k_lo(n: int) -> int {
    n / 3
}

pub open spec fn spec_k_hi(n: int) -> int {
    (n + 2) / 3
}

proof fn lemma_div3_bounds(n: int)
    requires
        0 <= n,
    ensures
        3 * (n / 3) <= n,
        n < 3 * ((n / 3) + 1),
{
}

proof fn lemma_two_floor_le_n(n: int)
    requires
        0 <= n,
    ensures
        2 * (n / 3) <= n,
{
    lemma_div3_bounds(n);
    assert(2 * (n / 3) <= 3 * (n / 3));
    assert(3 * (n / 3) <= n);
}

proof fn lemma_k_lo_feasible(n: int)
    requires
        1 <= n,
    ensures
        spec_k_feasible(n / 3, n),
{
    lemma_two_floor_le_n(n);
    assert(0 <= n / 3);
}

proof fn lemma_feasible_char(c1: int, c2: int, n: int)
    requires
        spec_feasible(c1, c2, n),
    ensures
        c1 == n - 2 * c2,
        spec_k_feasible(c2, n),
{
    assert(c1 + 2 * c2 == n);
    assert(c1 == n - 2 * c2);
    assert(2 * c2 <= c1 + 2 * c2);
    assert(2 * c2 <= n);
}

proof fn lemma_abs_diff_eq_triple(n: int, c1: int, c2: int)
    requires
        spec_feasible(c1, c2, n),
    ensures
        spec_abs_diff(c1, c2) == spec_abs_triple(n, c2),
{
    lemma_feasible_char(c1, c2, n);
    assert(c1 - c2 == n - 3 * c2);
    if c1 >= c2 {
        assert(n - 3 * c2 >= 0);
        assert(spec_abs_diff(c1, c2) == c1 - c2);
        assert(spec_abs_triple(n, c2) == n - 3 * c2);
    } else {
        assert(n - 3 * c2 < 0);
        assert(spec_abs_diff(c1, c2) == c2 - c1);
        assert(spec_abs_triple(n, c2) == 3 * c2 - n);
    }
}

proof fn lemma_abs_nonneg(x: int)
    ensures
        spec_abs_i(x) >= 0,
{
}

proof fn lemma_mod0_triple(n: int, k: int, q: int)
    requires
        n == 3 * q,
        spec_k_feasible(k, n),
        q >= 0,
    ensures
        spec_abs_triple(n, k) >= spec_abs_triple(n, q),
        spec_abs_triple(n, q) == 0,
{
    assert(n - 3 * q == 0);
    assert(spec_abs_triple(n, q) == 0);
    lemma_abs_nonneg(n - 3 * k);
}

proof fn lemma_three_times_plus1_neq0(m: int)
    ensures
        3 * m + 1 != 0,
{
    assert(3 * m + 1 != 0) by {
        if 3 * m + 1 == 0 {
            assert(3 * m == -1);
            assert(false);
        }
    };
}

proof fn lemma_mod1_triple(n: int, k: int, q: int)
    requires
        n == 3 * q + 1,
        q >= 0,
        spec_k_feasible(k, n),
    ensures
        spec_abs_triple(n, k) >= spec_abs_triple(n, q),
{
    assert(n - 3 * k == 3 * (q - k) + 1);
    lemma_three_times_plus1_neq0(q - k);
    assert(n - 3 * k != 0);
    lemma_abs_nonneg(n - 3 * k);
    assert(spec_abs_triple(n, k) >= 1);
    assert(n - 3 * q == 1);
    assert(spec_abs_triple(n, q) == 1);
}

proof fn lemma_three_times_plus2_neq0(m: int)
    ensures
        3 * m + 2 != 0,
{
    assert(3 * m + 2 != 0) by {
        if 3 * m + 2 == 0 {
            assert(3 * m == -2);
            assert(false);
        }
    };
}

proof fn lemma_mod2_triple(n: int, k: int, q: int, k_res: int)
    requires
        n == 3 * q + 2,
        q >= 0,
        spec_k_feasible(k, n),
        k_res == (n + 2) / 3,
        spec_k_feasible(k_res, n),
    ensures
        spec_abs_triple(n, k) >= spec_abs_triple(n, k_res),
{
    assert(n - 3 * k == 3 * (q - k) + 2);
    lemma_three_times_plus2_neq0(q - k);
    assert(n - 3 * k != 0);
    lemma_abs_nonneg(n - 3 * k);
    assert(spec_abs_triple(n, k) >= 1);
    assert((n + 2) / 3 == (3 * q + 4) / 3);
    assert((3 * q + 4) / 3 == q + 1);
    assert(k_res == q + 1);
    assert(n - 3 * k_res == -1);
    assert(spec_abs_triple(n, k_res) == 1);
}

proof fn lemma_c2_when_mod0(n: i64, c2: i64, q: int)
    requires
        1 <= n <= 1_000_000_000,
        n % 3 == 0,
        q == (n as int) / 3,
        c2 == n / 3,
    ensures
        c2 as int == q,
{
    assert((n as int) % 3 == 0);
    assert((n as int) == 3 * q);
    assert(n / 3 == q as i64);
}

proof fn lemma_c2_when_mod1(n: i64, c2: i64, q: int)
    requires
        1 <= n <= 1_000_000_000,
        n % 3 == 1,
        q == (n as int) / 3,
        c2 == {
            let k_lo = n / 3;
            let d_lo = n - 3 * k_lo;
            let k_hi = (n + 2) / 3;
            if k_hi != k_lo && 2 * k_hi <= n {
                let t = n - 3 * k_hi;
                let d_hi = if t < 0 {
                    -t
                } else {
                    t
                };
                if d_hi < d_lo {
                    k_hi
                } else {
                    k_lo
                }
            } else {
                k_lo
            }
        },
    ensures
        c2 as int == q,
{
    let k_lo = n / 3;
    let d_lo = n - 3 * k_lo;
    let k_hi = (n + 2) / 3;
    assert((n as int) == 3 * q + 1);
    if q == 0 {
        assert(n == 1);
        assert(k_hi == 1);
        assert(!(2 * k_hi <= n));
        assert(c2 == k_lo);
        assert(c2 == 0);
        assert(q == 0);
    } else {
        assert(q >= 1);
        assert(k_hi != k_lo);
        assert(2 * k_hi <= n);
        let t = n - 3 * k_hi;
        let d_hi = if t < 0 {
            -t
        } else {
            t
        };
        assert(d_hi == 2);
        assert(d_lo == 1);
        assert(!(d_hi < d_lo));
        assert(c2 == k_lo);
        assert(c2 as int == q);
    }
}

proof fn lemma_c2_when_mod2(n: i64, c2: i64, q: int)
    requires
        1 <= n <= 1_000_000_000,
        n % 3 == 2,
        q == (n as int) / 3,
        c2 == {
            let k_lo = n / 3;
            let d_lo = n - 3 * k_lo;
            let k_hi = (n + 2) / 3;
            if k_hi != k_lo && 2 * k_hi <= n {
                let t = n - 3 * k_hi;
                let d_hi = if t < 0 {
                    -t
                } else {
                    t
                };
                if d_hi < d_lo {
                    k_hi
                } else {
                    k_lo
                }
            } else {
                k_lo
            }
        },
    ensures
        c2 as int == (n as int + 2) / 3,
{
    let k_lo = n / 3;
    let k_hi = (n + 2) / 3;
    assert((n as int) == 3 * q + 2);
    assert(k_hi != k_lo);
    assert(2 * k_hi <= n);
    let d_lo = n - 3 * k_lo;
    let t = n - 3 * k_hi;
    let d_hi = if t < 0 {
        -t
    } else {
        t
    };
    assert(d_lo == 2);
    assert(d_hi == 1);
    assert(d_hi < d_lo);
    assert(c2 == k_hi);
    assert(c2 as int == (n as int + 2) / 3);
}

impl Solution {
    pub fn polycarp_coins(n: i64) -> (res: (i64, i64))
        requires
            1 <= n <= 1_000_000_000,
        ensures
            spec_feasible(res.0 as int, res.1 as int, n as int),
            forall|c1p: int, c2p: int|
                spec_feasible(c1p, c2p, n as int) ==> #[trigger] spec_abs_diff(res.0 as int, res.1 as int)
                    <= spec_abs_diff(c1p, c2p),
            exists|c1e: int, c2e: int|
                c1e == res.0 as int && c2e == res.1 as int && #[trigger] spec_feasible(c1e, c2e, n as int),
    {
        let k_lo = n / 3;
        let d_lo = n - 3 * k_lo;
        let k_hi = (n + 2) / 3;
        let c2 = if k_hi != k_lo && 2 * k_hi <= n {
            let t = n - 3 * k_hi;
            let d_hi = if t < 0 {
                -t
            } else {
                t
            };
            if d_hi < d_lo {
                k_hi
            } else {
                k_lo
            }
        } else {
            k_lo
        };
        let c1 = n - 2 * c2;
        proof {
            assert(exists|c1e: int, c2e: int|
                c1e == c1 as int && c2e == c2 as int && spec_feasible(c1e, c2e, n as int)) by {
                assert(spec_feasible(c1 as int, c2 as int, n as int));
            };
            let ni = n as int;
            let q = ni / 3;
            lemma_k_lo_feasible(ni);
            assert(spec_k_feasible(c2 as int, ni));
            assert(c1 == n - 2 * c2);
            assert(spec_feasible(c1 as int, c2 as int, ni));
            assert forall|c1p: int, c2p: int|
                spec_feasible(c1p, c2p, ni) implies spec_abs_diff(c1 as int, c2 as int)
                    <= spec_abs_diff(c1p, c2p)
            by {
                let kp = c2p;
                lemma_abs_diff_eq_triple(ni, c1 as int, c2 as int);
                lemma_abs_diff_eq_triple(ni, c1p, c2p);
                let r = n % 3;
                if r == 0 {
                    lemma_c2_when_mod0(n, c2, q);
                    assert(ni == 3 * q);
                    lemma_mod0_triple(ni, kp, q);
                } else if r == 1 {
                    lemma_c2_when_mod1(n, c2, q);
                    assert(ni == 3 * q + 1);
                    lemma_mod1_triple(ni, kp, q);
                } else {
                    assert(r == 2);
                    lemma_c2_when_mod2(n, c2, q);
                    assert(ni == 3 * q + 2);
                    lemma_mod2_triple(ni, kp, q, c2 as int);
                }
            };
        }
        (c1, c2)
    }
}

}
