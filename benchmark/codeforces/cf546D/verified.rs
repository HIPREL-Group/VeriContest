use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn divides(n: int, d: int) -> bool {
    1 <= d && n % d == 0
}

pub open spec fn has_factor_below(n: int, bound: int) -> bool
    recommends
        2 <= bound,
{
    exists|d: int| 2 <= d < bound && #[trigger] divides(n, d)
}

pub open spec fn least_divisor(n: int, d: int) -> bool {
    &&& 2 <= d <= n
    &&& divides(n, d)
    &&& forall|e: int| 2 <= e < d && #[trigger] divides(n, e) ==> false
}

pub open spec fn is_prime(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d < n && #[trigger] divides(n, d) ==> false
}

pub open spec fn smallest_divisor_from(n: int, d: int) -> int
    recommends
        2 <= d <= n,
    decreases n - d,
{
    if d >= n {
        n
    } else if n % d == 0 {
        d
    } else {
        smallest_divisor_from(n, d + 1)
    }
}

pub open spec fn smallest_prime_divisor(n: int) -> int
    recommends
        2 <= n,
{
    smallest_divisor_from(n, 2)
}

pub open spec fn omega(n: int) -> int
    recommends
        1 <= n,
    decreases n,
{
    if n <= 1 {
        0
    } else {
        let q = n / smallest_prime_divisor(n);
        if q >= n {
            1
        } else if q <= 1 {
            1
        } else {
            1 + omega(q)
        }
    }
}

pub open spec fn omega_prefix(n: int) -> int
    recommends
        0 <= n,
    decreases n,
{
    if n <= 1 {
        0
    } else {
        omega_prefix(n - 1) + omega(n)
    }
}

pub open spec fn omega_interval_sum(lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi,
    decreases hi - lo,
{
    if hi <= lo {
        0
    } else {
        omega_interval_sum(lo, hi - 1) + omega(hi)
    }
}

proof fn lemma_smallest_divisor_from_properties(n: int, d: int)
    requires
        2 <= d <= n,
    ensures
        d <= smallest_divisor_from(n, d) <= n,
        divides(n, smallest_divisor_from(n, d)),
        forall|e: int| d <= e < smallest_divisor_from(n, d) && #[trigger] divides(n, e) ==> false,
    decreases n - d,
{
    if d >= n {
        assert(n % n == 0) by (nonlinear_arith)
            requires 2 <= n,
        {
        }
        assert(divides(n, n));
    } else if n % d == 0 {
    } else {
        lemma_smallest_divisor_from_properties(n, d + 1);
    }
}

proof fn lemma_divisibility_transitive(n: int, d: int, e: int)
    requires
        1 <= e <= d <= n,
        n % d == 0,
        d % e == 0,
    ensures
        n % e == 0,
{
    let q1 = n / d;
    let q2 = d / e;
    assert(n == q1 * d) by (nonlinear_arith)
        requires q1 == n / d, n % d == 0, d >= 1,
    {
    }
    assert(d == q2 * e) by (nonlinear_arith)
        requires q2 == d / e, d % e == 0, e >= 1,
    {
    }
    assert(n == (q1 * q2) * e) by (nonlinear_arith)
        requires n == q1 * d, d == q2 * e,
    {
    }
    assert(n % e == 0) by (nonlinear_arith)
        requires n == (q1 * q2) * e, e >= 1,
    {
    }
}

proof fn lemma_smallest_prime_divisor_properties(n: int)
    requires
        2 <= n,
    ensures
        least_divisor(n, smallest_prime_divisor(n)),
        is_prime(smallest_prime_divisor(n)),
{
    lemma_smallest_divisor_from_properties(n, 2);
    let s = smallest_prime_divisor(n);
    assert(least_divisor(n, s));
    assert forall|e: int| 2 <= e < s && #[trigger] divides(s, e) implies false by {
        if divides(s, e) {
            lemma_divisibility_transitive(n, s, e);
            assert(divides(n, e));
            assert(false);
        }
    }
}

proof fn lemma_least_divisor_is_smallest(n: int, d: int)
    requires
        2 <= n,
        least_divisor(n, d),
    ensures
        d == smallest_prime_divisor(n),
{
    lemma_smallest_divisor_from_properties(n, 2);
    let s = smallest_prime_divisor(n);
    assert(n % s == 0);
    if s < d {
        assert(n % s != 0);
        assert(false);
    }
    if d < s {
        assert(n % d != 0);
        assert(false);
    }
}

proof fn lemma_omega_spd_bound(n: int)
    requires
        2 <= n,
    ensures
        n / smallest_prime_divisor(n) < n,
        1 <= n / smallest_prime_divisor(n),
{
    lemma_smallest_prime_divisor_properties(n);
    let d = smallest_prime_divisor(n);
    assert(2 <= d <= n);
    assert(n % d == 0);
    let q = n / d;
    assert(1 <= q) by (nonlinear_arith)
        requires 2 <= d, d <= n, q == n / d, n % d == 0,
    {
    }
    assert(q < n) by (nonlinear_arith)
        requires 2 <= d, d <= n, q == n / d, n % d == 0,
    {
    }
}

proof fn lemma_omega_bound(n: int)
    requires
        1 <= n,
    ensures
        0 <= omega(n) <= n,
    decreases n,
{
    if n > 1 {
        lemma_smallest_prime_divisor_properties(n);
        lemma_omega_spd_bound(n);
        let d = smallest_prime_divisor(n);
        let q = n / d;
        assert(1 <= q < n) by (nonlinear_arith)
            requires
                2 <= d <= n,
                q == n / d,
                n % d == 0,
        {
        }
        lemma_omega_bound(q);
        assert(q < n);
        assert(omega(n) == 1 + omega(q));
        assert(1 + omega(q) <= n) by (nonlinear_arith)
            requires
                1 <= q < n,
                omega(q) <= q,
        {
        }
    }
}

proof fn lemma_omega_prefix_bound(n: int)
    requires
        0 <= n,
    ensures
        0 <= omega_prefix(n) <= n * n,
    decreases n,
{
    if n > 1 {
        lemma_omega_prefix_bound(n - 1);
        lemma_omega_bound(n);
        assert(omega_prefix(n) == omega_prefix(n - 1) + omega(n));
        assert(omega_prefix(n) <= n * n) by (nonlinear_arith)
            requires
                0 <= omega_prefix(n - 1) <= (n - 1) * (n - 1),
                0 <= omega(n) <= n,
        {
        }
    }
}

proof fn lemma_omega_prefix_difference(lo: int, hi: int)
    requires
        0 <= lo <= hi,
    ensures
        omega_prefix(hi) - omega_prefix(lo) == omega_interval_sum(lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_omega_prefix_difference(lo, hi - 1);
    }
}

proof fn lemma_omega_interval_nonnegative(lo: int, hi: int)
    requires
        0 <= lo <= hi,
    ensures
        0 <= omega_interval_sum(lo, hi),
    decreases hi - lo,
{
    if hi > lo {
        lemma_omega_interval_nonnegative(lo, hi - 1);
        lemma_omega_bound(hi);
    }
}

impl Solution {
    pub fn max_scores_for_games(queries: Vec<(i32, i32)>) -> (res: Vec<u64>)
        requires
            1 <= queries.len() <= 1_000_000,
            forall|k: int|
                0 <= k < queries.len() ==> {
                    let (a, b) = #[trigger] queries[k];
                    1 <= b <= a <= 5_000_000
                },
        ensures
            res.len() == queries.len(),
            forall|k: int|
                0 <= k < res.len() ==> #[trigger] res[k] as int == omega_interval_sum(
                    queries[k].1 as int,
                    queries[k].0 as int,
                ),
    {
        let mut spf: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i <= 5_000_000usize
            invariant
                i <= 5_000_001usize,
                spf.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] spf[j] == 0usize,
            decreases 5_000_001usize - i,
        {
            spf.push(0usize);
            i = i + 1;
        }

        i = 2usize;
        proof {
            assert forall|m: int| 2 <= m <= 5_000_000 && spf[m] != 0usize implies #[trigger] least_divisor(m, spf[m] as int) by {
                assert(0 <= m && m < 5_000_001);
                assert(spf[m] == 0usize);
            }
        }
        while i <= 5_000_000usize
            invariant
                spf.len() == 5_000_001usize,
                2usize <= i <= 5_000_001usize,
                forall|m: int| 2 <= m <= 5_000_000 && spf[m] != 0usize ==> #[trigger] least_divisor(m, spf[m] as int),
                forall|m: int| 2 <= m <= 5_000_000 && #[trigger] has_factor_below(m, i as int) ==> spf[m] != 0usize,
            decreases 5_000_001usize - i,
        {
            let mut j = i;
            while j <= 5_000_000usize
                invariant
                    spf.len() == 5_000_001usize,
                    2usize <= i <= 5_000_000usize,
                    i <= j <= 5_000_000usize + i,
                    j as int % (i as int) == 0,
                    forall|m: int| 2 <= m <= 5_000_000 && spf[m] != 0usize ==> #[trigger] least_divisor(m, spf[m] as int),
                    forall|m: int| 2 <= m <= 5_000_000 && #[trigger] has_factor_below(m, i as int) ==> spf[m] != 0usize,
                    forall|m: int| #![trigger spf[m]] i as int <= m < j as int && m % (i as int) == 0 ==> spf[m] != 0usize && least_divisor(m, spf[m] as int),
                decreases 5_000_000usize + i - j,
            {
                let cur = j;
                let ghost old_spf = spf@;
                if spf[j] == 0usize {
                    spf.set(j, i);
                    proof {
                        assert(old_spf[cur as int] == 0usize);
                        assert(cur as int % (i as int) == 0);
                        assert(divides(cur as int, i as int));
                        assert(least_divisor(cur as int, i as int)) by {
                            assert(2 <= i as int);
                            assert(i as int <= cur as int);
                            assert forall|e: int| 2 <= e < i as int && #[trigger] divides(cur as int, e) implies false by {
                                if divides(cur as int, e) {
                                    assert(has_factor_below(cur as int, i as int));
                                    assert(old_spf[cur as int] != 0usize);
                                    assert(false);
                                }
                            }
                        }
                        assert(spf@ == old_spf.update(cur as int, i));
                        assert forall|m: int| 2 <= m <= 5_000_000 && spf[m] != 0usize implies #[trigger] least_divisor(m, spf[m] as int) by {
                            if m == cur as int {
                            } else {
                                assert(spf[m] == old_spf[m]);
                            }
                        }
                        assert forall|m: int| #![trigger spf[m]] i as int <= m < cur as int && m % (i as int) == 0 implies spf[m] != 0usize && least_divisor(m, spf[m] as int) by {
                            assert(m != cur as int);
                            assert(spf[m] == old_spf[m]);
                            assert(old_spf[m] != 0usize);
                            assert(least_divisor(m, old_spf[m] as int));
                        }
                    }
                }
                let ghost old_j = j;
                j = j + i;
                proof {
                    let ghost ji = j as int;
                    let ghost oji = old_j as int;
                    let ghost ii = i as int;
                    assert(ji == oji + ii);
                    assert(ji % ii == 0) by (nonlinear_arith)
                        requires oji % ii == 0, ji == oji + ii, ii >= 2,
                    {
                    }
                    assert forall|m: int| #![trigger spf[m]] i as int <= m < j as int && m % (i as int) == 0 implies spf[m] != 0usize && least_divisor(m, spf[m] as int) by {
                        if m < old_j as int {
                        } else if m == cur as int {
                            assert(2 <= m && m <= 5_000_000);
                            assert(spf[m] != 0usize);
                        } else {
                            let ghost ci = cur as int;
                            let ghost ii = i as int;
                            assert(ci % ii == 0);
                            assert(m % ii == 0);
                            assert(false) by (nonlinear_arith)
                                requires
                                    ci < m,
                                    m < ci + ii,
                                    m % ii == 0,
                                    ci % ii == 0,
                                    ii >= 2,
                            {
                            }
                        }
                    }
                }
            }
            proof {
                assert forall|m: int| 2 <= m <= 5_000_000 && #[trigger] has_factor_below(m, i as int + 1) implies spf[m] != 0usize by {
                    if has_factor_below(m, i as int) {
                    } else {
                        let d = choose|d: int| 2 <= d < i as int + 1 && divides(m, d);
                        assert(2 <= d && d < i as int + 1);
                        assert(!(d < i as int));
                        assert(d == i as int);
                        assert(divides(m, i as int));
                        assert(m % (i as int) == 0);
                        let ghost ii = i as int;
                        assert(ii <= m) by (nonlinear_arith)
                            requires 2 <= ii, 2 <= m, m % ii == 0,
                        {
                        }
                        assert(i as int <= m);
                        assert(m < j as int);
                        let ghost _trigger = spf[m];
                        assert(spf[m] != 0usize);
                    }
                }
            }
            i = i + 1;
        }

        proof {
            assert forall|m: int| 2 <= m <= 5_000_000 implies spf[m] != 0usize by {
                assert(m % m == 0) by (nonlinear_arith)
                    requires m >= 2,
                {
                }
                assert(divides(m, m));
                assert(2 <= m && m < 5_000_001);
                assert(has_factor_below(m, 5_000_001int));
            }
        }

        let ghost orig_spf = spf@;
        i = 2usize;
        while i <= 5_000_000usize
            invariant
                spf.len() == 5_000_001usize,
                2usize <= i <= 5_000_001usize,
                forall|m: int| 2 <= m <= 5_000_000 ==> orig_spf[m] != 0usize && least_divisor(m, orig_spf[m] as int),
                forall|k: int| 2 <= k < i as int ==> #[trigger] spf[k] as int == omega(k) && spf[k] as int <= k,
                forall|m: int| i as int <= m <= 5_000_000 ==> #[trigger] spf[m] == orig_spf[m],
            decreases 5_000_001usize - i,
        {
            proof {
                assert(spf[i as int] == orig_spf[i as int]);
                assert(least_divisor(i as int, orig_spf[i as int] as int));
                lemma_least_divisor_is_smallest(i as int, orig_spf[i as int] as int);
                lemma_smallest_prime_divisor_properties(i as int);
                lemma_omega_spd_bound(i as int);
                lemma_omega_bound(i as int);
            }
            let d = spf[i];
            let q = i / d;
            proof {
                let ghost ii = i as int;
                let ghost di = d as int;
                let ghost qi = q as int;
                assert(di == smallest_prime_divisor(ii));
                assert(ii % di == 0);
                assert(1 <= qi && qi < ii) by (nonlinear_arith)
                    requires 2 <= di, di <= ii, qi == ii / di, ii % di == 0,
                {
                }
            }
            if q <= 1 {
                spf.set(i, 1usize);
                proof {
                    let ghost ii = i as int;
                    let ghost qi = q as int;
                    assert(qi == ii / smallest_prime_divisor(ii));
                    assert(qi < ii);
                    assert(qi <= 1);
                    assert(omega(ii) == 1);
                    assert forall|k: int| 2 <= k < ii + 1 implies #[trigger] spf[k] as int == omega(k) && spf[k] as int <= k by {
                        if k < ii {
                        } else {
                        }
                    }
                    assert forall|m: int| ii + 1 <= m <= 5_000_000 implies #[trigger] spf[m] == orig_spf[m] by {
                    }
                }
            } else {
                proof {
                    let ghost qi = q as int;
                    let ghost ii = i as int;
                    assert(2 <= qi && qi < ii);
                    assert(spf[qi] as int == omega(qi));
                    assert(spf[qi] as int <= qi);
                }
                let omega_val = spf[q] + 1;
                spf.set(i, omega_val);
                proof {
                    let ghost ii = i as int;
                    let ghost qi = q as int;
                    assert(qi == ii / smallest_prime_divisor(ii));
                    assert(qi < ii);
                    assert(qi > 1);
                    assert(omega(ii) == 1 + omega(qi));
                    assert(omega_val as int == omega(ii));
                    assert(omega(ii) <= ii);
                    assert forall|k: int| 2 <= k < ii + 1 implies #[trigger] spf[k] as int == omega(k) && spf[k] as int <= k by {
                        if k < ii {
                        } else {
                        }
                    }
                    assert forall|m: int| ii + 1 <= m <= 5_000_000 implies #[trigger] spf[m] == orig_spf[m] by {
                    }
                }
            }
            i = i + 1;
        }

        let mut prefix: Vec<u64> = Vec::new();
        prefix.push(0u64);
        prefix.push(0u64);

        i = 2usize;
        while i <= 5_000_000usize
            invariant
                spf.len() == 5_000_001usize,
                prefix.len() == i,
                2usize <= i <= 5_000_001usize,
                forall|k: int| 2 <= k <= 5_000_000 ==> #[trigger] spf[k] as int == omega(k) && spf[k] as int <= k,
                prefix[0] == 0u64,
                prefix[1] == 0u64,
                forall|k: int| 0 <= k < i as int ==> #[trigger] prefix[k] as int == omega_prefix(k) && prefix[k] as int <= k * k,
            decreases 5_000_001usize - i,
        {
            let ghost ii = i as int;
            let ghost prefix_at_im1: int = prefix[i - 1] as int;
            proof {
                assert(prefix_at_im1 <= (ii - 1) * (ii - 1));
                lemma_omega_bound(ii);
                lemma_omega_prefix_bound(ii - 1);
            }
            let value = spf[i] as u64;
            proof {
                let ghost vi = value as int;
                assert(vi == omega(ii));
                assert(vi <= ii);
                assert(prefix_at_im1 + vi <= 25_000_005_000_000) by (nonlinear_arith)
                    requires
                        0 <= prefix_at_im1,
                        prefix_at_im1 <= (ii - 1) * (ii - 1),
                        0 <= vi,
                        vi <= ii,
                        2 <= ii,
                        ii <= 5_000_000,
                {
                }
            }
            let total = prefix[i - 1] + value;
            let ghost old_prefix = prefix@;
            prefix.push(total);
            proof {
                assert(total as int == prefix_at_im1 + value as int);
                assert(total as int == omega_prefix(ii)) by {
                    assert(prefix_at_im1 == omega_prefix(ii - 1));
                    assert(omega_prefix(ii) == omega_prefix(ii - 1) + omega(ii));
                }
                let ghost vi = value as int;
                let ghost ti = total as int;
                assert(ti <= ii * ii) by (nonlinear_arith)
                    requires
                        0 <= prefix_at_im1,
                        prefix_at_im1 <= (ii - 1) * (ii - 1),
                        0 <= vi,
                        vi <= ii,
                        2 <= ii,
                        ti == prefix_at_im1 + vi,
                {
                }
                assert(prefix@ == old_prefix.push(total));
                assert forall|k: int| 0 <= k < ii + 1 implies #[trigger] prefix[k] as int == omega_prefix(k) && prefix[k] as int <= k * k by {
                    if k == ii {
                        assert(prefix[k] == total);
                    } else {
                        assert(k < ii);
                        assert(prefix[k] == old_prefix[k]);
                    }
                }
            }
            i = i + 1;
        }

        let mut res = Vec::new();
        i = 0usize;
        while i < queries.len()
            invariant
                prefix.len() == 5_000_001usize,
                i <= queries.len(),
                res.len() == i,
                forall|k: int|
                    0 <= k < queries.len() ==> {
                        let (a, b) = #[trigger] queries[k];
                        1 <= b <= a <= 5_000_000
                    },
                forall|k: int| 0 <= k <= 5_000_000 ==> #[trigger] prefix[k] as int == omega_prefix(k),
                forall|k: int|
                    0 <= k < i as int ==> #[trigger] res[k] as int == omega_interval_sum(
                        queries[k].1 as int,
                        queries[k].0 as int,
                    ),
            decreases queries.len() - i,
        {
            let cur = i;
            let (a, b) = queries[i];
            proof {
                lemma_omega_prefix_difference(b as int, a as int);
                lemma_omega_interval_nonnegative(b as int, a as int);
                assert(prefix[a as int] as int - prefix[b as int] as int == omega_interval_sum(b as int, a as int));
                assert(prefix[b as int] as int <= prefix[a as int] as int);
            }
            let answer = prefix[a as usize] - prefix[b as usize];
            proof {
                assert(answer as int == omega_interval_sum(b as int, a as int)) by {
                    assert(prefix[a as int] as int == omega_prefix(a as int));
                    assert(prefix[b as int] as int == omega_prefix(b as int));
                }
            }
            let ghost old_res = res@;
            res.push(answer);
            i = i + 1;
            proof {
                assert(res@ == old_res.push(answer));
                assert forall|k: int|
                    0 <= k < i as int implies #[trigger] res[k] as int == omega_interval_sum(
                        queries[k].1 as int,
                        queries[k].0 as int,
                    ) by {
                    if k == cur as int {
                        assert(res[k] == answer);
                    } else {
                        assert(k < cur as int);
                        assert(res[k] == old_res[k]);
                    }
                }
            }
        }
        res
    }
}

}
