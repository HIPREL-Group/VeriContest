use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_divisor(n: int, d: int) -> bool
    {
        d > 0 && d < n && n % d == 0
    }

    pub open spec fn sum_divisors_up_to(n: int, k: int) -> int
        decreases k,
    {
        if k <= 0 {
            0
        } else if Self::is_divisor(n, k) {
            k + Self::sum_divisors_up_to(n, k - 1)
        } else {
            Self::sum_divisors_up_to(n, k - 1)
        }
    }

    pub open spec fn paired_sum_upto(n: int, k: int) -> int
        decreases k
    {
        if k <= 0 {
            0
        } else if n % k == 0 {
            (if k != n / k { k + n / k } else { k }) + Self::paired_sum_upto(n, k - 1)
        } else {
            Self::paired_sum_upto(n, k - 1)
        }
    }

    pub open spec fn total_covered_sum(n: int, k: int, d: int) -> int
        decreases d
    {
        if d <= 0 {
            0
        } else {
            (if n % d == 0 && (d <= k || n / d <= k) { d } else { 0 })
                + Self::total_covered_sum(n, k, d - 1)
        }
    }

    proof fn lemma_total_covered_zero(n: int, d: int)
        requires
            n >= 1,
            d >= 0,
        ensures
            Self::total_covered_sum(n, 0, d) == 0,
        decreases d,
    {
        if d > 0 {
            Self::lemma_total_covered_zero(n, d - 1);
            let term = if n % d == 0 && (d <= 0 || n / d <= 0) { d } else { 0nat as int };
            assert(Self::total_covered_sum(n, 0, d) == term + Self::total_covered_sum(n, 0, d - 1));
            if n % d == 0 {
                assert(n / d >= 1) by (nonlinear_arith)
                    requires
                        n >= 1,
                        d >= 1,
                        n % d == 0;
                assert(term == 0);
            } else {
                assert(term == 0);
            }
        } else {
            assert(d == 0);
            assert(Self::total_covered_sum(n, 0, d) == 0);
        }
    }

    proof fn lemma_covered_delta(n: int, k: int, d: int)
        requires
            n >= 1,
            k >= 1,
            k * k <= n,
            d >= 0,
        ensures
            Self::total_covered_sum(n, k, d) == Self::total_covered_sum(n, k - 1, d)
                + (if d >= k && n % k == 0 { k } else { 0 })
                + (if k != n / k && n % k == 0 && d >= n / k { n / k } else { 0 }),
        decreases d,
    {
        if d <= 0 {
            assert(d == 0);
            assert(Self::total_covered_sum(n, k, 0) == 0);
            assert(Self::total_covered_sum(n, k - 1, 0) == 0);
            assert(!(d >= k));
            assert(!(d >= n / k) || n / k <= 0);
            assert(n / k >= 1) by (nonlinear_arith)
                requires n >= 1, k >= 1, k * k <= n;
        } else {
            Self::lemma_covered_delta(n, k, d - 1);
            let term_k: int = if n % d == 0 && (d <= k || n / d <= k) { d } else { 0 };
            let term_km1: int = if n % d == 0 && (d <= k - 1 || n / d <= k - 1) { d } else { 0 };
            assert(Self::total_covered_sum(n, k, d) == term_k + Self::total_covered_sum(n, k, d - 1));
            assert(Self::total_covered_sum(n, k - 1, d) == term_km1 + Self::total_covered_sum(n, k - 1, d - 1));

            if d < k {
                assert(d <= k - 1);
                assert(term_k == term_km1);
                assert(!(d >= k));
                assert(d < n / k) by (nonlinear_arith)
                    requires n >= 1, k >= 1, k * k <= n, d < k;
                assert(!(d >= n / k));
            } else if d == k {
                assert(n / k >= k) by (nonlinear_arith)
                    requires n >= 1, k >= 1, k * k <= n;
                assert(!(d <= k - 1));
                assert(!(n / d <= k - 1)) by (nonlinear_arith)
                    requires n / k >= k, d == k;
                assert(term_km1 == 0);
                assert(d <= k);
                assert(term_k == (if n % d == 0 { d } else { 0 }));
            } else {
                assert(d > k);
                assert(!(d <= k));
                assert(!(d <= k - 1));
                assert(n == d * (n / d) + n % d) by (nonlinear_arith)
                    requires d >= 1;
                assert(n == k * (n / k) + n % k) by (nonlinear_arith)
                    requires k >= 1;
                if n % d == 0 && n / d == k {
                    assert(n == d * k);
                    assert(n % k == 0) by (nonlinear_arith)
                        requires n == d * k, k >= 1;
                    assert(n / k == d) by (nonlinear_arith)
                        requires n == d * k, k >= 1;
                    assert(term_k == d);
                    assert(!(n / d <= k - 1));
                    assert(term_km1 == 0);
                    assert(k != n / k);
                } else {
                    if n % d != 0 {
                        assert(term_k == 0);
                        assert(term_km1 == 0);
                    } else {
                        assert(n / d != k);
                        if n / d <= k - 1 {
                            assert(term_k == d);
                            assert(term_km1 == d);
                        } else {
                            assert(n / d > k);
                            assert(!(n / d <= k));
                            assert(!(n / d <= k - 1));
                            assert(term_k == 0);
                            assert(term_km1 == 0);
                        }
                    }
                    if n % k == 0 && k != n / k && d == n / k {
                        assert(n == k * d);
                        assert(n % d == 0) by (nonlinear_arith)
                            requires n == k * d, d >= 1;
                        assert(n / d == k) by (nonlinear_arith)
                            requires n == k * d, d >= 1;
                        assert(false);
                    }
                }
            }
        }
    }

    proof fn lemma_paired_eq_total_covered(n: int, k: int)
        requires
            n >= 1,
            k >= 0,
            k * k <= n,
        ensures
            Self::paired_sum_upto(n, k) == Self::total_covered_sum(n, k, n),
        decreases k,
    {
        if k <= 0 {
            assert(k == 0);
            Self::lemma_total_covered_zero(n, n);
            assert(Self::paired_sum_upto(n, 0) == 0);
        } else {
            assert((k - 1) * (k - 1) <= n) by (nonlinear_arith)
                requires k * k <= n, k >= 1;
            Self::lemma_paired_eq_total_covered(n, k - 1);
            Self::lemma_covered_delta(n, k, n);
            assert(n >= k) by (nonlinear_arith)
                requires k * k <= n, k >= 1;
            assert(n / k <= n) by (nonlinear_arith)
                requires n >= 1, k >= 1;
            assert(Self::total_covered_sum(n, k, n) == Self::total_covered_sum(n, k - 1, n)
                + (if n >= k && n % k == 0 { k } else { 0 })
                + (if k != n / k && n % k == 0 && n >= n / k { n / k } else { 0 }));
            assert(Self::paired_sum_upto(n, k) == (if n % k == 0 { (if k != n / k { k + n / k } else { k }) } else { 0 })
                + Self::paired_sum_upto(n, k - 1));
        }
    }

    proof fn lemma_all_divisors_covered(n: int, k: int, d: int)
        requires
            n >= 1,
            k >= 1,
            k * k <= n,
            n < (k + 1) * (k + 1),
            1 <= d <= n,
        ensures
            n % d == 0 ==> (d <= k || n / d <= k),
    {
        if n % d == 0 {
            if d > k && n / d > k {
                assert(d >= k + 1);
                assert(n / d >= k + 1);
                assert(n == d * (n / d) + n % d) by (nonlinear_arith)
                    requires d >= 1;
                assert(n >= (k + 1) * (k + 1)) by (nonlinear_arith)
                    requires
                        d >= k + 1,
                        n / d >= k + 1,
                        n == d * (n / d),
                        k >= 1;
                assert(false);
            }
        }
    }

    proof fn lemma_total_covered_eq_sigma(n: int, k: int, d: int)
        requires
            n >= 1,
            k >= 1,
            k * k <= n,
            n < (k + 1) * (k + 1),
            0 <= d <= n,
        ensures
            d < n ==> Self::total_covered_sum(n, k, d) == Self::sum_divisors_up_to(n, d),
            d == n ==> Self::total_covered_sum(n, k, d) == n + Self::sum_divisors_up_to(n, n - 1),
        decreases d,
    {
        if d <= 0 {
            assert(d == 0);
            assert(Self::total_covered_sum(n, k, 0) == 0);
            assert(Self::sum_divisors_up_to(n, 0) == 0);
        } else if d < n {
            Self::lemma_total_covered_eq_sigma(n, k, d - 1);
            Self::lemma_all_divisors_covered(n, k, d);
            let term = if n % d == 0 && (d <= k || n / d <= k) { d } else { 0 };
            assert(Self::total_covered_sum(n, k, d) == term + Self::total_covered_sum(n, k, d - 1));
            if n % d == 0 {
                assert(d <= k || n / d <= k);
                assert(term == d);
                assert(Self::is_divisor(n, d));
                assert(Self::sum_divisors_up_to(n, d) == d + Self::sum_divisors_up_to(n, d - 1));
            } else {
                assert(term == 0);
                assert(!Self::is_divisor(n, d));
                assert(Self::sum_divisors_up_to(n, d) == Self::sum_divisors_up_to(n, d - 1));
            }
        } else {
            assert(d == n);
            Self::lemma_total_covered_eq_sigma(n, k, n - 1);
            let term = if n % n == 0 && (n <= k || n / n <= k) { n } else { 0 };
            assert(n % n == 0) by (nonlinear_arith)
                requires n >= 1;
            assert(n / n == 1) by (nonlinear_arith)
                requires n >= 1;
            assert(n / n <= k);
            assert(term == n);
            assert(Self::total_covered_sum(n, k, n) == n + Self::total_covered_sum(n, k, n - 1));
        }
    }

    proof fn lemma_paired_eq_sigma(n: int, k: int)
        requires
            n >= 1,
            k >= 1,
            k * k <= n,
            n < (k + 1) * (k + 1),
        ensures
            Self::paired_sum_upto(n, k) == n + Self::sum_divisors_up_to(n, n - 1),
    {
        Self::lemma_paired_eq_total_covered(n, k);
        Self::lemma_total_covered_eq_sigma(n, k, n);
    }

    proof fn lemma_paired_sum_bound(n: int, k: int)
        requires
            n >= 1,
            k >= 0,
        ensures
            0 <= Self::paired_sum_upto(n, k) <= 2 * n * k,
        decreases k,
    {
        if k > 0 {
            Self::lemma_paired_sum_bound(n, k - 1);
            if n % k == 0 {
                assert(n == k * (n / k) + n % k) by (nonlinear_arith)
                    requires k >= 1;
                assert(n / k >= 1) by (nonlinear_arith)
                    requires n == k * (n / k), n >= 1, k >= 1;
                assert(k <= n) by (nonlinear_arith)
                    requires n == k * (n / k), n / k >= 1, k >= 1;
                assert(n / k <= n) by (nonlinear_arith)
                    requires n >= 1, k >= 1;
                assert(Self::paired_sum_upto(n, k) <= 2 * n * k) by (nonlinear_arith)
                    requires
                        Self::paired_sum_upto(n, k) == (if k != n / k { k + n / k } else { k }) + Self::paired_sum_upto(n, k - 1),
                        k <= n,
                        n / k <= n,
                        n >= 1,
                        k >= 1,
                        Self::paired_sum_upto(n, k - 1) <= 2 * n * (k - 1);
            } else {
                assert(Self::paired_sum_upto(n, k) == Self::paired_sum_upto(n, k - 1));
                assert(Self::paired_sum_upto(n, k) <= 2 * n * k) by (nonlinear_arith)
                    requires
                        Self::paired_sum_upto(n, k) == Self::paired_sum_upto(n, k - 1),
                        Self::paired_sum_upto(n, k - 1) <= 2 * n * (k - 1),
                        n >= 1;
            }
        }
    }

    pub fn get_sum(n: i32) -> (res: i64)
        requires
            1 <= n <= 100_000_000,
        ensures
            res == Self::sum_divisors_up_to(n as int, n - 1),
    {
        let nn: i64 = n as i64;
        let mut sum: i64 = 0;
        let mut i: i64 = 1;
        proof {
            assert(Self::paired_sum_upto(n as int, 0) == 0);
        }
        while i * i <= nn
            invariant
                i >= 1,
                i <= 100_000_001,
                i * i <= 10_000_000_400_000_001,
                nn == n as i64,
                1 <= n <= 100_000_000,
                (i - 1) * (i - 1) <= nn,
                sum as int == Self::paired_sum_upto(n as int, (i - 1) as int),
                0 <= sum <= 2 * (n as i64) * (i - 1),
            decreases 100_000_002 - i,
        {
            proof {
                Self::lemma_paired_sum_bound(n as int, i as int);
                assert(i * i <= nn);
                assert(i <= nn) by (nonlinear_arith)
                    requires i >= 1, i * i <= nn;
            }
            if nn % i == 0 {
                let comp: i64 = nn / i;
                proof {
                    assert(i * comp + nn % i == nn) by (nonlinear_arith)
                        requires i >= 1, comp == nn / i;
                    assert(comp <= nn) by (nonlinear_arith)
                        requires n as i64 == nn, nn >= 1, i >= 1, comp == nn / i;
                    assert(2 * nn * (i - 1) <= 2 * nn * nn) by (nonlinear_arith)
                        requires
                            i <= nn,
                            nn >= 1;
                    assert(sum <= 2 * nn * nn);
                    assert(2 * nn * nn <= 20_000_000_000_000_000) by (nonlinear_arith)
                        requires nn <= 100_000_000, nn >= 1;
                    assert(sum <= 20_000_000_000_000_000i64);
                    assert(sum + i <= 20_000_000_100_000_000i64) by (nonlinear_arith)
                        requires
                            sum <= 20_000_000_000_000_000i64,
                            i <= nn,
                            nn <= 100_000_000;
                }
                sum = sum + i;
                proof {
                    assert(2 * nn * nn <= 20_000_000_000_000_000) by (nonlinear_arith)
                        requires nn <= 100_000_000, nn >= 1;
                    assert(sum <= 20_000_000_100_000_000i64);
                    assert(sum + comp <= 20_000_000_200_000_000i64) by (nonlinear_arith)
                        requires
                            sum <= 20_000_000_100_000_000i64,
                            comp <= nn,
                            nn <= 100_000_000;
                }
                if i != comp {
                    sum = sum + comp;
                }
                proof {
                    assert(Self::paired_sum_upto(n as int, i as int)
                        == (if i as int != nn as int / i as int { i as int + comp as int } else { i as int })
                            + Self::paired_sum_upto(n as int, (i - 1) as int));
                }
            } else {
                proof {
                    assert(Self::paired_sum_upto(n as int, i as int)
                        == Self::paired_sum_upto(n as int, (i - 1) as int));
                }
            }
            i = i + 1;
            proof {
                assert(i <= 100_000_001) by (nonlinear_arith)
                    requires (i - 1) * (i - 1) <= nn, nn <= 100_000_000, i >= 1;
                assert(i * i <= 10_000_000_400_000_001) by (nonlinear_arith)
                    requires i <= 100_000_001, i >= 1;
            }
        }
        proof {
            assert(!(i * i <= nn));
            assert((i - 1) * (i - 1) <= n as int);
            assert(n < i * i) by (nonlinear_arith)
                requires nn == n as i64, !(i * i <= nn);
            assert(i >= 2) by (nonlinear_arith)
                requires i >= 1, n < i * i, n >= 1;
            Self::lemma_paired_eq_sigma(n as int, (i - 1) as int);
        }
        sum - nn
    }

    pub fn check_perfect_number(num: i32) -> (res: bool)
        requires
            1 <= num <= 100_000_000,
        ensures
            res == (num == Self::sum_divisors_up_to(num as int, num - 1))
    {
        if (num as i64) == Self::get_sum(num) {
            true
        }
        else {
            false
        }
    }

}

}
