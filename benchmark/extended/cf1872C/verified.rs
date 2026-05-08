use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_adds,
    lemma_mod_multiples_basic,
};
use vstd::arithmetic::mul::{lemma_mul_is_associative, lemma_mul_is_commutative};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_has_common_divisor_ge_2(a: int, b: int) -> bool {
        exists|d: int|
            #![trigger a % d]
            2 <= d && a % d == 0 && b % d == 0
    }

    pub open spec fn spec_is_composite_ge_4(s: int) -> bool {
        s >= 4 && exists|d: int|
            #![trigger s % d]
            2 <= d < s && s % d == 0
    }

    proof fn lemma_i32_nonneg_mod2(s: i32)
        requires
            0 <= s,
        ensures
            (s as int) % 2 == (s % 2) as int,
    {
        assert((s % 2 == 0) == ((s as int) % 2 == 0));
    }

    proof fn lemma_small_s_not_composite(s: i32)
        requires
            (s as int) < 4,
        ensures
            !Self::spec_is_composite_ge_4(s as int),
    {
        assert((s as int) < 4);
        assert(!Self::spec_is_composite_ge_4(s as int));
    }

    proof fn lemma_even_split_ok(li: int, ri: int, s: i32)
        requires
            1 <= li <= ri <= 10_000_000,
            li <= (s as int) <= ri,
            (s as int) >= 4,
            s % 2 == 0,
        ensures
            1 <= ((s - 2) as int),
            li <= (s as int) <= ri,
            Self::spec_has_common_divisor_ge_2(2, (s - 2) as int),
    {
        assert(0 <= s);
        Self::lemma_i32_nonneg_mod2(s);
        assert((s as int) % 2 == 0);
        assert((s as int) >= 4);
        assert(((s - 2) as int) >= 2);
        assert(li <= (s as int) <= ri);
        assert(((s - 2) as int) % 2 == 0) by (nonlinear_arith)
            requires
                (s as int) % 2 == 0;
        assert(2 <= 2);
        assert((2 as int) % 2 == 0);
        assert(((s - 2) as int) % 2 == 0);
        assert(Self::spec_has_common_divisor_ge_2(2, (s - 2) as int));
    }

    proof fn lemma_divides_diff(s: int, d: int)
        requires
            2 <= d < s,
            s % d == 0,
        ensures
            (s - d) % d == 0,
    {
        let q = s / d;
        lemma_fundamental_div_mod(s, d);
        assert(0 < d);
        assert(0 <= s);
        assert(s == q * d + s % d);
        assert(s == q * d);
        assert(s - d == (q - 1) * d) by (nonlinear_arith)
            requires
                s == q * d,
                2 <= d < s;
        broadcast use lemma_mod_multiples_basic;
        assert(((q - 1) * d) % d == 0);
        assert((s - d) % d == 0);
    }

    proof fn lemma_even_divisor_forces_even_dividend(s: int, dd: int)
        requires
            dd >= 2,
            dd % 2 == 0,
            s % dd == 0,
        ensures
            s % 2 == 0,
    {
        let k = s / dd;
        lemma_fundamental_div_mod(s, dd);
        assert(0 < dd);
        assert(s == k * dd);
        lemma_fundamental_div_mod(dd, 2);
        assert(0 < 2);
        assert(dd == 2 * (dd / 2) + dd % 2);
        assert(dd == 2 * (dd / 2));
        let m = dd / 2;
        assert(dd == 2 * m);
        assert(s == k * (2 * m));
        lemma_mul_is_associative(k, 2, m);
        assert(k * (2 * m) == (k * 2) * m);
        assert(s == (k * 2) * m);
        lemma_mul_is_commutative(k, 2);
        assert(k * 2 == 2 * k);
        assert((k * 2) * m == (2 * k) * m);
        lemma_mul_is_associative(2, k, m);
        assert((2 * k) * m == 2 * (k * m));
        assert(s == 2 * (k * m));
        broadcast use lemma_mod_multiples_basic;
        assert((2 * (k * m)) % 2 == 0);
        assert(s % 2 == 0);
    }

    proof fn lemma_odd_split_ok(li: int, ri: int, s: i32, d: i32)
        requires
            1 <= li <= ri <= 10_000_000,
            li <= (s as int) <= ri,
            (s as int) >= 4,
            s % 2 == 1,
            3 <= (d as int),
            (d as int) * (d as int) <= (s as int),
            s % d == 0,
        ensures
            1 <= ((s - d) as int),
            li <= (s as int) <= ri,
            Self::spec_has_common_divisor_ge_2(d as int, (s - d) as int),
    {
        assert((d as int) < (s as int)) by (nonlinear_arith)
            requires
                3 <= (d as int),
                (d as int) * (d as int) <= (s as int),
                (s as int) >= 4;
        assert(2 <= (d as int) < (s as int));
        assert(((s - d) as int) >= 1) by (nonlinear_arith)
            requires
                (d as int) < (s as int);
        assert(li <= (s as int) <= ri);
        Self::lemma_divides_diff(s as int, d as int);
        assert(((s - d) as int) % (d as int) == 0);
        assert(2 <= (d as int));
        assert((d as int) % (d as int) == 0);
        assert(Self::spec_has_common_divisor_ge_2(d as int, (s - d) as int));
    }

    proof fn lemma_d_mul_d_gt_s_from_loop_exit(s: i32, d: i32)
        requires
            0 <= s,
            3 <= d,
            !(d <= s / d),
        ensures
            (d as int) * (d as int) > (s as int),
    {
        assert(d > s / d);
        assert((d as int) > ((s as int) / (d as int)));
        assert((d as int) * (d as int) > (s as int)) by (nonlinear_arith)
            requires
                3 <= d,
                (d as int) > ((s as int) / (d as int)),
                (s as int) >= 0;
    }

    proof fn lemma_dd_cannot_divide_odd(si: int, d: i32, dd: int)
        requires
            si % 2 == 1,
            si >= 5,
            (d as int) >= 3,
            ((d as int) % 2) == 1,
            (d as int) * (d as int) > si,
            forall|k: int|
                #![trigger si % k]
                (3 <= k && k < (d as int) && k % 2 == 1) ==> si % k != 0,
            2 <= dd && dd < si && si % dd == 0,
        ensures
            false,
    {
        if dd % 2 == 0 {
            Self::lemma_even_divisor_forces_even_dividend(si, dd);
            assert(si % 2 == 0);
            assert(false);
        }
        assert(dd >= 3);
        assert(dd % 2 == 1);
        if dd * dd <= si {
            assert(dd < (d as int)) by (nonlinear_arith)
                requires
                    dd * dd <= si,
                    (d as int) * (d as int) > si,
                    (d as int) >= 3,
                    dd >= 3,
                    si >= 5;
            assert(3 <= dd && dd < (d as int) && dd % 2 == 1);
            assert(si % dd != 0);
            assert(false);
        }
        let other = si / dd;
        lemma_fundamental_div_mod(si, dd);
        assert(0 < dd);
        assert(si == other * dd + si % dd);
        assert(si == other * dd);
        assert(other * dd >= 5) by (nonlinear_arith)
            requires
                si == other * dd,
                si >= 5;
        assert(other >= 1) by (nonlinear_arith)
            requires
                other * dd >= 5,
                dd >= 2;
        assert(other < dd) by (nonlinear_arith)
            requires
                si == other * dd,
                dd * dd > si,
                dd >= 2;
        if other % 2 == 0 {
            assert(other >= 2) by (nonlinear_arith)
                requires
                    other >= 1,
                    other % 2 == 0;
            assert(si == other * dd);
            lemma_mul_is_commutative(dd, other);
            assert(si == dd * other);
            assert(0 <= 0 < other);
            lemma_fundamental_div_mod_converse(si, other, dd, 0);
            assert(si % other == 0);
            Self::lemma_even_divisor_forces_even_dividend(si, other);
            assert(si % 2 == 0);
            assert(false);
        }
        if other < 3 {
            assert(other == 1 || other == 2);
            if other == 1 {
                assert(other == 1);
                assert(other == si / dd);
                assert(si / dd == 1);
                assert(si % dd == 0);
                lemma_fundamental_div_mod(si, dd);
                assert(si == (si / dd) * dd + si % dd);
                assert(si == (si / dd) * dd);
                assert((si / dd) * dd == dd) by (nonlinear_arith)
                    requires
                        si / dd == 1;
                assert(si == dd);
                assert(false);
            }
            assert(si == 2 * dd);
            broadcast use lemma_mod_multiples_basic;
            assert((2 * dd) % 2 == 0);
            assert(si % 2 == 0);
            assert(false);
        }
        assert(other * other <= si) by (nonlinear_arith)
            requires
                si == other * dd,
                other < dd,
                dd >= 3,
                si >= 5;
        assert(other < (d as int)) by (nonlinear_arith)
            requires
                other * other <= si,
                (d as int) * (d as int) > si,
                (d as int) >= 3,
                other >= 3,
                si >= 5;
        assert(3 <= other && other < (d as int) && other % 2 == 1);
        assert(si == other * dd);
        lemma_mul_is_commutative(other, dd);
        assert(si == dd * other);
        assert(0 <= 0 < other);
        lemma_fundamental_div_mod_converse(si, other, dd, 0);
        assert(si % other == 0);
        assert(si % other != 0);
        assert(false);
    }

    proof fn lemma_odd_not_composite(si: int, d: i32)
        requires
            si % 2 == 1,
            si >= 5,
            (d as int) >= 3,
            ((d as int) % 2) == 1,
            (d as int) * (d as int) > si,
            forall|k: int|
                #![trigger si % k]
                (3 <= k && k < (d as int) && k % 2 == 1) ==> si % k != 0,
        ensures
            !Self::spec_is_composite_ge_4(si),
    {
        assert(!Self::spec_is_composite_ge_4(si)) by {
            assert forall|dd: int|
                #![trigger si % dd]
                !(2 <= dd < si && si % dd == 0) by {
                if 2 <= dd && dd < si && si % dd == 0 {
                    Self::lemma_dd_cannot_divide_odd(si, d, dd);
                    assert(false);
                }
            };
        };
    }

    proof fn lemma_common_divisor_implies_composite(a: int, b: int, d: int)
        requires
            1 <= a,
            1 <= b,
            2 <= d,
            a % d == 0,
            b % d == 0,
        ensures
            Self::spec_is_composite_ge_4(a + b),
    {
        let s = a + b;
        lemma_fundamental_div_mod(a, d);
        lemma_fundamental_div_mod(b, d);
        assert(0 < d);
        assert(0 <= a);
        assert(0 <= b);
        assert(a == d * (a / d) + a % d);
        assert(a % d == 0);
        assert(a == d * (a / d));
        lemma_mul_is_commutative(d, a / d);
        assert(a == (a / d) * d);
        assert(b == d * (b / d) + b % d);
        assert(b % d == 0);
        assert(b == d * (b / d));
        lemma_mul_is_commutative(d, b / d);
        assert(b == (b / d) * d);
        assert(a / d >= 1) by (nonlinear_arith)
            requires
                1 <= a,
                2 <= d,
                a % d == 0,
                a == (a / d) * d;
        assert(b / d >= 1) by (nonlinear_arith)
            requires
                1 <= b,
                2 <= d,
                b % d == 0,
                b == (b / d) * d;
        assert(a >= d) by (nonlinear_arith)
            requires
                a == (a / d) * d,
                a / d >= 1,
                2 <= d;
        assert(b >= d) by (nonlinear_arith)
            requires
                b == (b / d) * d,
                b / d >= 1,
                2 <= d;
        assert(s >= 2 * d) by (nonlinear_arith)
            requires
                s == a + b,
                a >= d,
                b >= d;
        assert(s >= 4);
        assert(2 <= d < s) by (nonlinear_arith)
            requires
                s >= 2 * d,
                2 <= d,
                1 <= a,
                1 <= b;
        assert(s == a + b);
        lemma_mod_adds(a, b, d);
        assert(a % d + b % d == 0);
        assert(a % d + b % d < d);
        assert(a % d + b % d == (a + b) % d);
        assert((a + b) % d == 0);
        assert(s % d == 0);
        assert(2 <= d < s);
        assert(s % d == 0);
        assert(Self::spec_is_composite_ge_4(s));
    }

    proof fn lemma_no_composite_interval_implies_no_pair(l: i32, r: i32)
        requires
            forall|k: int|
                #![trigger Self::spec_is_composite_ge_4(k)]
                (l as int) <= k <= (r as int) ==> !Self::spec_is_composite_ge_4(k),
        ensures
            forall|a: int, b: int|
                #![auto]
                (1 <= a && 1 <= b && (l as int) <= a + b <= (r as int))
                    ==> !Self::spec_has_common_divisor_ge_2(a, b),
    {
        assert forall|a: int, b: int|
            (1 <= a && 1 <= b && (l as int) <= a + b <= (r as int))
                implies !Self::spec_has_common_divisor_ge_2(a, b) by {
            if 1 <= a && 1 <= b && (l as int) <= a + b <= (r as int) {
                if Self::spec_has_common_divisor_ge_2(a, b) {
                    assert(exists|dd: int|
                        #![trigger a % dd]
                        2 <= dd && a % dd == 0 && b % dd == 0);
                    let d_w = choose|dd: int|
                        #![trigger a % dd]
                        2 <= dd && a % dd == 0 && b % dd == 0;
                    let s = a + b;
                    Self::lemma_common_divisor_implies_composite(a, b, d_w);
                    assert(Self::spec_is_composite_ge_4(s));
                    assert((l as int) <= s <= (r as int));
                    assert(!Self::spec_is_composite_ge_4(s));
                    assert(false);
                }
            }
        };
    }

    proof fn lemma_none_ok(l: i32, r: i32, s_end: i32)
        requires
            s_end == r + 1,
            forall|k: int|
                #![trigger Self::spec_is_composite_ge_4(k)]
                (l as int) <= k < (s_end as int) ==> !Self::spec_is_composite_ge_4(k),
        ensures
            forall|a: int, b: int|
                #![auto]
                (1 <= a && 1 <= b && (l as int) <= a + b <= (r as int))
                    ==> !Self::spec_has_common_divisor_ge_2(a, b),
    {
        assert forall|k: int|
            (l as int) <= k <= (r as int) implies !Self::spec_is_composite_ge_4(k) by {
            if (l as int) <= k && k <= (r as int) {
                assert(k < (s_end as int));
            }
        };
        Self::lemma_no_composite_interval_implies_no_pair(l, r);
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn non_coprime_split(l: i32, r: i32) -> (res: Option<(i32, i32)>)
        requires
            l >= 1,
            l <= r,
            r <= 10_000_000,
            1 <= (l as int) <= (r as int) <= 10_000_000,
        ensures
            res != None::<(i32, i32)> ==> {
                let p = res->Some_0;
                &&& 1 <= (p.0 as int) <= 10_000_000
                &&& 1 <= (p.1 as int) <= 10_000_000
                &&& (l as int) <= (p.0 as int) + (p.1 as int) <= (r as int)
                &&& Self::spec_has_common_divisor_ge_2(p.0 as int, p.1 as int)
            },
            res == None::<(i32, i32)> <==> forall|a: int, b: int|
                (1 <= a && 1 <= b && (l as int) <= a + b <= (r as int))
                    ==> !Self::spec_has_common_divisor_ge_2(a, b),
    {
        let mut s = l;
        while s <= r
            invariant
                1 <= (l as int) <= (r as int) <= 10_000_000,
                (l as int) <= (s as int) <= (r as int) + 1,
                (r as int) <= 10_000_000,
                forall|k: int|
                    #![trigger Self::spec_is_composite_ge_4(k)]
                    (l as int) <= k < (s as int) ==> !Self::spec_is_composite_ge_4(k),
            decreases
                (r as int) - (s as int) + 1,
        {
            if s >= 4 {
                if s % 2 == 0 {
                    proof {
                        Self::lemma_even_split_ok(l as int, r as int, s);
                    }
                    return Some((2, s - 2));
                }
                let ghost si = (s as int);
                let mut d: i32 = 3;
                while d <= s / d
                    invariant
                        1 <= (l as int) <= (r as int) <= 10_000_000,
                        (l as int) <= (s as int) <= (r as int),
                        s % 2 == 1,
                        4 <= (s as int),
                        si == s as int,
                        3 <= (d as int),
                        (d as int) <= 100_000,
                        ((d as int) % 2) == 1,
                        forall|k: int|
                            #![trigger si % k]
                            (3 <= k && k < (d as int) && k % 2 == 1) ==> si % k != 0,
                    decreases
                        100_000 - d,
                {
                    if s % d == 0 {
                        proof {
                            assert((d as int) * (d as int) <= (s as int)) by (nonlinear_arith)
                                requires
                                    d <= s / d,
                                    3 <= d,
                                    (s as int) >= 4;
                            Self::lemma_odd_split_ok(l as int, r as int, s, d);
                        }
                        return Some((d, s - d));
                    }
                    proof {
                        assert(0 <= s);
                        assert((s as int) <= (r as int));
                        assert((r as int) <= 10_000_000);
                        assert((s as int) <= 10_000_000);
                        Self::lemma_i32_nonneg_mod2(s);
                        assert((s as int) % 2 == 1);
                        assert((d as int) % 2 == 1);
                        assert((s as int) % (d as int) != 0);
                        assert((d as int) <= 4000) by (nonlinear_arith)
                            requires
                                (d as int) <= (s as int) / (d as int),
                                3 <= (d as int),
                                (s as int) <= 10_000_000;
                        assert((d as int) + 2 <= 100_000);
                    }
                    d = d + 2;
                }
                proof {
                    assert(si == s as int);
                    assert(0 <= s);
                    assert(!(d <= s / d));
                    Self::lemma_d_mul_d_gt_s_from_loop_exit(s, d);
                    Self::lemma_odd_not_composite(si, d);
                }
            } else {
                proof {
                    Self::lemma_small_s_not_composite(s);
                }
            }
            proof {
                assert(!Self::spec_is_composite_ge_4(s as int));
                assert((s as int) <= (r as int));
                assert((s as int) + 1 <= 10_000_001);
            }
            s = s + 1;
        }
        proof {
            assert(s == r + 1);
            Self::lemma_none_ok(l, r, s);
        }
        None
    }
}

}
