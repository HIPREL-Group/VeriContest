use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_pair(a: int, b: int, num: int) -> bool {
    a >= 1 && b >= 1 && (a * b == num + 1 || a * b == num + 2)
}

pub open spec fn pair_diff(a: int, b: int) -> int {
    b - a
}

pub open spec fn no_div(n1: int, n2: int, j: int) -> bool {
    n1 % j != 0 && n2 % j != 0
}

proof fn div_exact(n: int, d: int)
    requires d >= 1, n >= 1, n % d == 0,
    ensures d * (n / d) == n,
{
    assert(d * (n / d) == n) by(nonlinear_arith)
        requires d >= 1, n >= 1, n % d == 0,
    {}
}

proof fn product_div(a: int, b: int, n: int)
    requires a >= 1, b >= 1, a * b == n,
    ensures n % a == 0, n / a == b,
{
    assert(n % a == 0 && n / a == b) by(nonlinear_arith)
        requires a >= 1, b >= 1, a * b == n,
    {}
}

proof fn gap_mono(n: int, d1: int, d2: int)
    requires
        1 <= d1 < d2,
        d1 * (n / d1) == n,
        d2 * (n / d2) == n,
        n > 0,
    ensures
        n / d2 - d2 < n / d1 - d1,
{
    let q1 = n / d1;
    let q2 = n / d2;
    assert(q2 >= 1) by(nonlinear_arith)
        requires d2 >= 1, d2 * q2 == n, n > 0,
    {}
    assert(q1 > q2) by(nonlinear_arith)
        requires d1 * q1 == d2 * q2, 1 <= d1 < d2, q2 >= 1,
    {}
    assert(q1 - d1 > q2 - d2) by(nonlinear_arith)
        requires q1 > q2, d1 < d2,
    {}
}

proof fn div_sq_ok(n: int, gi: int)
    requires
        gi >= 1, n >= 1,
        n % gi == 0,
        gi * gi <= n + 1,
    ensures
        n / gi >= gi,
{
    div_exact(n, gi);
    let q = n / gi;
    if gi == 1 {
        assert(q >= 1) by(nonlinear_arith)
            requires gi == 1, gi * q == n, n >= 1,
        {}
    } else {
        if q < gi {
            assert(gi * q < gi * gi) by(nonlinear_arith)
                requires gi >= 2, q >= 0, q < gi,
            {}
            assert(gi * q >= gi * gi - 1) by(nonlinear_arith)
                requires gi * q == n, n + 1 >= gi * gi,
            {}
            assert(gi * q == gi * gi - 1) by(nonlinear_arith)
                requires gi * q < gi * gi, gi * q >= gi * gi - 1,
            {}
            assert(false) by(nonlinear_arith)
                requires gi >= 2, gi * q == gi * gi - 1,
            {}
        }
    }
}

proof fn same_number_opt(n: int, gi: int, a: int, b: int)
    requires
        1 <= a < gi, a <= b, a * b == n,
        n >= 2, n % gi == 0, gi * gi <= n,
    ensures
        n / gi - gi < b - a,
{
    div_exact(n, gi);
    product_div(a, b, n);
    gap_mono(n, a, gi);
}

proof fn cross_opt(n_ours: int, n_theirs: int, gi: int, a: int, b: int)
    requires
        1 <= a < gi, a * b == n_theirs, b >= a,
        n_ours % gi == 0,
        gi * gi <= n_ours + 1,
        n_ours >= 2, n_theirs >= 2,
        n_theirs >= n_ours - 1,
        n_theirs <= n_ours + 1,
    ensures
        n_ours / gi - gi <= b - a,
{
    product_div(a, b, n_theirs);
    div_exact(n_ours, gi);
    div_sq_ok(n_ours, gi);

    assert(n_theirs / a >= (n_ours - 1) / a) by(nonlinear_arith)
        requires a >= 1, n_theirs >= n_ours - 1, n_ours >= 2,
    {}

    assert((n_ours - 1) / a >= n_ours / a - 1) by(nonlinear_arith)
        requires a >= 1, n_ours >= 2,
    {}

    assert(n_ours / a >= n_ours / gi) by(nonlinear_arith)
        requires 1 <= a < gi, n_ours >= 2,
    {}

    assert(n_theirs / a >= n_ours / gi - 1) by(nonlinear_arith)
        requires
            n_theirs / a >= (n_ours - 1) / a,
            (n_ours - 1) / a >= n_ours / a - 1,
            n_ours / a >= n_ours / gi,
    {}

    assert(b - a >= n_ours / gi - gi) by(nonlinear_arith)
        requires
            b == n_theirs / a,
            n_theirs / a >= n_ours / gi - 1,
            gi - a >= 1,
    {}
}

impl Solution {
    pub fn closest_divisors(num: i32) -> (res: Vec<i32>)
        requires
            1 <= num <= 1_000_000_000,
        ensures
            res.len() == 2,
            1 <= res[0] <= res[1],
            is_valid_pair(res[0] as int, res[1] as int, num as int),
            forall|a: int, b: int|
                1 <= a <= b && (a * b == (num as int) + 1 || a * b == (num as int) + 2) ==>
                    res[1] as int - res[0] as int <= #[trigger] pair_diff(a, b),
    {
        let mut i: i32 = 2;
        while i * i <= num + 2
            invariant
                2 <= i <= 31625,
                1 <= num <= 1_000_000_000,
                (i as int - 1) * (i as int - 1) <= (num as int) + 2,
                (i as int) * (i as int) <= (num as int) + 2 * (i as int) + 1,
            decreases 31625 - i,
        {
            proof {
                let gi = i as int;
                assert(gi * gi <= (num as int) + 2);
                assert(gi <= 31624) by(nonlinear_arith)
                    requires gi * gi <= (num as int) + 2, (num as int) <= 1_000_000_000,
                {}
                assert((gi + 1) * (gi + 1) <= (num as int) + 2 * (gi + 1) + 1) by(nonlinear_arith)
                    requires gi * gi <= (num as int) + 2,
                {}
            }
            i += 1;
        }
        i -= 1;

        let ghost gn: int = num as int;
        let ghost gn1: int = gn + 1;
        let ghost gn2: int = gn + 2;
        let ghost sv: int = i as int;

        proof {
            assert(sv >= 1);
            assert(sv * sv <= gn2);
            assert((sv + 1) * (sv + 1) > gn2);
        }

        let mut best_a: i32 = 1;
        let mut best_b: i32 = num + 1;
        let mut found = false;

        while i >= 1 && !found
            invariant
                1 <= num <= 1_000_000_000,
                0 <= i <= sv,
                (i as int) * (i as int) <= gn2,
                sv >= 1,
                sv * sv <= gn2,
                (sv + 1) * (sv + 1) > gn2,
                gn == num as int,
                gn1 == gn + 1,
                gn2 == gn + 2,
                !found ==> (best_a == 1 && best_b == num + 1),
                !found ==> i >= 1,
                found ==> (
                    1 <= best_a <= best_b
                    && ((best_a as int) * (best_b as int) == gn1
                        || (best_a as int) * (best_b as int) == gn2)
                ),
                found ==> forall|a: int, b: int|
                    1 <= a <= b && (a * b == gn1 || a * b == gn2) ==>
                        best_b as int - best_a as int <= #[trigger] pair_diff(a, b),
                !found ==> forall|j: int|
                    j > i && j <= sv ==>
                        #[trigger] no_div(gn1, gn2, j),
            decreases if found { 0int } else { i as int + 1 },
        {
            let n1 = num + 1;
            let n2 = num + 2;

            if n1 % i == 0 {
                best_a = i;
                best_b = n1 / i;

                proof {
                    let gi = i as int;
                    div_exact(gn1, gi);
                    assert(gi * gi <= gn2);
                    div_sq_ok(gn1, gi);

                    assert forall|a: int, b: int|
                        1 <= a <= b && (a * b == gn1 || a * b == gn2)
                    implies
                        best_b as int - best_a as int <= #[trigger] pair_diff(a, b)
                    by {
                        if a == gi {
                            if a * b == gn1 {
                                product_div(a, b, gn1);
                            } else {
                                product_div(a, b, gn2);
                                assert(b >= best_b as int) by(nonlinear_arith)
                                    requires a * b == gn2, a * (best_b as int) == gn1, gn2 > gn1, a >= 1,
                                {}
                            }
                        } else if a > gi {
                            let nv: int = if a * b == gn1 { gn1 } else { gn2 };
                            assert(a * a <= nv) by(nonlinear_arith)
                                requires a >= 1, b >= a, a * b == nv,
                            {}
                            assert(a * a <= gn2) by(nonlinear_arith)
                                requires a * a <= nv, nv <= gn2,
                            {}
                            assert(a <= sv) by(nonlinear_arith)
                                requires a >= 1, a * a <= gn2, (sv + 1) * (sv + 1) > gn2, sv >= 1,
                            {}
                            product_div(a, b, nv);
                            assert(no_div(gn1, gn2, a));
                            assert(nv % a == 0);
                            assert(false);
                        } else {
                            if a * b == gn1 {
                                div_sq_ok(gn1, gi);
                                assert(gi * gi <= gn1) by(nonlinear_arith)
                                    requires gi >= 1, gn1 / gi >= gi, gi * (gn1 / gi) == gn1,
                                {}
                                same_number_opt(gn1, gi, a, b);
                            } else {
                                cross_opt(gn1, gn2, gi, a, b);
                            }
                        }
                    }
                }

                found = true;
            } else if n2 % i == 0 {
                best_a = i;
                best_b = n2 / i;

                proof {
                    let gi = i as int;
                    div_exact(gn2, gi);
                    assert(gi * gi <= gn2);

                    assert(best_b as int >= gi) by(nonlinear_arith)
                        requires gi >= 1, gi * (best_b as int) == gn2, gi * gi <= gn2,
                    {}

                    assert(gn1 % gi != 0);

                    assert forall|a: int, b: int|
                        1 <= a <= b && (a * b == gn1 || a * b == gn2)
                    implies
                        best_b as int - best_a as int <= #[trigger] pair_diff(a, b)
                    by {
                        if a == gi {
                            if a * b == gn2 {
                                product_div(a, b, gn2);
                            } else {
                                product_div(a, b, gn1);
                                assert(gn1 % gi == 0);
                                assert(false);
                            }
                        } else if a > gi {
                            let nv: int = if a * b == gn1 { gn1 } else { gn2 };
                            assert(a * a <= nv) by(nonlinear_arith)
                                requires a >= 1, b >= a, a * b == nv,
                            {}
                            assert(a * a <= gn2) by(nonlinear_arith)
                                requires a * a <= nv, nv <= gn2,
                            {}
                            assert(a <= sv) by(nonlinear_arith)
                                requires a >= 1, a * a <= gn2, (sv + 1) * (sv + 1) > gn2, sv >= 1,
                            {}
                            product_div(a, b, nv);
                            assert(no_div(gn1, gn2, a));
                            assert(nv % a == 0);
                            assert(false);
                        } else {
                            if a * b == gn2 {
                                same_number_opt(gn2, gi, a, b);
                            } else {
                                cross_opt(gn2, gn1, gi, a, b);
                            }
                        }
                    }
                }

                found = true;
            }

            if !found {
                proof {
                    let gi = i as int;
                    assert(no_div(gn1, gn2, gi));
                    assert(gn1 % 1 == 0) by(nonlinear_arith)
                        requires gn1 >= 2,
                    {}
                    assert(gi != 1);
                    assert((gi - 1) * (gi - 1) <= gn2) by(nonlinear_arith)
                        requires gi * gi <= gn2, gi >= 2,
                    {}
                }
                i -= 1;
            }
        }

        proof {
            assert(found);
        }

        vec![best_a, best_b]
    }
}

}
