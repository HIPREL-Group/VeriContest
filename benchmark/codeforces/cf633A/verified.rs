use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::arithmetic::mul::lemma_mul_is_commutative;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn exact_damage_feasible(a: int, b: int, c: int) -> bool {
    exists|x: int, y: int| x >= 0 && y >= 0 && #[trigger] (a * x + b * y) == c
}

impl Solution {
    pub fn exact_damage_possible(a: i32, b: i32, c: i32) -> (res: bool)
        requires
            1 <= a <= 100,
            1 <= b <= 100,
            1 <= c <= 10_000,
        ensures
            res == exact_damage_feasible(a as int, b as int, c as int),
    {
        let mut x: i32 = 0;
        #[verifier::loop_isolation(false)]
        while x <= c
            invariant
                1 <= a <= 100,
                1 <= b <= 100,
                1 <= c <= 10_000,
                x >= 0,
                x <= c + 1,
                forall|x2: int| 0 <= x2 < (x as int) ==> #[trigger] ((c as int - a as int * x2) % (b as int)) != 0,
            decreases c + 1 - x,
        {
            if x > c / a {
                proof {
                    assert(x > c / a);
                }
                break;
            }
            proof {
                lemma_x_leq_c_div_implies_xa_leq_c(x as int, a as int, c as int);
            }
            let rem = c - x * a;
            if rem % b == 0 {
                proof {
                    let xi = x as int;
                    let ai = a as int;
                    let bi = b as int;
                    let ci = c as int;
                    let ri = ci - ai * xi;
                    assert(ri == rem as int);
                    lemma_fundamental_div_mod(ri, bi);
                    assert(ri == bi * (ri / bi) + (ri % bi));
                    assert(ri % bi == 0);
                    assert(ri == bi * (ri / bi));
                    let yy = ri / bi;
                    assert(yy >= 0);
                    assert(ai * xi + bi * yy == ci);
                    assert(exact_damage_feasible(ai, bi, ci));
                }
                return true;
            }
            let ox = x;
            x = x + 1;
            proof {
                lemma_x_leq_c_div_implies_xa_leq_c(ox as int, a as int, c as int);
                assert(x == ox + 1);
                assert(x <= c + 1);
            }
        }
        proof {
            let xi = x as int;
            let ai = a as int;
            let bi = b as int;
            let ci = c as int;
            assert(xi <= ci + 1);
            if xi <= ci {
                assert(xi > ci / ai);
                lemma_x_gt_c_div_implies_xa_gt_c(xi, ai, ci);
            } else {
                assert(xi == ci + 1);
                lemma_succ_times_a_gt_c(ci, ai);
            }
            assert(xi * ai > ci);
            assert(forall|x2: int| 0 <= x2 < xi ==> #[trigger] ((ci - ai * x2) % bi) != 0);
            lemma_no_solution_after_checks(ai, bi, ci, xi);
        }
        false
    }
}

proof fn lemma_x_leq_c_div_implies_xa_leq_c(x: int, a: int, c: int)
    requires
        a >= 1,
        c >= 0,
        0 <= x <= c / a,
    ensures
        x * a <= c,
{
    let q = c / a;
    lemma_fundamental_div_mod(c, a);
    assert(c == a * q + (c % a));
    assert(0 <= (c % a) < a);
    assert(x <= q);
    assert(x * a <= q * a) by (nonlinear_arith)
        requires
            x <= q,
            a >= 0,
    {
    }
    assert(q * a <= c) by (nonlinear_arith)
        requires
            c == a * q + (c % a),
            (c % a) >= 0,
    {
    }
    assert(x * a <= c);
}

proof fn lemma_succ_times_a_gt_c(c: int, a: int)
    requires
        a >= 1,
        c >= 1,
    ensures
        (c + 1) * a > c,
{
    assert((c + 1) * a == c * a + a) by (nonlinear_arith)
        requires
            true,
    {
    }
    assert(c * a + a > c) by (nonlinear_arith)
        requires
            c >= 1,
            a >= 1,
    {
    }
}

proof fn lemma_x_gt_c_div_implies_xa_gt_c(x: int, a: int, c: int)
    requires
        a >= 1,
        c >= 0,
        x > c / a,
        x <= c,
    ensures
        x * a > c,
{
    let q = c / a;
    lemma_fundamental_div_mod(c, a);
    assert(c == a * q + (c % a));
    assert(0 <= (c % a) < a);
    assert(x >= q + 1);
    assert(x * a >= (q + 1) * a) by (nonlinear_arith)
        requires
            x >= q + 1,
            a >= 0,
    {
    }
    assert((q + 1) * a == a * q + a) by (nonlinear_arith)
        requires
            true,
    {
    }
    assert(a * q + a > a * q + (c % a)) by (nonlinear_arith)
        requires
            (c % a) < a,
            a >= 1,
    {
    }
    assert((q + 1) * a > c);
    assert(x * a > c);
}

proof fn lemma_no_solution_after_checks(a: int, b: int, c: int, x: int)
    requires
        1 <= a,
        1 <= b,
        x >= 0,
        x * a > c,
        forall|x2: int| 0 <= x2 < x ==> #[trigger] ((c - a * x2) % b) != 0,
    ensures
        !exact_damage_feasible(a, b, c),
{
    assert forall|x2: int, y: int|
        x2 >= 0 && y >= 0 && #[trigger] (a * x2 + b * y) == c implies false by {
        if x2 >= 0 && y >= 0 && a * x2 + b * y == c {
            assert(a * x2 + b * y == c);
            assert(b * y >= 0);
            assert(a * x2 <= c);
            assert(x2 * a <= c);
            assert(x2 < x) by (nonlinear_arith)
                requires
                    x2 * a <= c,
                    x * a > c,
                    a >= 1,
            {
            }
            assert(0 <= x2 < x);
            assert((c - a * x2) % b == 0) by {
                assert(c - a * x2 == b * y);
                lemma_mod_multiples_basic(y, b);
                assert((y * b) % b == 0);
                assert(b * y == y * b) by {
                    lemma_mul_is_commutative(b, y);
                }
                assert((b * y) % b == 0);
            }
            assert(false);
        }
    }
}

}
