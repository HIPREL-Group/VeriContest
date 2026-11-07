use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_remainder};
use vstd::arithmetic::mul::{
    lemma_mul_is_commutative, lemma_mul_is_distributive_add, lemma_mul_inequality,
    lemma_mul_upper_bound,
};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_int(a: int, b: int) -> int {
        if a <= b {
            a
        } else {
            b
        }
    }

    pub open spec fn can_pay_exact(a: int, b: int, n: int, S: int) -> bool {
        exists|x: int, y: int|
            0 <= x <= a && 0 <= y <= b && #[trigger] (x * n + y) == S
    }

    pub open spec fn greedy_x(a: int, n: int, S: int) -> int {
        Self::min_int(a, S / n)
    }

    pub open spec fn greedy_remainder(a: int, n: int, S: int) -> int {
        S - Self::greedy_x(a, n, S) * n
    }

    proof fn lemma_x0_le_sn(x0: int, n: int, S: int)
        requires
            1 <= n,
            0 <= x0,
            x0 * n <= S,
        ensures
            x0 <= S / n,
    {
        let q = S / n;
        let r = S % n;
        lemma_fundamental_div_mod(S, n);
        lemma_remainder(S, n);
        assert(S == n * q + r);
        lemma_mul_is_commutative(n, q);
        assert(S == q * n + r);
        assert(0 <= r < n);
        if x0 > q {
            assert(x0 >= q + 1);
            lemma_mul_inequality(q + 1, x0, n);
            assert((q + 1) * n <= x0 * n);
            lemma_mul_is_distributive_add(n, q, 1);
            assert(n * (q + 1) == n * q + n);
            lemma_mul_is_commutative(n, q + 1);
            lemma_mul_is_commutative(n, q);
            assert((q + 1) * n == q * n + n);
            assert(n > r);
            assert(q * n + n > q * n + r);
            assert(q * n + n > S);
            assert(x0 * n > S);
            assert(false);
        } else {
            assert(x0 <= q);
        }
    }

    proof fn lemma_sound(a: int, b: int, n: int, S: int)
        requires
            1 <= a,
            1 <= b,
            1 <= n,
            1 <= S,
            Self::greedy_remainder(a, n, S) <= b,
        ensures
            Self::can_pay_exact(a, b, n, S),
    {
        let xg = Self::greedy_x(a, n, S);
        let r = Self::greedy_remainder(a, n, S);
        assert(r == S - xg * n);
        assert(xg * n + r == S);
        lemma_remainder(S, n);
        assert((S / n) * n <= S);
        assert(xg <= S / n);
        assert(xg <= a);
        lemma_mul_inequality(xg, S / n, n);
        assert(xg * n <= (S / n) * n);
        assert(xg * n <= S);
        assert(0 <= r);
        assert(0 <= xg && xg <= a);
        assert(0 <= r && r <= b);
        assert(Self::can_pay_exact(a, b, n, S));
    }

    proof fn lemma_x0_le_greedy(a: int, n: int, S: int, x0: int, y0: int)
        requires
            1 <= a,
            1 <= n,
            1 <= S,
            0 <= x0 <= a,
            0 <= y0,
            x0 * n + y0 == S,
        ensures
            x0 <= Self::greedy_x(a, n, S),
    {
        assert(x0 * n + y0 == S);
        assert(y0 >= 0);
        assert(x0 * n <= S);
        Self::lemma_x0_le_sn(x0, n, S);
        let t = S / n;
        assert(Self::greedy_x(a, n, S) == Self::min_int(a, t));
        assert(x0 <= a);
        assert(x0 <= t);
        assert(x0 <= Self::min_int(a, t));
        assert(x0 <= Self::greedy_x(a, n, S));
    }

    proof fn lemma_impossible(a: int, b: int, n: int, S: int)
        requires
            1 <= a,
            1 <= b,
            1 <= n,
            1 <= S,
            Self::greedy_remainder(a, n, S) > b,
        ensures
            !Self::can_pay_exact(a, b, n, S),
    {
        let r = Self::greedy_remainder(a, n, S);
        assert forall|x0: int, y0: int|
            (0 <= x0 <= a && 0 <= y0 <= b && #[trigger] (x0 * n + y0) == S) implies
            false
        by {
            Self::lemma_x0_le_greedy(a, n, S, x0, y0);
            let xg = Self::greedy_x(a, n, S);
            assert(x0 <= xg);
            assert(n >= 1);
            lemma_mul_inequality(x0, xg, n);
            assert(x0 * n <= xg * n);
            assert(y0 == S - x0 * n);
            assert(S - xg * n <= S - x0 * n);
            assert(r <= y0);
            assert(y0 <= b);
            assert(r <= b);
            assert(r > b);
            assert(false);
        };
        assert(!Self::can_pay_exact(a, b, n, S));
    }

    proof fn lemma_exec_matches_greedy(a: i64, n: i64, S: i64, x: i64)
        requires
            1 <= a <= 1000000000,
            1 <= n <= 1000000000,
            1 <= S <= 1000000000,
            (a < S / n && x == a) || (!(a < S / n) && x == S / n),
        ensures
            x as int == Self::greedy_x(a as int, n as int, S as int),
    {
        let ai = a as int;
        let ni = n as int;
        let Si = S as int;
        let ti = Si / ni;
        assert((S / n) as int == ti);
        if a < S / n {
            assert(x == a);
            assert((a as int) < (S / n) as int);
            assert(ai < ti);
            assert(Self::min_int(ai, ti) == ai);
            assert(x as int == Self::greedy_x(ai, ni, Si));
        } else {
            assert(x == S / n);
            assert((a as int) >= (S / n) as int);
            assert(ai >= ti);
            assert(Self::min_int(ai, ti) == ti);
            assert(x as int == Self::greedy_x(ai, ni, Si));
        }
    }

    proof fn lemma_mul_no_overflow(x: i64, n: i64, S: i64, a: i64)
        requires
            1 <= a <= 1000000000,
            1 <= n <= 1000000000,
            1 <= S <= 1000000000,
            0 <= x <= a,
            x <= S / n,
        ensures
            x * n <= S,
    {
        let xi = x as int;
        let ni = n as int;
        let Si = S as int;
        let qi = Si / ni;
        let ri = Si % ni;
        lemma_fundamental_div_mod(Si, ni);
        lemma_remainder(Si, ni);
        assert(Si == ni * qi + ri);
        lemma_mul_is_commutative(ni, qi);
        assert(Si == qi * ni + ri);
        assert(qi * ni <= Si);
        assert(xi <= qi);
        lemma_mul_inequality(xi, qi, ni);
        assert(xi * ni <= qi * ni);
        assert(xi * ni <= Si);
        lemma_mul_upper_bound(xi, a as int, ni, 1000000000);
        assert(xi * ni <= 1000000000000000000);
        assert(1000000000000000000 < 0x7fff_ffff_ffff_ffff);
        assert((x * n) as int == xi * ni);
    }

    pub fn payment_without_change(a: i64, b: i64, n: i64, S: i64) -> (res: bool)
        requires
            1 <= a <= 1000000000,
            1 <= b <= 1000000000,
            1 <= n <= 1000000000,
            1 <= S <= 1000000000,
        ensures
            res == Self::can_pay_exact(a as int, b as int, n as int, S as int),
    {
        let x = if a < S / n {
            a
        } else {
            S / n
        };
        proof {
            assert((a < S / n && x == a) || (!(a < S / n) && x == S / n));
            Self::lemma_exec_matches_greedy(a, n, S, x);
            assert(x <= a);
            assert(x <= S / n);
            Self::lemma_mul_no_overflow(x, n, S, a);
        }
        let rem = S - x * n;
        proof {
            assert(rem as int == Self::greedy_remainder(a as int, n as int, S as int));
            if rem <= b {
                Self::lemma_sound(a as int, b as int, n as int, S as int);
            } else {
                Self::lemma_impossible(a as int, b as int, n as int, S as int);
            }
        }
        rem <= b
    }
}

}
