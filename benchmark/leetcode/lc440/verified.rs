use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn strip_trailing_zeros(y: nat) -> nat
        decreases y,
    {
        if y % 10 == 0 && y != 0 {
            Self::strip_trailing_zeros((y / 10) as nat)
        } else {
            y
        }
    }

    pub open spec fn lex_next(x: int, n: int) -> int {
        if x * 10 <= n {
            x * 10
        } else if x % 10 != 9 && x + 1 <= n {
            x + 1
        } else {
            Self::strip_trailing_zeros(((x / 10) + 1) as nat) as int
        }
    }

    pub open spec fn lex_elem(i: nat, n: int) -> int
        decreases i,
    {
        if i == 0 {
            1
        } else {
            Self::lex_next(Self::lex_elem((i - 1) as nat, n), n)
        }
    }

    pub open spec fn spec_find_kth_number(n: int, k: int) -> int
        recommends
            1 <= k <= n,
            1 <= n,
    {
        Self::lex_elem((k - 1) as nat, n)
    }

    proof fn strip_trailing_zeros_range(y: nat)
        requires
            y >= 1,
        ensures
            1 <= Self::strip_trailing_zeros(y) <= y,
        decreases y,
    {
        if y % 10 == 0 && y != 0 {
            Self::strip_trailing_zeros_range((y / 10) as nat);
        }
    }

    proof fn lex_next_in_range(x: int, n: int)
        requires
            1 <= n,
            1 <= x <= n,
        ensures
            1 <= Self::lex_next(x, n) <= n,
    {
        if x * 10 <= n {
        } else if x % 10 != 9 && x + 1 <= n {
        } else {
            Self::strip_trailing_zeros_range(((x / 10) + 1) as nat);
        }
    }

    pub open spec fn pow10(k: nat) -> int
        decreases k,
    {
        if k == 0 { 1 } else { 10 * Self::pow10((k - 1) as nat) }
    }

    proof fn lemma_pow10_pos(k: nat)
        ensures
            Self::pow10(k) >= 1,
        decreases k,
    {
        if k > 0 {
            Self::lemma_pow10_pos((k - 1) as nat);
        }
    }

    proof fn lemma_pow10_10_big()
        ensures
            Self::pow10(10) > 1_000_000_000,
    {
        assert(Self::pow10(0) == 1);
        assert(Self::pow10(1) == 10 * Self::pow10(0));
        assert(Self::pow10(2) == 10 * Self::pow10(1));
        assert(Self::pow10(3) == 10 * Self::pow10(2));
        assert(Self::pow10(4) == 10 * Self::pow10(3));
        assert(Self::pow10(5) == 10 * Self::pow10(4));
        assert(Self::pow10(6) == 10 * Self::pow10(5));
        assert(Self::pow10(7) == 10 * Self::pow10(6));
        assert(Self::pow10(8) == 10 * Self::pow10(7));
        assert(Self::pow10(9) == 10 * Self::pow10(8));
        assert(Self::pow10(10) == 10 * Self::pow10(9));
    }

    proof fn lemma_pow10_11_bigger()
        ensures
            Self::pow10(11) > 10_000_000_000,
    {
        Self::lemma_pow10_10_big();
        assert(Self::pow10(11) == 10 * Self::pow10(10));
    }

    proof fn lemma_pow10_monotonic(a: nat, b: nat)
        requires
            a <= b,
        ensures
            Self::pow10(a) <= Self::pow10(b),
        decreases b - a,
    {
        if a < b {
            Self::lemma_pow10_monotonic(a, (b - 1) as nat);
            Self::lemma_pow10_pos((b - 1) as nat);
        }
    }

    pub open spec fn spec_count_steps_fuel(n: int, curr: int, next: int, fuel: nat) -> int
        decreases fuel,
    {
        if fuel == 0 || curr > n {
            0
        } else {
            let bound = if next <= n + 1 { next } else { n + 1 };
            (bound - curr) + Self::spec_count_steps_fuel(n, curr * 10, next * 10, (fuel - 1) as nat)
        }
    }

    proof fn lemma_count_steps_fuel_extra(n: int, curr: int, next: int, f: nat)
        requires
            curr >= 1,
            curr * Self::pow10(f) > n,
        ensures
            Self::spec_count_steps_fuel(n, curr, next, f) == Self::spec_count_steps_fuel(n, curr, next, (f + 1) as nat),
        decreases f,
    {
        Self::lemma_pow10_pos(f);
        if curr > n {
        } else {
            if f == 0 {
                assert(Self::pow10(0) == 1);
                assert(false);
            }
            let fm1 = (f - 1) as nat;
            assert(Self::pow10(f) == 10 * Self::pow10(fm1));
            assert((curr * 10) * Self::pow10(fm1) == curr * (10 * Self::pow10(fm1))) by (nonlinear_arith);
            assert((curr * 10) * Self::pow10(fm1) > n);
            Self::lemma_count_steps_fuel_extra(n, curr * 10, next * 10, fm1);
        }
    }

    pub open spec fn spec_count_steps(n: int, curr: int, next: int) -> int {
        Self::spec_count_steps_fuel(n, curr, next, 12)
    }

    proof fn lemma_count_steps_unfold(n: int, curr: int, next: int)
        requires
            1 <= curr,
            curr <= n,
            n <= 1_000_000_000,
        ensures
            Self::spec_count_steps(n, curr, next) ==
                (if next <= n + 1 { next } else { n + 1 } - curr)
                    + Self::spec_count_steps(n, curr * 10, next * 10),
    {
        Self::lemma_pow10_11_bigger();
        assert((curr * 10) * Self::pow10(11) >= 1 * Self::pow10(11)) by (nonlinear_arith)
            requires
                curr * 10 >= 1,
                Self::pow10(11) >= 0,
        {
        }
        assert((curr * 10) * Self::pow10(11) > n);
        Self::lemma_count_steps_fuel_extra(n, curr * 10, next * 10, 11);
    }

    proof fn lemma_count_steps_fuel_nonneg(n: int, curr: int, next: int, fuel: nat)
        requires
            curr <= next,
            curr >= 1,
        ensures
            Self::spec_count_steps_fuel(n, curr, next, fuel) >= 0,
        decreases fuel,
    {
        if fuel > 0 && curr <= n {
            Self::lemma_count_steps_fuel_nonneg(n, curr * 10, next * 10, (fuel - 1) as nat);
        }
    }

    proof fn lemma_count_steps_fuel_eq(n: int, x: int, fuel: nat)
        requires
            x >= 1,
        ensures
            Self::spec_count_steps_fuel(n, x, x, fuel) == 0,
        decreases fuel,
    {
        if fuel > 0 && x <= n {
            Self::lemma_count_steps_fuel_eq(n, x * 10, (fuel - 1) as nat);
        }
    }

    proof fn lemma_count_steps_eq(n: int, x: int)
        requires
            x >= 1,
        ensures
            Self::spec_count_steps(n, x, x) == 0,
    {
        Self::lemma_count_steps_fuel_eq(n, x, 12);
    }

    proof fn lemma_count_steps_fuel_additive(n: int, curr: int, mid: int, hi: int, fuel: nat)
        requires
            1 <= curr <= mid <= hi,
        ensures
            Self::spec_count_steps_fuel(n, curr, hi, fuel) ==
                Self::spec_count_steps_fuel(n, curr, mid, fuel) + Self::spec_count_steps_fuel(n, mid, hi, fuel),
        decreases fuel,
    {
        if fuel == 0 {
            return;
        }
        if curr > n {
            return;
        }
        let fm1 = (fuel - 1) as nat;
        Self::lemma_count_steps_fuel_additive(n, curr * 10, mid * 10, hi * 10, fm1);
        if mid <= n {
            assert(Self::spec_count_steps_fuel(n, curr, mid, fuel)
                == (mid - curr) + Self::spec_count_steps_fuel(n, curr * 10, mid * 10, fm1));
            assert(Self::spec_count_steps_fuel(n, mid, hi, fuel)
                == ((if hi <= n + 1 { hi } else { n + 1 }) - mid) + Self::spec_count_steps_fuel(n, mid * 10, hi * 10, fm1));
            assert(Self::spec_count_steps_fuel(n, curr, hi, fuel)
                == ((if hi <= n + 1 { hi } else { n + 1 }) - curr) + Self::spec_count_steps_fuel(n, curr * 10, hi * 10, fm1));
        } else {
            assert(mid * 10 > n);
            assert(Self::spec_count_steps_fuel(n, mid * 10, hi * 10, fm1) == 0);
            assert(Self::spec_count_steps_fuel(n, mid, hi, fuel) == 0);
            assert(Self::spec_count_steps_fuel(n, curr, mid, fuel)
                == (n + 1 - curr) + Self::spec_count_steps_fuel(n, curr * 10, mid * 10, fm1));
            assert(Self::spec_count_steps_fuel(n, curr, hi, fuel)
                == (n + 1 - curr) + Self::spec_count_steps_fuel(n, curr * 10, hi * 10, fm1));
        }
    }

    proof fn lemma_count_steps_additive(n: int, curr: int, mid: int, hi: int)
        requires
            1 <= curr <= mid <= hi,
        ensures
            Self::spec_count_steps(n, curr, hi) ==
                Self::spec_count_steps(n, curr, mid) + Self::spec_count_steps(n, mid, hi),
    {
        Self::lemma_count_steps_fuel_additive(n, curr, mid, hi, 12);
    }

    pub open spec fn clip(n: int, v: int) -> int {
        if v <= n + 1 { v } else { n + 1 }
    }

    proof fn lemma_count_power_range(n: int, k: nat, budget: nat)
        requires
            1 <= n <= 1_000_000_000,
            k + budget >= 11,
        ensures
            Self::spec_count_steps(n, Self::pow10(k), Self::pow10((k + 1) as nat))
                == (if Self::pow10(k) <= n { n + 1 - Self::pow10(k) } else { 0 }),
        decreases budget,
    {
        Self::lemma_pow10_pos(k);
        let pk = Self::pow10(k);
        let pk1 = Self::pow10((k + 1) as nat);
        assert(pk1 == 10 * pk);
        if pk > n {
            assert(Self::spec_count_steps(n, pk, pk1) == 0) by {
                assert(Self::spec_count_steps_fuel(n, pk, pk1, 12) == 0);
            }
        } else {
            Self::lemma_count_steps_unfold(n, pk, pk1);
            assert(Self::spec_count_steps(n, pk, pk1)
                == Self::clip(n, pk1) - pk + Self::spec_count_steps(n, pk * 10, pk1 * 10));
            assert(pk * 10 == Self::pow10((k + 1) as nat));
            assert(pk1 * 10 == Self::pow10((k + 2) as nat));
            if budget == 0 {
                assert(k >= 11);
                Self::lemma_pow10_11_bigger();
                Self::lemma_pow10_monotonic(11, k);
                assert(false);
            } else {
                Self::lemma_count_power_range(n, (k + 1) as nat, (budget - 1) as nat);
                if pk1 <= n {
                    assert(Self::clip(n, pk1) == pk1);
                    assert(Self::spec_count_steps(n, pk1, Self::pow10((k + 2) as nat)) == n + 1 - pk1);
                } else {
                    assert(Self::clip(n, pk1) == n + 1);
                    assert(Self::spec_count_steps(n, pk1, Self::pow10((k + 2) as nat)) == 0);
                }
            }
        }
    }

    proof fn lemma_count_steps_total(n: int)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            Self::spec_count_steps(n, 1, 10) == n,
    {
        assert(Self::pow10(0) == 1);
        assert(Self::pow10(1) == 10);
        Self::lemma_count_power_range(n, 0, 11);
    }

    proof fn lemma_count_steps_bound_gen(n: int, curr: int, next: int)
        requires
            1 <= curr <= n + 1,
            curr <= next <= 10 * curr,
            1 <= n <= 1_000_000_000,
        ensures
            0 <= Self::spec_count_steps(n, curr, next) <= n + 1 - curr,
        decreases (if curr <= n { n + 1 - curr } else { 0 }) as nat,
    {
        Self::lemma_count_steps_fuel_nonneg(n, curr, next, 12);
        if curr <= n {
            Self::lemma_count_steps_unfold(n, curr, next);
            if curr * 10 <= n {
                Self::lemma_count_steps_bound_gen(n, curr * 10, next * 10);
            } else {
                assert(Self::spec_count_steps(n, curr * 10, next * 10) == 0) by {
                    assert(Self::spec_count_steps_fuel(n, curr * 10, next * 10, 12) == 0);
                }
            }
        }
    }

    proof fn lemma_count_steps_subtree_bound(n: int, curr: int)
        requires
            1 <= curr <= n + 1,
            1 <= n <= 1_000_000_000,
        ensures
            0 <= Self::spec_count_steps(n, curr, curr + 1) <= n + 1 - curr,
    {
        Self::lemma_count_steps_bound_gen(n, curr, curr + 1);
    }

    pub open spec fn lt_count(x: int, n: int) -> int
        decreases x,
    {
        if x <= 0 {
            0
        } else {
            let p = x / 10;
            let sib_start = if p == 0 { 1int } else { p * 10 };
            (if p >= 1 { Self::lt_count(p, n) + (if p <= n { 1int } else { 0int }) } else { 0int })
                + Self::spec_count_steps(n, sib_start, x)
        }
    }

    proof fn lemma_div10_mul10(y: int)
        requires
            y >= 1,
        ensures
            (y * 10) / 10 == y,
    {
        assert(y * 10 == 10 * y);
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(y, 10);
    }

    proof fn lemma_lt_count_mult10(y: int, n: int)
        requires
            y >= 1,
        ensures
            Self::lt_count(y * 10, n) == Self::lt_count(y, n) + (if y <= n { 1int } else { 0int }),
    {
        Self::lemma_div10_mul10(y);
        let x = y * 10;
        assert(x / 10 == y);
        Self::lemma_count_steps_eq(n, x);
    }

    proof fn lemma_div_no_carry(q: int)
        requires
            q >= 0,
            (q + 1) % 10 != 0,
        ensures
            (q + 1) / 10 == q / 10,
    {
        assert(q == 10 * (q / 10) + q % 10) by (nonlinear_arith)
            requires true
        {
        }
        assert((q + 1) == 10 * (q / 10) + (q % 10 + 1));
        assert(0 <= q % 10 < 10);
        assert(q % 10 + 1 != 10);
        assert(0 <= q % 10 + 1 <= 10);
        assert(q % 10 + 1 < 10);
        assert((q + 1) / 10 == q / 10) by (nonlinear_arith)
            requires
                (q + 1) == 10 * (q / 10) + (q % 10 + 1),
                0 <= q % 10 + 1 < 10,
        {
        }
    }

    proof fn lemma_lt_count_same_parent(q: int, n: int)
        requires
            q >= 1,
            (q + 1) % 10 != 0,
        ensures
            Self::lt_count(q + 1, n) == Self::lt_count(q, n) + Self::spec_count_steps(n, q, q + 1),
    {
        Self::lemma_div_no_carry(q);
        let gp = q / 10;
        let sib_start = if gp == 0 { 1int } else { gp * 10 };
        assert((q + 1) / 10 == gp);
        assert(sib_start <= q) by (nonlinear_arith)
            requires
                gp == q / 10,
                q >= 1,
                sib_start == (if gp == 0 { 1int } else { gp * 10 }),
                q == 10 * gp + (q % 10),
                0 <= q % 10 < 10,
        {
        }
        Self::lemma_count_steps_additive(n, sib_start, q, q + 1);
        assert(Self::lt_count(q + 1, n)
            == (if gp >= 1 { Self::lt_count(gp, n) + (if gp <= n { 1int } else { 0int }) } else { 0int })
                + Self::spec_count_steps(n, sib_start, q + 1));
        assert(Self::lt_count(q, n)
            == (if gp >= 1 { Self::lt_count(gp, n) + (if gp <= n { 1int } else { 0int }) } else { 0int })
                + Self::spec_count_steps(n, sib_start, q));
    }

    proof fn lemma_div_bounded(q: int, r: int)
        requires
            q >= 0,
            0 <= r <= 9,
        ensures
            (q * 10 + r) / 10 == q,
    {
        assert(q * 10 + r == 10 * q + r) by (nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(q * 10 + r, 10, q, r);
    }

    proof fn lemma_last_child_total_rank(q: int, y: int, n: int)
        requires
            q >= 1,
            1 <= n <= 1_000_000_000,
            0 <= y - q * 10 <= 9,
            y <= n,
            (y % 10 == 9 || y + 1 > n),
        ensures
            Self::lt_count(y, n) + Self::spec_count_steps(n, y, y + 1)
                == Self::lt_count(q, n) + Self::spec_count_steps(n, q, q + 1),
    {
        let r = y - q * 10;
        Self::lemma_div_bounded(q, r);
        assert(y / 10 == q);
        let end10 = q * 10 + 10;
        assert(y <= end10);
        Self::lemma_count_steps_additive(n, q * 10, y, end10);
        Self::lemma_count_steps_additive(n, y, y + 1, end10);
        if y % 10 == 9 {
            assert(y + 1 == end10);
            Self::lemma_count_steps_eq(n, y + 1);
        } else {
            assert(y + 1 > n);
            assert(Self::spec_count_steps(n, y + 1, end10) == 0) by {
                assert(Self::spec_count_steps_fuel(n, y + 1, end10, 12) == 0);
            }
        }
        assert(Self::spec_count_steps(n, q * 10, end10) ==
            Self::spec_count_steps(n, q * 10, y) + Self::spec_count_steps(n, y, y + 1));
        Self::lemma_count_steps_unfold(n, q, q + 1);
        assert((q + 1) * 10 == q * 10 + 10);
        assert((q + 1) * 10 == end10);
        assert(Self::spec_count_steps(n, q, q + 1)
            == (if q + 1 <= n + 1 { q + 1 } else { n + 1 } - q) + Self::spec_count_steps(n, q * 10, end10));
        assert((if q + 1 <= n + 1 { q + 1 } else { n + 1 } - q) == 1);
        assert(Self::lt_count(y, n)
            == (Self::lt_count(q, n) + (if q <= n { 1int } else { 0int })) + Self::spec_count_steps(n, q * 10, y));
        assert(q <= n);
    }

    proof fn lemma_advance(q: int, n: int)
        requires
            q >= 1,
            1 <= n <= 1_000_000_000,
            q <= n,
            Self::lt_count(q, n) + Self::spec_count_steps(n, q, q + 1) < n,
        ensures
            Self::lt_count(Self::strip_trailing_zeros((q + 1) as nat) as int, n)
                == Self::lt_count(q, n) + Self::spec_count_steps(n, q, q + 1),
        decreases q,
    {
        if (q + 1) % 10 != 0 {
            Self::lemma_lt_count_same_parent(q, n);
            assert(Self::strip_trailing_zeros((q + 1) as nat) == (q + 1) as nat);
        } else {
            let gp = q / 10;
            assert(q == 10 * gp + q % 10);
            assert(q % 10 == 9);
            if gp == 0 {
                assert(q == 9);
                assert(Self::lt_count(9, n) == 0 + Self::spec_count_steps(n, 1, 9));
                Self::lemma_count_steps_additive(n, 1, 9, 10);
                Self::lemma_count_steps_total(n);
                assert(false);
            } else {
                assert(q - gp * 10 == 9);
                Self::lemma_last_child_total_rank(gp, q, n);
                assert(Self::lt_count(gp, n) + Self::spec_count_steps(n, gp, gp + 1) < n);
                assert(gp <= n);
                Self::lemma_advance(gp, n);
                assert((q + 1) / 10 == gp + 1);
                assert((q + 1) % 10 == 0);
                assert((q + 1) as nat != 0);
                assert(Self::strip_trailing_zeros((q + 1) as nat)
                    == Self::strip_trailing_zeros(((q + 1) / 10) as nat));
            }
        }
    }

    proof fn lemma_lex_next_advances(y: int, n: int)
        requires
            1 <= y <= n,
            n <= 1_000_000_000,
            Self::lt_count(y, n) < n - 1,
        ensures
            Self::lt_count(Self::lex_next(y, n), n) == Self::lt_count(y, n) + 1,
    {
        if y * 10 <= n {
            Self::lemma_lt_count_mult10(y, n);
            assert(Self::lex_next(y, n) == y * 10);
        } else if y % 10 != 9 && y + 1 <= n {
            Self::lemma_lt_count_same_parent(y, n);
            assert((y + 1) % 10 != 0);
            Self::lemma_count_steps_unfold(n, y, y + 1);
            assert(Self::spec_count_steps_fuel(n, y * 10, (y + 1) * 10, 12) == 0);
            assert(Self::spec_count_steps(n, y, y + 1)
                == (if y + 1 <= n + 1 { y + 1 } else { n + 1 } - y) + Self::spec_count_steps(n, y * 10, (y + 1) * 10));
            assert(Self::spec_count_steps(n, y, y + 1) == 1);
            assert(Self::lex_next(y, n) == y + 1);
        } else {
            let qq = y / 10;
            assert(y == 10 * qq + y % 10);
            Self::lemma_count_steps_unfold(n, y, y + 1);
            assert(Self::spec_count_steps_fuel(n, y * 10, (y + 1) * 10, 12) == 0);
            assert(Self::spec_count_steps(n, y, y + 1) == 1);
            if qq == 0 {
                assert(y <= 9);
                Self::lemma_count_steps_additive(n, 1, y, y + 1);
                if y == 9 {
                    Self::lemma_count_steps_additive(n, 1, 9, 10);
                } else {
                    assert(y + 1 > n);
                    Self::lemma_count_steps_additive(n, 1, y + 1, 10);
                    assert(Self::spec_count_steps(n, y + 1, 10) == 0) by {
                        assert(Self::spec_count_steps_fuel(n, y + 1, 10, 12) == 0);
                    }
                }
                Self::lemma_count_steps_total(n);
                assert(Self::lt_count(y, n) == Self::spec_count_steps(n, 1, y));
                assert(false);
            } else {
                Self::lemma_last_child_total_rank(qq, y, n);
                assert(Self::lt_count(qq, n) + Self::spec_count_steps(n, qq, qq + 1) < n);
                assert(qq <= n);
                Self::lemma_advance(qq, n);
                assert(Self::lex_next(y, n) == Self::strip_trailing_zeros((qq + 1) as nat) as int);
            }
        }
    }

    proof fn lemma_lex_elem_rank(n: int, i: nat)
        requires
            1 <= n <= 1_000_000_000,
            i as int <= n - 1,
        ensures
            1 <= Self::lex_elem(i, n) <= n,
            Self::lt_count(Self::lex_elem(i, n), n) == i as int,
        decreases i,
    {
        if i == 0 {
            assert(Self::lex_elem(0, n) == 1);
            Self::lemma_count_steps_eq(n, 1);
            assert(Self::lt_count(1, n) == 0 + Self::spec_count_steps(n, 1, 1));
        } else {
            Self::lemma_lex_elem_rank(n, (i - 1) as nat);
            let y = Self::lex_elem((i - 1) as nat, n);
            assert(Self::lex_elem(i, n) == Self::lex_next(y, n));
            Self::lex_next_in_range(y, n);
            Self::lemma_lex_next_advances(y, n);
        }
    }

    proof fn lemma_lex_elem_surjective(n: int, r_val: int)
        requires
            1 <= n <= 1_000_000_000,
            1 <= r_val <= n,
        ensures
            exists|j: int| 0 <= j < n && #[trigger] Self::lex_elem(j as nat, n) == r_val,
    {
        let f = |j: int| Self::lex_elem(j as nat, n);
        let idx_set = vstd::set_lib::set_int_range(0, n);
        let full_set = vstd::set_lib::set_int_range(1, n + 1);
        vstd::set_lib::lemma_int_range(0, n);
        vstd::set_lib::lemma_int_range(1, n + 1);
        assert forall|a: int, b: int| idx_set.contains(a) && idx_set.contains(b) && f(a) == f(b) implies a == b by {
            Self::lemma_lex_elem_rank(n, a as nat);
            Self::lemma_lex_elem_rank(n, b as nat);
        }
        assert(vstd::relations::injective_on(f, idx_set));
        let image_set = idx_set.map(f);
        vstd::set_lib::lemma_map_size(idx_set, image_set, f);
        assert forall|v: int| image_set.contains(v) implies full_set.contains(v) by {
            let j = choose|j: int| idx_set.contains(j) && f(j) == v;
            Self::lemma_lex_elem_rank(n, j as nat);
        }
        assert(image_set.subset_of(full_set));
        vstd::set_lib::lemma_subset_equality(image_set, full_set);
        assert(full_set.contains(r_val));
        assert(image_set.contains(r_val));
        let j = choose|j: int| idx_set.contains(j) && f(j) == r_val;
        assert(0 <= j < n);
        assert(Self::lex_elem(j as nat, n) == r_val);
    }

    proof fn lemma_lt_count_unique(n: int, r_val: int, j0: int)
        requires
            1 <= n <= 1_000_000_000,
            1 <= r_val <= n,
            0 <= j0 <= n - 1,
            Self::lt_count(r_val, n) == j0,
        ensures
            r_val == Self::lex_elem(j0 as nat, n),
    {
        Self::lemma_lex_elem_surjective(n, r_val);
        let j = choose|j: int| 0 <= j < n && #[trigger] Self::lex_elem(j as nat, n) == r_val;
        Self::lemma_lex_elem_rank(n, j as nat);
        assert(j == j0);
    }

    proof fn lemma_fast_step(n: int, curr: int, k_left: nat, s: int)
        requires
            curr >= 1,
            1 <= n <= 1_000_000_000,
            k_left > 0,
            s == Self::spec_count_steps(n, curr, curr + 1),
            (k_left as int) < Self::spec_count_steps(n, curr, ((curr / 10) + 1) * 10),
        ensures
            s <= k_left as int ==> ({
                &&& ((k_left - s) as int) < Self::spec_count_steps(n, curr + 1, (((curr + 1) / 10) + 1) * 10)
                &&& Self::lt_count(curr + 1, n) == Self::lt_count(curr, n) + s
            }),
            s > k_left as int ==> ({
                &&& curr <= n
                &&& ((k_left - 1) as int) < Self::spec_count_steps(n, curr * 10, (curr + 1) * 10)
                &&& Self::lt_count(curr * 10, n) == Self::lt_count(curr, n) + 1
            }),
    {
        let g = ((curr / 10) + 1) * 10;
        if curr > n {
            assert(Self::spec_count_steps_fuel(n, curr, g, 12) == 0);
            assert(false);
        }
        assert(curr <= n);
        assert(curr == 10 * (curr / 10) + curr % 10);
        assert(0 <= curr % 10 < 10);
        assert(curr < g);
        assert(curr + 1 <= g);
        Self::lemma_count_steps_additive(n, curr, curr + 1, g);
        if s <= k_left as int {
            assert(Self::spec_count_steps(n, curr + 1, g) > (k_left as int) - s);
            assert(Self::spec_count_steps(n, curr + 1, g) >= 1);
            if curr + 1 == g {
                Self::lemma_count_steps_eq(n, g);
                assert(false);
            }
            assert(curr + 1 < g);
            assert((curr + 1) % 10 != 0);
            assert((curr + 1) / 10 == curr / 10);
            let gg = ((curr + 1) / 10 + 1) * 10;
            assert(gg == g);
            Self::lemma_lt_count_same_parent(curr, n);
        } else {
            assert(s > k_left as int);
            assert(s >= 2);
            Self::lemma_count_steps_unfold(n, curr, curr + 1);
            assert(s == (if curr + 1 <= n + 1 { curr + 1 } else { n + 1 } - curr)
                + Self::spec_count_steps(n, curr * 10, (curr + 1) * 10));
            assert((if curr + 1 <= n + 1 { curr + 1 } else { n + 1 } - curr) == 1);
            assert(s == 1 + Self::spec_count_steps(n, curr * 10, (curr + 1) * 10));
            assert((curr * 10) / 10 == curr) by (nonlinear_arith);
            assert(((curr * 10) / 10 + 1) * 10 == (curr + 1) * 10);
            Self::lemma_lt_count_mult10(curr, n);
        }
    }

    fn count_steps(n: i64, curr_in: i64, next_in: i64) -> (steps: i64)
        requires
            1 <= curr_in,
            next_in == curr_in + 1,
            curr_in <= n + 1,
            1 <= n <= 1_000_000_000,
        ensures
            steps as int == Self::spec_count_steps(n as int, curr_in as int, next_in as int),
    {
        proof {
            Self::lemma_count_steps_subtree_bound(n as int, curr_in as int);
        }
        let mut steps: i64 = 0;
        let mut curr = curr_in;
        let mut next = next_in;
        let ghost orig_curr = curr_in as int;
        let ghost orig_next = next_in as int;
        while curr <= n
            invariant
                1 <= n <= 1_000_000_000,
                1 <= curr,
                (next as int) * orig_curr == (curr as int) * (orig_curr + 1),
                1 <= orig_curr,
                steps >= 0,
                curr as int <= 10_000_000_001int,
                next as int <= 20_000_000_002int,
                steps as int + Self::spec_count_steps(n as int, curr as int, next as int)
                    == Self::spec_count_steps(n as int, orig_curr, orig_next),
                Self::spec_count_steps(n as int, orig_curr, orig_next) <= n as int + 1 - orig_curr,
            decreases (if curr <= n { n + 1 - curr } else { 0 }) as int,
        {
            assert((next as int - curr as int) * orig_curr == curr as int) by (nonlinear_arith)
                requires
                    (next as int) * orig_curr == (curr as int) * (orig_curr + 1),
            {
            }
            assert(next as int >= curr as int) by (nonlinear_arith)
                requires
                    (next as int - curr as int) * orig_curr == curr as int,
                    orig_curr >= 1,
                    curr as int >= 1,
            {
            }
            assert(next as int <= 2 * curr as int) by (nonlinear_arith)
                requires
                    (next as int) * orig_curr == (curr as int) * (orig_curr + 1),
                    orig_curr >= 1,
                    curr as int >= 1,
            {
            }
            let bound = if next <= n + 1 { next } else { n + 1 };
            proof {
                Self::lemma_count_steps_unfold(n as int, curr as int, next as int);
                Self::lemma_count_steps_fuel_nonneg(n as int, curr as int * 10, next as int * 10, 12);
                assert(bound as int <= n as int + 1);
                assert(bound as int >= curr as int);
                assert(bound as int - curr as int
                    <= Self::spec_count_steps(n as int, orig_curr, orig_next) - steps as int);
            }
            steps = steps + (bound - curr);
            assert((next as int * 10) * orig_curr == (curr as int * 10) * (orig_curr + 1)) by (nonlinear_arith)
                requires
                    (next as int) * orig_curr == (curr as int) * (orig_curr + 1),
            {
            }
            curr = curr * 10;
            next = next * 10;
        }
        proof {
            assert(Self::spec_count_steps(n as int, curr as int, next as int) == 0) by {
                assert(Self::spec_count_steps_fuel(n as int, curr as int, next as int, 12) == 0);
            }
        }
        steps
    }

    pub fn find_kth_number(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000000000,
            1 <= k <= n,
        ensures
            result as int == Self::spec_find_kth_number(n as int, k as int),
    {
        let n64 = n as i64;
        let mut k_left: i64 = (k - 1) as i64;
        let mut curr: i64 = 1;
        proof {
            Self::lemma_count_steps_total(n64 as int);
            assert(((1int / 10) + 1) * 10 == 10int);
            Self::lemma_count_steps_eq(n64 as int, 1);
        }
        while k_left > 0
            invariant
                1 <= n64 as int <= 1_000_000_000,
                1 <= curr,
                0 <= k_left,
                curr as int <= n64 as int,
                (k_left as int) < Self::spec_count_steps(n64 as int, curr as int, ((curr as int / 10) + 1) * 10),
                Self::lt_count(curr as int, n64 as int) + (k_left as int) == (k as int - 1),
            decreases k_left,
        {
            let steps = Self::count_steps(n64, curr, curr + 1);
            proof {
                Self::lemma_fast_step(n64 as int, curr as int, k_left as nat, steps as int);
                Self::lemma_count_steps_fuel_nonneg(n64 as int, curr as int, curr as int + 1, 12);
                assert(steps as int >= 0);
                Self::lemma_count_steps_unfold(n64 as int, curr as int, curr as int + 1);
                assert(Self::spec_count_steps(n64 as int, curr as int, curr as int + 1)
                    == (if curr as int + 1 <= n64 as int + 1 { curr as int + 1 } else { n64 as int + 1 } - curr as int)
                        + Self::spec_count_steps(n64 as int, curr as int * 10, (curr as int + 1) * 10));
                assert((if curr as int + 1 <= n64 as int + 1 { curr as int + 1 } else { n64 as int + 1 } - curr as int) == 1);
                Self::lemma_count_steps_fuel_nonneg(n64 as int, curr as int * 10, (curr as int + 1) * 10, 12);
                assert(steps as int >= 1);
            }
            if steps <= k_left {
                curr = curr + 1;
                k_left = k_left - steps;
            } else {
                curr = curr * 10;
                k_left = k_left - 1;
            }
        }
        proof {
            assert(Self::lt_count(curr as int, n64 as int) == (k as int - 1));
            Self::lemma_lt_count_unique(n64 as int, curr as int, k as int - 1);
        }
        curr as i32
    }
}

}
