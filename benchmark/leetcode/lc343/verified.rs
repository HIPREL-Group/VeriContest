use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<int>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            s[0] + Self::seq_sum(s.subrange(1, s.len() as int))
        }
    }

    pub open spec fn seq_product(s: Seq<int>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            1
        } else {
            s[0] * Self::seq_product(s.subrange(1, s.len() as int))
        }
    }

    pub open spec fn is_valid_partition(s: Seq<int>, n: int) -> bool {
        s.len() >= 2
        && (forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1)
        && Self::seq_sum(s) == n
    }

    pub open spec fn pow3(exp: nat) -> int
        decreases exp,
    {
        if exp == 0 { 1 } else { 3 * Self::pow3((exp - 1) as nat) }
    }

    pub open spec fn spec_integer_break(n: int) -> int {
        if n == 2 {
            1
        } else if n == 3 {
            2
        } else {
            let q = n / 3;
            let r = n % 3;
            if r == 0 {
                Self::pow3(q as nat)
            } else if r == 1 {
                Self::pow3((q - 1) as nat) * 4
            } else {
                Self::pow3(q as nat) * 2
            }
        }
    }

    proof fn lemma_pow3_unfold(e: nat)
        ensures Self::pow3(e) == if e == 0 { 1 } else { 3 * Self::pow3((e - 1) as nat) },
    {}

    proof fn lemma_pow3_concrete()
        ensures
            Self::pow3(0) == 1,
            Self::pow3(1) == 3,
            Self::pow3(2) == 9,
            Self::pow3(3) == 27,
            Self::pow3(4) == 81,
            Self::pow3(5) == 243,
            Self::pow3(6) == 729,
            Self::pow3(7) == 2187,
            Self::pow3(8) == 6561,
            Self::pow3(9) == 19683,
            Self::pow3(10) == 59049,
            Self::pow3(11) == 177147,
            Self::pow3(12) == 531441,
            Self::pow3(13) == 1594323,
            Self::pow3(14) == 4782969,
            Self::pow3(15) == 14348907,
            Self::pow3(16) == 43046721,
            Self::pow3(17) == 129140163,
            Self::pow3(18) == 387420489,
            Self::pow3(19) == 1162261467,
    {
        reveal_with_fuel(Solution::pow3, 21);
    }

    proof fn lemma_pow3_step(e: nat)
        ensures Self::pow3((e + 1) as nat) == 3 * Self::pow3(e),
    {}

    proof fn lemma_pow3_positive(e: nat)
        ensures Self::pow3(e) >= 1,
        decreases e,
    {
        if e > 0 { Self::lemma_pow3_positive((e - 1) as nat); }
    }

    proof fn lemma_pow3_bound_19(e: nat)
        requires e <= 19,
        ensures 0 < Self::pow3(e) <= 1_162_261_467,
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_pow3_bound_18(e: nat)
        requires e <= 18,
        ensures 0 < Self::pow3(e) <= 387_420_489,
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_seq_unfold_sum(s: Seq<int>)
        requires s.len() >= 1,
        ensures Self::seq_sum(s) == s[0] + Self::seq_sum(s.subrange(1, s.len() as int)),
    {
        reveal_with_fuel(Solution::seq_sum, 2);
    }

    proof fn lemma_seq_unfold_product(s: Seq<int>)
        requires s.len() >= 1,
        ensures Self::seq_product(s) == s[0] * Self::seq_product(s.subrange(1, s.len() as int)),
    {
        reveal_with_fuel(Solution::seq_product, 2);
    }

    proof fn lemma_seq_sum_1(s: Seq<int>)
        requires s.len() == 1,
        ensures Self::seq_sum(s) == s[0],
    {
        reveal_with_fuel(Solution::seq_sum, 2);
        assert(s.subrange(1, 1) =~= Seq::<int>::empty());
    }

    proof fn lemma_seq_product_1(s: Seq<int>)
        requires s.len() == 1,
        ensures Self::seq_product(s) == s[0],
    {
        reveal_with_fuel(Solution::seq_product, 2);
        assert(s.subrange(1, 1) =~= Seq::<int>::empty());
    }

    proof fn lemma_seq_sum_2(s: Seq<int>)
        requires s.len() == 2,
        ensures Self::seq_sum(s) == s[0] + s[1],
    {
        let r = s.subrange(1, 2);
        assert(r =~= seq![s[1]]);
        Self::lemma_seq_unfold_sum(s);
        Self::lemma_seq_sum_1(r);
    }

    proof fn lemma_seq_product_2(s: Seq<int>)
        requires s.len() == 2,
        ensures Self::seq_product(s) == s[0] * s[1],
    {
        let r = s.subrange(1, 2);
        assert(r =~= seq![s[1]]);
        Self::lemma_seq_unfold_product(s);
        Self::lemma_seq_product_1(r);
    }

    proof fn lemma_seq_sum_prepend(v: int, rest: Seq<int>)
        ensures Self::seq_sum(seq![v] + rest) == v + Self::seq_sum(rest),
    {
        let s = seq![v] + rest;
        assert(s.subrange(1, s.len() as int) =~= rest);
        reveal_with_fuel(Solution::seq_sum, 2);
    }

    proof fn lemma_seq_product_prepend(v: int, rest: Seq<int>)
        ensures Self::seq_product(seq![v] + rest) == v * Self::seq_product(rest),
    {
        let s = seq![v] + rest;
        assert(s.subrange(1, s.len() as int) =~= rest);
        reveal_with_fuel(Solution::seq_product, 2);
    }

    proof fn lemma_seq_sum_nonneg(s: Seq<int>)
        requires forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1,
        ensures Self::seq_sum(s) >= 0,
        decreases s.len(),
    {
        if s.len() == 0 {
            reveal_with_fuel(Solution::seq_sum, 2);
        } else {
            Self::lemma_seq_unfold_sum(s);
            Self::lemma_seq_sum_nonneg(s.subrange(1, s.len() as int));
        }
    }

    proof fn lemma_ge_eq(x: int, y: int, m: int)
        requires x == y, y >= m,
        ensures x >= m,
    {}

    proof fn lemma_nat_int_ge(x: int, m: nat)
        requires x >= m as int,
        ensures x >= m,
    {
        assert(x >= m);
    }

    proof fn lemma_sum_rest_ge_5(n: int, sum_rest: int)
        requires sum_rest == n - 3, sum_rest >= 2,
        ensures n >= 5,
    {
        assert(n >= 5) by (nonlinear_arith) requires sum_rest == n - 3, sum_rest >= 2 {}
    }

    proof fn lemma_seq_sum_min(s: Seq<int>, m: nat)
        requires
            s.len() >= m,
            forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1,
        ensures Self::seq_sum(s) >= m,
        decreases m,
    {
        if m == 0 {
            Self::lemma_seq_sum_nonneg(s);
        } else {
            Self::lemma_seq_unfold_sum(s);
            let rest = s.subrange(1, s.len() as int);
            Self::lemma_seq_sum_min(rest, (m - 1) as nat);
            assert(s[0] >= 1);
            assert(Self::seq_sum(s) == s[0] + Self::seq_sum(rest));
            assert(Self::seq_sum(rest) >= m - 1);
            assert(s[0] + Self::seq_sum(rest) >= m) by (nonlinear_arith)
                requires s[0] >= 1, Self::seq_sum(rest) >= m - 1, m >= 1 {}
            Self::lemma_ge_eq(Self::seq_sum(s), s[0] + Self::seq_sum(rest), m as int);
            Self::lemma_nat_int_ge(Self::seq_sum(s), m);
            assert(Self::seq_sum(s) >= m);
        }
    }

    proof fn lemma_seq_sum_append(s1: Seq<int>, s2: Seq<int>)
        ensures Self::seq_sum(s1 + s2) == Self::seq_sum(s1) + Self::seq_sum(s2),
        decreases s1.len(),
    {
        if s1.len() == 0 {
            assert(s1 + s2 =~= s2);
        } else {
            let rest = s1.subrange(1, s1.len() as int);
            assert((s1 + s2).subrange(1, (s1 + s2).len() as int) =~= rest + s2);
            Self::lemma_seq_sum_append(rest, s2);
        }
    }

    proof fn lemma_seq_product_same(s: Seq<int>, t: Seq<int>)
        requires s =~= t,
        ensures Self::seq_product(s) == Self::seq_product(t),
        decreases s.len(),
    {
        if s.len() == 0 {
            reveal_with_fuel(Solution::seq_product, 2);
        } else {
            Self::lemma_seq_unfold_product(s);
            Self::lemma_seq_unfold_product(t);
            assert(s[0] == t[0]);
            assert(s.subrange(1, s.len() as int) =~= t.subrange(1, t.len() as int));
            Self::lemma_seq_product_same(s.subrange(1, s.len() as int), t.subrange(1, t.len() as int));
        }
    }

    proof fn lemma_seq_product_append(s1: Seq<int>, s2: Seq<int>)
        ensures Self::seq_product(s1 + s2) == Self::seq_product(s1) * Self::seq_product(s2),
        decreases s1.len(),
    {
        if s1.len() == 0 {
            assert(s1 + s2 =~= s2);
            reveal_with_fuel(Solution::seq_product, 2);
        } else {
            let rest = s1.subrange(1, s1.len() as int);
            assert((s1 + s2)[0] == s1[0]);
            assert((s1 + s2).subrange(1, (s1 + s2).len() as int) =~= rest + s2);
            Self::lemma_seq_unfold_product(s1 + s2);
            Self::lemma_seq_product_same((s1 + s2).subrange(1, (s1 + s2).len() as int), rest + s2);
            Self::lemma_seq_product_append(rest, s2);
            Self::lemma_seq_unfold_product(s1);
            assert(Self::seq_product((s1 + s2).subrange(1, (s1 + s2).len() as int)) == Self::seq_product(rest + s2));
            assert(Self::seq_product(s1 + s2) == (s1 + s2)[0] * Self::seq_product(rest + s2));
            assert(Self::seq_product(rest + s2) == Self::seq_product(rest) * Self::seq_product(s2));
            assert((s1 + s2)[0] * Self::seq_product(rest + s2) == (s1 + s2)[0] * Self::seq_product(rest) * Self::seq_product(s2)) by (nonlinear_arith)
                requires Self::seq_product(rest + s2) == Self::seq_product(rest) * Self::seq_product(s2) {}
            assert(Self::seq_product(s1 + s2) == (s1 + s2)[0] * Self::seq_product(rest) * Self::seq_product(s2));
            assert((s1 + s2)[0] == s1[0]);
            assert((s1 + s2)[0] * Self::seq_product(rest) * Self::seq_product(s2) == Self::seq_product(s1) * Self::seq_product(s2));
            assert(Self::seq_product(s1 + s2) == Self::seq_product(s1) * Self::seq_product(s2));
            assert(Self::seq_product(s1) == s1[0] * Self::seq_product(rest));
            assert(s1 + s2 =~= s1.add(s2));
            Self::lemma_seq_product_same(s1 + s2, s1.add(s2));
            assert(Self::seq_product(s1.add(s2)) == Self::seq_product(s1) * Self::seq_product(s2));
        }
    }

    proof fn lemma_product_positive(s: Seq<int>)
        requires forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1,
        ensures Self::seq_product(s) >= 1,
        decreases s.len(),
    {
        if s.len() > 0 {
            let rest = s.subrange(1, s.len() as int);
            assert(forall |i: int| 0 <= i < rest.len() ==> #[trigger] rest[i] == s[i + 1]);
            Self::lemma_product_positive(rest);
            assert(s[0] >= 1 && Self::seq_product(rest) >= 1);
            assert(s[0] * Self::seq_product(rest) >= 1) by (nonlinear_arith)
                requires s[0] >= 1, Self::seq_product(rest) >= 1,
            {}
        }
    }

    proof fn lemma_threes_sum(q: nat)
        requires q >= 1,
        ensures Self::seq_sum(Seq::new(q as nat, |_i: int| 3int)) == 3 * q,
        decreases q,
    {
        let s = Seq::new(q as nat, |_i: int| 3int);
        if q == 1 {
            Self::lemma_seq_sum_1(s);
        } else {
            let rest = Seq::new((q - 1) as nat, |_i: int| 3int);
            assert(s.subrange(1, s.len() as int) =~= rest);
            assert(s[0] == 3);
            Self::lemma_seq_unfold_sum(s);
            Self::lemma_threes_sum((q - 1) as nat);
            assert(Self::seq_sum(rest) == 3 * (q - 1));
            assert(3 + 3 * (q - 1) == 3 * q) by (nonlinear_arith) requires q >= 1 {};
        }
    }

    proof fn lemma_threes_product(q: nat)
        requires q >= 1,
        ensures Self::seq_product(Seq::new(q as nat, |_i: int| 3int)) == Self::pow3(q),
        decreases q,
    {
        let s = Seq::new(q as nat, |_i: int| 3int);
        if q == 1 {
            Self::lemma_seq_product_1(s);
            Self::lemma_pow3_concrete();
        } else {
            let rest = Seq::new((q - 1) as nat, |_i: int| 3int);
            assert(s.subrange(1, s.len() as int) =~= rest);
            assert(s[0] == 3);
            Self::lemma_seq_unfold_product(s);
            Self::lemma_threes_product((q - 1) as nat);
            Self::lemma_pow3_step((q - 1) as nat);
            assert(Self::seq_product(s) == 3 * Self::pow3((q - 1) as nat));
            assert(3 * Self::pow3((q - 1) as nat) == Self::pow3(q));
        }
    }

    proof fn lemma_spec_integer_break_2()
        ensures Self::spec_integer_break(2) == 1,
    {}

    proof fn lemma_spec_integer_break_3()
        ensures Self::spec_integer_break(3) == 2,
    {}

    proof fn lemma_spec_integer_break_4()
        ensures Self::spec_integer_break(4) == 4,
    {}

    proof fn lemma_spec_integer_break_3q1(q: int)
        requires q >= 2, 3 * q + 1 <= 58,
        ensures Self::spec_integer_break(3 * q + 1) == Self::pow3((q - 1) as nat) * 4,
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_witness_exists(n: int)
        requires 2 <= n <= 58,
        ensures
            exists |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n)
                && Self::seq_product(s) == Self::spec_integer_break(n),
    {
        Self::lemma_pow3_concrete();
        if n == 2 {
            let s = seq![1int, 1int];
            assert(s[0] == 1 && s[1] == 1);
            Self::lemma_seq_sum_2(s);
            Self::lemma_seq_product_2(s);
            Self::lemma_spec_integer_break_2();
            assert(Self::is_valid_partition(s, 2));
            assert(Self::seq_product(s) == Self::spec_integer_break(2));
        } else if n == 3 {
            let s = seq![1int, 2int];
            assert(s[0] == 1 && s[1] == 2);
            Self::lemma_seq_sum_2(s);
            Self::lemma_seq_product_2(s);
            Self::lemma_spec_integer_break_3();
            assert(Self::is_valid_partition(s, 3));
            assert(Self::seq_product(s) == Self::spec_integer_break(3));
        } else {
            let q = n / 3;
            let r = n % 3;
            if r == 0 {
                assert(q >= 2);
                let s = Seq::new(q as nat, |_i: int| 3int);
                Self::lemma_threes_sum(q as nat);
                Self::lemma_threes_product(q as nat);
                assert(Self::is_valid_partition(s, n));
                assert(Self::seq_product(s) == Self::spec_integer_break(n));
            } else if r == 1 {
                if q == 1 {
                    assert(n == 4);
                    let s = seq![2int, 2int];
                    Self::lemma_seq_sum_2(s);
                    Self::lemma_seq_product_2(s);
                    assert(Self::is_valid_partition(s, 4));
                    assert(Self::seq_product(s) == Self::spec_integer_break(4));
                } else {
                    let threes = Seq::new((q - 1) as nat, |_i: int| 3int);
                    let tail = seq![2int, 2int];
                    let s = threes + tail;
                    Self::lemma_threes_sum((q - 1) as nat);
                    Self::lemma_threes_product((q - 1) as nat);
                    Self::lemma_seq_sum_append(threes, tail);
                    Self::lemma_seq_sum_2(tail);
                    Self::lemma_seq_product_append(threes, tail);
                    Self::lemma_seq_product_2(tail);
                    assert(forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1) by {
                        assert(forall |i: int| 0 <= i < threes.len() ==> #[trigger] threes[i] == 3);
                    }
                    assert(n == 3 * q + 1);
                    Self::lemma_spec_integer_break_3q1(q);
                    assert(tail[0] == 2 && tail[1] == 2);
                    assert(tail[0] * tail[1] == 4) by (nonlinear_arith) requires tail[0] == 2, tail[1] == 2 {}
                    assert(Self::seq_product(threes) == Self::pow3((q - 1) as nat));
                    assert(Self::seq_product(tail) == 4);
                    assert(Self::seq_product(s) == Self::seq_product(threes) * Self::seq_product(tail));
                    assert(Self::seq_product(s) == Self::pow3((q - 1) as nat) * 4);
                    assert(Self::is_valid_partition(s, n));
                    assert(Self::seq_product(s) == Self::spec_integer_break(n));
                }
            } else {
                let threes = Seq::new(q as nat, |_i: int| 3int);
                let tail = seq![2int];
                let s = threes + tail;
                Self::lemma_threes_sum(q as nat);
                Self::lemma_threes_product(q as nat);
                Self::lemma_seq_sum_append(threes, tail);
                Self::lemma_seq_sum_1(tail);
                Self::lemma_seq_product_append(threes, tail);
                Self::lemma_seq_product_1(tail);
                assert(forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1) by {
                    assert(forall |i: int| 0 <= i < threes.len() ==> #[trigger] threes[i] == 3);
                }
                assert(Self::is_valid_partition(s, n));
                assert(Self::seq_product(s) == Self::spec_integer_break(n));
            }
        }
    }

    proof fn lemma_spec_lower_bound(n: int)
        requires 2 <= n <= 58,
        ensures Self::spec_integer_break(n) >= (n * n) / 4,
    {
        Self::lemma_pow3_concrete();
        if n == 2 {
            Self::lemma_spec_integer_break_2();
        } else if n == 3 {
            Self::lemma_spec_integer_break_3();
        } else if n == 4 {
            Self::lemma_spec_integer_break_4();
        } else if n == 5 {
        } else if n == 6 {
        } else if n == 7 {
        } else if n == 8 {
        } else if n == 9 {
        } else if n == 10 {
        } else if n == 11 {
        } else if n == 12 {
        } else if n == 13 {
        } else if n == 14 {
        } else if n == 15 {
        } else if n == 16 {
        } else if n == 17 {
        } else if n == 18 {
        } else if n == 19 {
        } else if n == 20 {
        } else if n == 21 {
        } else if n == 22 {
        } else if n == 23 {
        } else if n == 24 {
        } else if n == 25 {
        } else if n == 26 {
        } else if n == 27 {
        } else if n == 28 {
        } else if n == 29 {
        } else if n == 30 {
        } else if n == 31 {
        } else if n == 32 {
        } else if n == 33 {
        } else if n == 34 {
        } else if n == 35 {
        } else if n == 36 {
        } else if n == 37 {
        } else if n == 38 {
        } else if n == 39 {
        } else if n == 40 {
        } else if n == 41 {
        } else if n == 42 {
        } else if n == 43 {
        } else if n == 44 {
        } else if n == 45 {
        } else if n == 46 {
        } else if n == 47 {
        } else if n == 48 {
        } else if n == 49 {
        } else if n == 50 {
        } else if n == 51 {
        } else if n == 52 {
        } else if n == 53 {
        } else if n == 54 {
        } else if n == 55 {
        } else if n == 56 {
        } else if n == 57 {
        } else {
            assert(n == 58);
        }
        assert(Self::spec_integer_break(n) >= (n * n) / 4);
    }

    proof fn lemma_spec_monotone(a: int, b: int)
        requires 2 <= a < b <= 58,
        ensures Self::spec_integer_break(a) <= Self::spec_integer_break(b),
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_factor_2_bound(n: int)
        requires 4 <= n <= 58,
        ensures 2 * Self::spec_integer_break(n - 2) <= Self::spec_integer_break(n),
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_factor_3_bound(n: int)
        requires 5 <= n <= 58,
        ensures 3 * Self::spec_integer_break(n - 3) <= Self::spec_integer_break(n),
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_factor_4_bound(n: int)
        requires 6 <= n <= 58,
        ensures 4 * Self::spec_integer_break(n - 4) <= Self::spec_integer_break(n),
    {
        Self::lemma_pow3_concrete();
    }

    proof fn lemma_product_upper_bound(s: Seq<int>, n: int)
        requires
            2 <= n <= 58,
            Self::is_valid_partition(s, n),
        ensures
            Self::seq_product(s) <= Self::spec_integer_break(n),
        decreases n, s.len(),
    {
        Self::lemma_pow3_concrete();
        Self::lemma_product_positive(s);

        if s.len() == 2 {
            Self::lemma_seq_product_2(s);
            Self::lemma_seq_sum_2(s);
            let a = s[0];
            let b = s[1];
            assert(a * b <= (n * n) / 4) by (nonlinear_arith)
                requires a >= 1, b >= 1, a + b == n {}
            Self::lemma_spec_lower_bound(n);
        } else {
            let a = s[0];
            let rest = s.subrange(1, s.len() as int);
            assert(forall |i: int| 0 <= i < rest.len() ==> #[trigger] rest[i] == s[i + 1]);
            assert(Self::seq_sum(rest) == n - a);
            assert(rest.len() >= 2);
            Self::lemma_product_positive(rest);

            if a == 1 {
                assert(s.len() >= 3);
                Self::lemma_seq_sum_min(s, 3);
                assert(n >= 3);
                assert(s =~= seq![1int] + rest);
                Self::lemma_seq_product_prepend(1, rest);
                assert(Self::seq_product(seq![1int] + rest) == 1 * Self::seq_product(rest));
                assert(s =~= seq![1int] + rest);
                assert(Self::seq_product(s) == Self::seq_product(rest));
                assert(Self::is_valid_partition(rest, n - 1));
                Self::lemma_product_upper_bound(rest, n - 1);
                Self::lemma_spec_monotone(n - 1, n);
            } else if a == 2 {
                assert(rest.len() >= 2);
                Self::lemma_seq_sum_min(rest, 2);
                assert(n >= 4);
                assert(Self::is_valid_partition(rest, n - 2));
                Self::lemma_product_upper_bound(rest, n - 2);
                assert(Self::seq_product(s) == 2 * Self::seq_product(rest));
                Self::lemma_factor_2_bound(n);
            } else if a == 3 {
                assert(rest.len() >= 2);
                Self::lemma_seq_sum_min(rest, 2);
                assert(Self::seq_sum(rest) == n - 3);
                Self::lemma_sum_rest_ge_5(n, Self::seq_sum(rest));
                assert(Self::is_valid_partition(rest, n - 3));
                Self::lemma_product_upper_bound(rest, n - 3);
                assert(Self::seq_product(s) == 3 * Self::seq_product(rest));
                Self::lemma_factor_3_bound(n);
            } else if a == 4 {
                assert(rest.len() >= 2);
                Self::lemma_seq_sum_min(rest, 2);
                assert(n >= 6);
                assert(Self::is_valid_partition(rest, n - 4));
                Self::lemma_product_upper_bound(rest, n - 4);
                assert(Self::seq_product(s) == 4 * Self::seq_product(rest));
                Self::lemma_factor_4_bound(n);
            } else {
                assert(a >= 5);
                Self::lemma_seq_sum_nonneg(rest);
                assert(n >= 5) by (nonlinear_arith)
                    requires a >= 5, Self::seq_sum(rest) == n - a, Self::seq_sum(rest) >= 0 {}
                let inner = seq![a - 3] + rest;
                let new_s = seq![3int] + inner;
                Self::lemma_seq_sum_prepend(a - 3, rest);
                Self::lemma_seq_sum_prepend(3, inner);
                assert(Self::seq_sum(new_s) == 3 + (a - 3) + Self::seq_sum(rest) == n);
                assert(forall |i: int| 0 <= i < new_s.len() ==> #[trigger] new_s[i] >= 1) by {
                    assert(new_s[0] == 3);
                    assert(inner[0] == a - 3 >= 1);
                    assert(forall |i: int| 1 <= i < inner.len() ==> inner[i] == #[trigger] rest[i - 1]);
                }
                assert(Self::is_valid_partition(new_s, n));

                Self::lemma_seq_product_prepend(a - 3, rest);
                Self::lemma_seq_product_prepend(3, inner);
                assert(Self::seq_product(new_s) == 3 * ((a - 3) * Self::seq_product(rest)));
                assert(Self::seq_product(s) == a * Self::seq_product(rest));
                assert(Self::seq_product(s) <= Self::seq_product(new_s)) by (nonlinear_arith)
                    requires
                        Self::seq_product(s) == a * Self::seq_product(rest),
                        Self::seq_product(new_s) == 3 * ((a - 3) * Self::seq_product(rest)),
                        a >= 5,
                        Self::seq_product(rest) >= 1,
                {}
                assert(Self::is_valid_partition(inner, n - 3));
                Self::lemma_product_upper_bound(inner, n - 3);
                Self::lemma_factor_3_bound(n);
                assert(3 * Self::seq_product(inner) <= Self::spec_integer_break(n));
                assert(Self::seq_product(new_s) == 3 * Self::seq_product(inner));
                assert(Self::seq_product(s) <= Self::spec_integer_break(n));
            }
        }
    }

    proof fn lemma_maximality(n: int)
        requires 2 <= n <= 58,
        ensures
            forall |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n)
                ==> Self::seq_product(s) <= Self::spec_integer_break(n),
    {
        assert forall |s: Seq<int>| #[trigger] Self::is_valid_partition(s, n)
            implies Self::seq_product(s) <= Self::spec_integer_break(n) by {
            Self::lemma_product_upper_bound(s, n);
        }
    }

    pub fn integer_break(n: i32) -> (result: i32)
        requires
            2 <= n <= 58,
        ensures
            result >= 1,
            exists |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n as int)
                && Self::seq_product(s) == result as int,
            forall |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n as int)
                ==> Self::seq_product(s) <= result as int,
    {
        if n == 2 {
            proof {
                Self::lemma_witness_exists(2);
                Self::lemma_maximality(2);
            }
            return 1;
        }
        if n == 3 {
            proof {
                Self::lemma_witness_exists(3);
                Self::lemma_maximality(3);
            }
            return 2;
        }
        let q = n / 3;
        let r = n % 3;
        let mut p: i32 = 1;
        let mut i: i32 = 0;

        if r == 0 {
            while i < q
                invariant
                    0 <= i <= q <= 19,
                    p as int == Self::pow3(i as nat),
                    0 < p as int <= 1_162_261_467,
                decreases q - i,
            {
                proof { if i < 19 { Self::lemma_pow3_bound_18(i as nat); } }
                p = p * 3;
                i += 1;
                proof {
                    Self::lemma_pow3_step((i - 1) as nat);
                    Self::lemma_pow3_bound_19(i as nat);
                }
            }
            proof {
                assert(p as int == Self::spec_integer_break(n as int));
                Self::lemma_witness_exists(n as int);
                Self::lemma_maximality(n as int);
            }
            p
        } else if r == 1 {
            while i < q - 1
                invariant
                    0 <= i <= q - 1 <= 18,
                    p as int == Self::pow3(i as nat),
                    0 < p as int <= 387_420_489,
                decreases q - 1 - i,
            {
                proof { if i < 18 { Self::lemma_pow3_bound_18(i as nat); } }
                p = p * 3;
                i += 1;
                proof {
                    Self::lemma_pow3_step((i - 1) as nat);
                    Self::lemma_pow3_bound_18(i as nat);
                }
            }
            proof {
                assert((p * 4) as int == Self::spec_integer_break(n as int));
                Self::lemma_witness_exists(n as int);
                Self::lemma_maximality(n as int);
            }
            p * 4
        } else {
            while i < q
                invariant
                    0 <= i <= q <= 18,
                    p as int == Self::pow3(i as nat),
                    0 < p as int <= 387_420_489,
                decreases q - i,
            {
                proof { if i < 18 { Self::lemma_pow3_bound_18(i as nat); } }
                p = p * 3;
                i += 1;
                proof {
                    Self::lemma_pow3_step((i - 1) as nat);
                    Self::lemma_pow3_bound_18(i as nat);
                }
            }
            proof {
                assert((p * 2) as int == Self::spec_integer_break(n as int));
                Self::lemma_witness_exists(n as int);
                Self::lemma_maximality(n as int);
            }
            p * 2
        }
    }
}

}
