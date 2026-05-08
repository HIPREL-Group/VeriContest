use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn coeffs_valid(coeffs: Seq<int>) -> bool {
        forall |i: int| 0 <= i < coeffs.len() ==> -1 <= #[trigger] coeffs[i] <= 1
    }

    pub open spec fn weighted_sum_of_powers(w: int, coeffs: Seq<int>) -> int
        recommends
            2 <= w,
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            0
        } else {
            coeffs[0] + w * Self::weighted_sum_of_powers(w, coeffs.subrange(1, coeffs.len() as int))
        }
    }

    pub open spec fn pow2(exp: int) -> int
        recommends
            0 <= exp,
        decreases exp,
    {
        if exp <= 0 {
            1
        } else {
            2 * Self::pow2(exp - 1)
        }
    }

    pub open spec fn exists_representation(w: int, m: int, digits: int) -> bool
        recommends
            2 <= w,
            0 <= digits,
    {
        exists |coeffs: Seq<int>| coeffs.len() <= digits
            && Self::coeffs_valid(coeffs)
            && Self::weighted_sum_of_powers(w, coeffs) == m
    }

    pub open spec fn balanced_representable_recursive(w: int, m: int, digits: int) -> bool
        recommends
            2 <= w,
            0 <= m,
            0 <= digits,
        decreases digits,
    {
        if digits <= 0 {
            m == 0
        } else if m == 0 {
            true
        } else {
            let r = m % w;
            (r == 0 && Self::balanced_representable_recursive(w, m / w, digits - 1))
                || (r == 1 && Self::balanced_representable_recursive(w, (m - 1) / w, digits - 1))
                || (r + 1 == w && Self::balanced_representable_recursive(w, (m + 1) / w, digits - 1))
        }
    }

    proof fn lemma_weighted_sum_of_powers_cons(w: int, d: int, tail: Seq<int>)
        requires
            2 <= w,
        ensures
            Self::weighted_sum_of_powers(w, seq![d] + tail) == d + w * Self::weighted_sum_of_powers(w, tail),
    {
        reveal_with_fuel(Solution::weighted_sum_of_powers, 2);
        assert((seq![d] + tail)[0] == d);
        assert((seq![d] + tail).subrange(1, (seq![d] + tail).len() as int) == tail);
    }

    proof fn lemma_recursive_two(m: int, digits: int)
        requires
            0 <= m,
            0 <= digits,
            m < Self::pow2(digits),
        ensures
            Self::balanced_representable_recursive(2, m, digits),
        decreases digits,
    {
        if digits == 0 {
            assert(m == 0);
        } else if m == 0 {
            reveal_with_fuel(Solution::balanced_representable_recursive, 2);
        } else {
            reveal_with_fuel(Solution::pow2, 2);
            if m % 2 == 0 {
                assert(m / 2 < Self::pow2(digits - 1)) by (nonlinear_arith)
                    requires
                        1 <= digits,
                        0 < m,
                        m < 2 * Self::pow2(digits - 1),
                        m % 2 == 0;
                Self::lemma_recursive_two(m / 2, digits - 1);
            } else {
                assert((m - 1) / 2 < Self::pow2(digits - 1)) by (nonlinear_arith)
                    requires
                        1 <= digits,
                        0 < m,
                        m < 2 * Self::pow2(digits - 1),
                        m % 2 == 1;
                Self::lemma_recursive_two((m - 1) / 2, digits - 1);
            }
            reveal_with_fuel(Solution::balanced_representable_recursive, 2);
        }
    }

    proof fn lemma_exists_implies_recursive(w: int, m: int, digits: int)
        requires
            2 <= w,
            0 <= m,
            0 <= digits,
            Self::exists_representation(w, m, digits),
        ensures
            Self::balanced_representable_recursive(w, m, digits),
        decreases digits,
    {
        if digits == 0 {
            let coeffs = choose |coeffs: Seq<int>| coeffs.len() <= digits
                && Self::coeffs_valid(coeffs)
                && Self::weighted_sum_of_powers(w, coeffs) == m;
            assert(coeffs.len() == 0);
            reveal_with_fuel(Solution::weighted_sum_of_powers, 2);
            assert(m == 0);
        } else if m == 0 {
            reveal_with_fuel(Solution::balanced_representable_recursive, 2);
        } else {
            let coeffs = choose |coeffs: Seq<int>| coeffs.len() <= digits
                && Self::coeffs_valid(coeffs)
                && Self::weighted_sum_of_powers(w, coeffs) == m;
            assert(coeffs.len() > 0) by {
                if coeffs.len() == 0 {
                    reveal_with_fuel(Solution::weighted_sum_of_powers, 2);
                    assert(Self::weighted_sum_of_powers(w, coeffs) == 0);
                    assert(false);
                }
            }
            let d = coeffs[0];
            let tail = coeffs.subrange(1, coeffs.len() as int);
            let tail_sum = Self::weighted_sum_of_powers(w, tail);
            Self::lemma_weighted_sum_of_powers_cons(w, d, tail);
            assert(Self::weighted_sum_of_powers(w, coeffs) == d + w * tail_sum);
            assert(coeffs == seq![d] + tail);
            assert(tail.len() <= digits - 1) by (nonlinear_arith)
                requires
                    coeffs.len() <= digits,
                    coeffs.len() > 0,
                    tail.len() == coeffs.len() - 1;
            assert(Self::coeffs_valid(tail)) by {
                assert forall |i: int| 0 <= i < tail.len() implies -1 <= #[trigger] tail[i] <= 1 by {
                    assert(tail[i] == coeffs[i + 1]);
                }
            }
            assert(-1 <= d <= 1);
            if d == 0 {
                assert(m == w * tail_sum);
                assert(m / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == w * tail_sum;
                assert(Self::exists_representation(w, m / w, digits - 1)) by {
                }
                Self::lemma_exists_implies_recursive(w, m / w, digits - 1);
                assert(m % w == 0) by (nonlinear_arith)
                    requires
                        2 <= w,
                        m == w * tail_sum;
                assert(m / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == w * tail_sum;
                reveal_with_fuel(Solution::balanced_representable_recursive, 2);
            } else if d == 1 {
                assert(m == 1 + w * tail_sum);
                assert((m - 1) / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == 1 + w * tail_sum;
                assert(Self::exists_representation(w, (m - 1) / w, digits - 1)) by {
                }
                Self::lemma_exists_implies_recursive(w, (m - 1) / w, digits - 1);
                assert(m % w == 1) by (nonlinear_arith)
                    requires
                        2 <= w,
                        m == 1 + w * tail_sum;
                assert((m - 1) / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == 1 + w * tail_sum;
                reveal_with_fuel(Solution::balanced_representable_recursive, 2);
            } else {
                assert(d == -1);
                assert(m == -1 + w * tail_sum);
                assert(1 <= tail_sum) by (nonlinear_arith)
                    requires
                        2 <= w,
                        0 < m,
                        m == -1 + w * tail_sum;
                assert((m + 1) / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == -1 + w * tail_sum;
                assert(Self::exists_representation(w, (m + 1) / w, digits - 1)) by {
                }
                Self::lemma_exists_implies_recursive(w, (m + 1) / w, digits - 1);
                assert(m % w + 1 == w) by (nonlinear_arith)
                    requires
                        2 <= w,
                        1 <= tail_sum,
                        m == -1 + w * tail_sum;
                assert((m + 1) / w == tail_sum) by (nonlinear_arith)
                    requires
                        1 <= w,
                        m == -1 + w * tail_sum;
                reveal_with_fuel(Solution::balanced_representable_recursive, 2);
            }
        }
    }

    proof fn lemma_recursive_implies_exists(w: int, m: int, digits: int)
        requires
            2 <= w,
            0 <= m,
            0 <= digits,
            Self::balanced_representable_recursive(w, m, digits),
        ensures
            Self::exists_representation(w, m, digits),
        decreases digits,
    {
        if digits == 0 {
            assert(m == 0);
            assert(Self::exists_representation(w, m, digits)) by {
                let coeffs = Seq::<int>::empty();
                assert(coeffs.len() <= digits);
                assert(Self::coeffs_valid(coeffs));
                reveal_with_fuel(Solution::weighted_sum_of_powers, 2);
            }
        } else if m == 0 {
            assert(Self::exists_representation(w, m, digits)) by {
                let coeffs = Seq::<int>::empty();
                assert(coeffs.len() <= digits);
                assert(Self::coeffs_valid(coeffs));
                reveal_with_fuel(Solution::weighted_sum_of_powers, 2);
            }
        } else {
            reveal_with_fuel(Solution::balanced_representable_recursive, 2);
            let r = m % w;
            if r == 0 && Self::balanced_representable_recursive(w, m / w, digits - 1) {
                Self::lemma_recursive_implies_exists(w, m / w, digits - 1);
                let tail = choose |coeffs: Seq<int>| coeffs.len() <= digits - 1
                    && Self::coeffs_valid(coeffs)
                    && Self::weighted_sum_of_powers(w, coeffs) == m / w;
                let coeffs = seq![0int] + tail;
                Self::lemma_weighted_sum_of_powers_cons(w, 0, tail);
                assert(coeffs.len() <= digits) by (nonlinear_arith)
                    requires
                        tail.len() <= digits - 1,
                        1 <= digits,
                        coeffs.len() == tail.len() + 1;
                assert(Self::coeffs_valid(coeffs)) by {
                    assert forall |i: int| 0 <= i < coeffs.len() implies -1 <= #[trigger] coeffs[i] <= 1 by {
                        if i == 0 {
                        } else {
                            assert(coeffs[i] == tail[i - 1]);
                        }
                    }
                }
                assert(Self::weighted_sum_of_powers(w, coeffs) == m) by {
                    assert(Self::weighted_sum_of_powers(w, tail) == m / w);
                    assert(m % w == 0);
                    assert(m == w * (m / w)) by (nonlinear_arith)
                        requires
                            2 <= w,
                            m % w == 0;
                }
                assert(Self::exists_representation(w, m, digits));
            } else if r == 1 && Self::balanced_representable_recursive(w, (m - 1) / w, digits - 1) {
                Self::lemma_recursive_implies_exists(w, (m - 1) / w, digits - 1);
                let tail = choose |coeffs: Seq<int>| coeffs.len() <= digits - 1
                    && Self::coeffs_valid(coeffs)
                    && Self::weighted_sum_of_powers(w, coeffs) == (m - 1) / w;
                let coeffs = seq![1int] + tail;
                Self::lemma_weighted_sum_of_powers_cons(w, 1, tail);
                assert(coeffs.len() <= digits) by (nonlinear_arith)
                    requires
                        tail.len() <= digits - 1,
                        1 <= digits,
                        coeffs.len() == tail.len() + 1;
                assert(Self::coeffs_valid(coeffs)) by {
                    assert forall |i: int| 0 <= i < coeffs.len() implies -1 <= #[trigger] coeffs[i] <= 1 by {
                        if i == 0 {
                        } else {
                            assert(coeffs[i] == tail[i - 1]);
                        }
                    }
                }
                assert(Self::weighted_sum_of_powers(w, coeffs) == m) by {
                    assert(Self::weighted_sum_of_powers(w, tail) == (m - 1) / w);
                    assert(m % w == 1);
                    assert((m - 1) % w == 0) by (nonlinear_arith)
                        requires
                            2 <= w,
                            m % w == 1;
                    assert(m == 1 + w * ((m - 1) / w)) by (nonlinear_arith)
                        requires
                            2 <= w,
                            (m - 1) % w == 0;
                }
                assert(Self::exists_representation(w, m, digits));
            } else {
                assert(r + 1 == w);
                assert(Self::balanced_representable_recursive(w, (m + 1) / w, digits - 1));
                Self::lemma_recursive_implies_exists(w, (m + 1) / w, digits - 1);
                let tail = choose |coeffs: Seq<int>| coeffs.len() <= digits - 1
                    && Self::coeffs_valid(coeffs)
                    && Self::weighted_sum_of_powers(w, coeffs) == (m + 1) / w;
                let coeffs = seq![-1int] + tail;
                Self::lemma_weighted_sum_of_powers_cons(w, -1, tail);
                assert(coeffs.len() <= digits) by (nonlinear_arith)
                    requires
                        tail.len() <= digits - 1,
                        1 <= digits,
                        coeffs.len() == tail.len() + 1;
                assert(Self::coeffs_valid(coeffs)) by {
                    assert forall |i: int| 0 <= i < coeffs.len() implies -1 <= #[trigger] coeffs[i] <= 1 by {
                        if i == 0 {
                        } else {
                            assert(coeffs[i] == tail[i - 1]);
                        }
                    }
                }
                assert(Self::weighted_sum_of_powers(w, coeffs) == m) by {
                    assert(Self::weighted_sum_of_powers(w, tail) == (m + 1) / w);
                    assert(r + 1 == w);
                    assert((m + 1) % w == 0) by (nonlinear_arith)
                        requires
                            2 <= w,
                            r + 1 == w,
                            r == m % w;
                    assert(m == -1 + w * ((m + 1) / w)) by (nonlinear_arith)
                        requires
                            2 <= w,
                            (m + 1) % w == 0;
                }
                assert(Self::exists_representation(w, m, digits));
            }
        }
    }

    proof fn lemma_recursive_equiv_exists(w: int, m: int, digits: int)
        requires
            2 <= w,
            0 <= m,
            0 <= digits,
        ensures
            Self::balanced_representable_recursive(w, m, digits) == Self::exists_representation(w, m, digits),
    {
        if Self::balanced_representable_recursive(w, m, digits) {
            Self::lemma_recursive_implies_exists(w, m, digits);
        } else if Self::exists_representation(w, m, digits) {
            Self::lemma_exists_implies_recursive(w, m, digits);
            assert(false);
        }
    }

    pub fn can_balance(w: i64, m: i64) -> (result: bool)
        requires
            2 <= w <= 1_000_000_000,
            1 <= m <= 1_000_000_000,
        ensures
            result == Self::exists_representation(w as int, m as int, 31),
    {
        if w == 2 {
            proof {
                assert((m as int) < 2_147_483_648);
                assert(2_147_483_648 == Self::pow2(31)) by (compute);
                Self::lemma_recursive_two(m as int, 31);
                Self::lemma_recursive_equiv_exists(2, m as int, 31);
            }
            return true;
        }
        proof {
            assert(3 <= w);
            assert(0 <= m as int);
            Self::lemma_recursive_equiv_exists(w as int, m as int, 31);
        }
        let mut current = m;
        let mut digits_left: i64 = 31;
        while current > 0 && digits_left > 0
            invariant
                3 <= w <= 1_000_000_000,
                1 <= m <= 1_000_000_000,
                0 <= current <= 1_000_000_000,
                0 <= digits_left <= 31,
                Self::balanced_representable_recursive(w as int, current as int, digits_left as int)
                    == Self::balanced_representable_recursive(w as int, m as int, 31),
            decreases digits_left,
        {
            let prev_current = current;
            let prev_digits_left = digits_left;
            let rem = current % w;
            if rem == 0 {
                proof {
                    reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                    assert(Self::balanced_representable_recursive(w as int, prev_current as int, prev_digits_left as int)
                        == Self::balanced_representable_recursive(w as int, (prev_current as int) / (w as int), (prev_digits_left - 1) as int));
                }
                assert(0 <= current / w);
                assert(current / w <= current) by (nonlinear_arith)
                    requires
                        1 <= w,
                        0 <= current;
                current = current / w;
                digits_left = digits_left - 1;
            } else if rem == 1 {
                proof {
                    reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                    assert(Self::balanced_representable_recursive(w as int, prev_current as int, prev_digits_left as int)
                        == Self::balanced_representable_recursive(w as int, ((prev_current as int) - 1) / (w as int), (prev_digits_left - 1) as int));
                }
                assert(0 <= ((current as int) - 1) / (w as int));
                assert((((current as int) - 1) / (w as int)) <= current as int) by (nonlinear_arith)
                    requires
                        1 <= w,
                        1 <= current;
                current = (current - 1) / w;
                digits_left = digits_left - 1;
            } else if rem + 1 == w {
                proof {
                    reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                    assert(Self::balanced_representable_recursive(w as int, prev_current as int, prev_digits_left as int)
                        == Self::balanced_representable_recursive(w as int, ((prev_current as int) + 1) / (w as int), (prev_digits_left - 1) as int));
                }
                assert(current + 1 <= 1_000_000_001);
                assert(0 <= ((current as int) + 1) / (w as int));
                assert((((current as int) + 1) / (w as int)) <= current as int) by (nonlinear_arith)
                    requires
                        3 <= w,
                        1 <= current;
                current = (current + 1) / w;
                digits_left = digits_left - 1;
            } else {
                proof {
                    reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                    assert(!Self::balanced_representable_recursive(w as int, prev_current as int, prev_digits_left as int));
                    assert(!Self::balanced_representable_recursive(w as int, m as int, 31));
                    Self::lemma_recursive_equiv_exists(w as int, m as int, 31);
                }
                return false;
            }
        }
        proof {
            if current == 0 {
                reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                assert(Self::balanced_representable_recursive(w as int, current as int, digits_left as int));
            } else {
                assert(digits_left == 0);
                reveal_with_fuel(Solution::balanced_representable_recursive, 2);
                assert(!Self::balanced_representable_recursive(w as int, current as int, digits_left as int));
            }
            assert(Self::balanced_representable_recursive(w as int, m as int, 31)
                == Self::balanced_representable_recursive(w as int, current as int, digits_left as int));
            Self::lemma_recursive_equiv_exists(w as int, m as int, 31);
        }
        current == 0
    }
}

}
