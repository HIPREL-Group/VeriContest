use vstd::arithmetic::mul::{
    lemma_mul_is_associative, lemma_mul_is_commutative,
    lemma_mul_is_distributive_add,
};
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, pow,
};
use vstd::calc;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

pub proof fn lemma_subrange_full<T>(s: Seq<T>)
    ensures
        s.subrange(0, s.len() as int) =~= s,
{
}

pub proof fn lemma_subrange_extend_one<T>(s: Seq<T>, end: int)
    requires
        0 <= end < s.len(),
    ensures
        s.subrange(0, end + 1) =~= s.subrange(0, end).push(s[end]),
{
    assert(s.subrange(0, end + 1).len() == s.subrange(0, end).push(s[end]).len());
    assert forall |i: int|
        0 <= i < s.subrange(0, end + 1).len()
        implies s.subrange(0, end + 1)[i] == s.subrange(0, end).push(s[end])[i]
    by {
        if i < end {
        } else {
            assert(i == end);
        }
    }
}

pub proof fn lemma_add_push<T>(s1: Seq<T>, s2: Seq<T>, x: T)
    ensures
        (s1 + s2).push(x) =~= s1 + s2.push(x),
{
    assert((s1 + s2).push(x).len() == (s1 + s2.push(x)).len());
    assert forall |i: int|
        0 <= i < (s1 + s2).push(x).len()
        implies (s1 + s2).push(x)[i] == (s1 + s2.push(x))[i]
    by {
        if i < s1.len() {
        } else if i < s1.len() + s2.len() {
            assert((s1 + s2)[i] == s2[i - s1.len()]);
            assert((s1 + s2.push(x))[i] == s2.push(x)[i - s1.len()]);
            assert(s2.push(x)[i - s1.len()] == s2[i - s1.len()]);
        } else {
            assert(i == s1.len() + s2.len());
            assert((s1 + s2).push(x)[i] == x);
            assert((s1 + s2.push(x))[i] == s2.push(x)[s2.len() as int]);
            assert(s2.push(x)[s2.len() as int] == x);
        }
    }
}

pub proof fn lemma_char_round_trip(ch: char)
    ensures
        (ch as usize) as char == ch,
{
}

pub proof fn seq_add_associative<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    ensures s1.add(s2).add(s3) =~= s1.add(s2.add(s3))
{
    assert forall|i: int| 0 <= i < s1.len() + s2.len() + s3.len() implies
        #[trigger] s1.add(s2).add(s3)[i] == s1.add(s2.add(s3))[i] by {
        if i < s1.len() {
            assert(s1.add(s2).add(s3)[i] == s1[i]);
            assert(s1.add(s2.add(s3))[i] == s1[i]);
        } else if i < s1.len() + s2.len() {
            assert(s1.add(s2).add(s3)[i] == s2[i - s1.len()]);
            assert(s1.add(s2.add(s3))[i] == s2.add(s3)[i - s1.len()]);
            assert(s2.add(s3)[i - s1.len()] == s2[i - s1.len()]);
        } else {
            assert(s1.add(s2).add(s3)[i] == s3[i - s1.len() - s2.len()]);
            assert(s1.add(s2.add(s3))[i] == s2.add(s3)[i - s1.len()]);
            assert(s2.add(s3)[i - s1.len()] == s3[i - s1.len() - s2.len()]);
        }
    }
}

pub proof fn lemma_filter_push<T>(seq: Seq<T>, x: T, f: spec_fn(T) -> bool)
    ensures
        seq.push(x).filter(f).len() == seq.filter(f).len() + if f(x) { 1 as nat } else { 0 as nat },
        seq.push(x).filter(f) =~= seq.filter(f) + (if f(x) { seq![x] } else { Seq::empty() }),
    decreases seq.len(),
{
    reveal_with_fuel(Seq::filter, 2);

    if seq.len() == 0 {
    } else {
        let head = seq[0];
        let tail = seq.subrange(1, seq.len() as int);

        lemma_filter_push(tail, x, f);

        assert(seq =~= seq![head] + tail);
        assert(seq.push(x) =~= seq![head] + tail.push(x));

        if f(head) {
            assert(seq.filter(f) =~= seq![head] + tail.filter(f));
            assert(seq.push(x).filter(f) =~= seq![head] + tail.push(x).filter(f));
        } else {
            assert(seq.filter(f) =~= tail.filter(f));
            assert(seq.push(x).filter(f) =~= tail.push(x).filter(f));
        }
    }
}

pub struct DigitList;
impl DigitList {
    /// Converts a sequence of digits (base 10) into its corresponding natural number.
    pub open spec fn digits_to_nat(digits: Seq<i32>) -> nat
        recommends
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        decreases digits.len(),
    {
        if digits.len() == 0 {
            0
        } else {
            let tail = digits.last() as nat;
            let remainder = digits.drop_last();
            10 * Self::digits_to_nat(remainder) + tail
        }
    }

    pub proof fn lemma_digits_empty_yield_zero()
        ensures
            Self::digits_to_nat(Seq::empty()) == 0,
    {
    }

    pub proof fn lemma_one_more_digit(digits: Seq<i32>)
        requires
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
            digits.len() >= 1,
        ensures
            Self::digits_to_nat(digits) == digits.first() * pow(10, (digits.len() - 1) as nat)
                + Self::digits_to_nat(digits.drop_first()),
        decreases digits.len(),
    {
        if digits.len() == 1 {
            Self::lemma_digits_empty_yield_zero();
            assert(digits.drop_last() == Seq::<i32>::empty());
            lemma_pow0(10);
        } else {
            let remainder = digits.drop_last();
            calc! {
                (==)
                Self::digits_to_nat(digits) as int; {}
                10 * Self::digits_to_nat(remainder) + digits.last(); {
                    Self::lemma_one_more_digit(remainder)
                }
                10 * (remainder.first() * pow(10, (remainder.len() - 1) as nat)
                    + Self::digits_to_nat(remainder.drop_first())) + digits.last(); {
                    lemma_mul_is_distributive_add(
                        10,
                        remainder.first() * pow(10, (remainder.len() - 1) as nat),
                        Self::digits_to_nat(remainder.drop_first()) as int,
                    )
                }
                10 * (remainder.first() * pow(10, (remainder.len() - 1) as nat)) + 10
                    * Self::digits_to_nat(remainder.drop_first()) + digits.last(); {
                    lemma_mul_is_associative(
                        10,
                        remainder.first() as int,
                        pow(10, (remainder.len() - 1) as nat),
                    );
                    assert(digits.drop_first().drop_last() == remainder.drop_first())
                }
                10 * remainder.first() * pow(10, (remainder.len() - 1) as nat)
                    + Self::digits_to_nat(digits.drop_first()); {
                    lemma_mul_is_commutative(10, remainder.first() as int);
                    lemma_mul_is_associative(
                        remainder.first() as int,
                        10,
                        pow(10, (remainder.len() - 1) as nat),
                    )
                }
                digits.first() * (10 * pow(10, (digits.len() - 2) as nat)) + Self::digits_to_nat(
                    digits.drop_first(),
                ); {
                    lemma_pow_adds(10, ((digits.len() - 1) - 1) as nat, 1);
                    lemma_pow1(10);
                    lemma_mul_is_commutative(10, pow(10, ((digits.len() - 1) - 1) as nat));
                }
                digits.first() * pow(10, (digits.len() - 1) as nat) + Self::digits_to_nat(
                    digits.drop_first(),
                );
            }
        }
    }
}

} // verus!
