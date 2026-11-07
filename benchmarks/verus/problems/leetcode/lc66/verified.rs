use vstd::arithmetic::{
    mul::{lemma_mul_is_associative, lemma_mul_is_distributive_add},
    power::{lemma_pow0, lemma_pow1, lemma_pow_adds, pow},
};
use vstd::prelude::*;
use vstd::seq_lib::*;

fn main() {}

verus! {

pub fn rev<T: Copy>(v: Vec<T>) -> (result: Vec<T>)
    ensures
        result@ == v@.reverse(),
{
    let mut result: Vec<T> = Vec::with_capacity(v.len());
    let mut i = v.len();
    while i > 0
        invariant
            0 <= i <= v.len(),
            result@.len() == v.len() - i,
            forall|j: int|
                0 <= j < result@.len() ==> #[trigger] result@[j] == v@[v@.len() - 1 - j],
        decreases i,
    {
        i -= 1;
        result.push(v[i]);
    }
    proof {
        assert(result@ =~= v@.reverse());
    }
    result
}

proof fn lemma_seq_reverse_index_i32(s: Seq<i32>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.reverse()[i] == s[s.len() - 1 - i],
{
    assert(s.reverse() == Seq::<i32>::new(s.len(), |j: int| s[s.len() - 1 - j]));
    assert(s.reverse()[i] == s[s.len() - 1 - i]);
}

pub struct Solution;

impl Solution {
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

    pub open spec fn rev_digits_to_nat(digits: Seq<i32>) -> nat
        recommends
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        decreases digits.len(),
    {
        if digits.len() == 0 {
            0
        } else {
            let tail = digits.first() as nat;
            let remainder = digits.drop_first();
            10 * Self::rev_digits_to_nat(remainder) + tail
        }
    }

    pub proof fn rev_digits_rev(digits: Seq<i32>)
        ensures
            Self::rev_digits_to_nat(digits.reverse()) == Self::digits_to_nat(digits),
        decreases digits.len(),
    {
        if digits.len() == 0 {
        } else {
            assert(digits.drop_last().reverse() == digits.reverse().drop_first());
            Self::rev_digits_rev(digits.drop_last());
        }
    }

    pub proof fn rev_one_more(
        digits: Seq<i32>,
    )
        requires
            1 <= digits.len() <= 101,
            forall|i: usize|
                0 <= i < digits.len() ==> 0 <= #[trigger] digits[i as int]
                    <= 9,
        ensures
            Self::rev_digits_to_nat(digits.drop_last()) + pow(10, digits.drop_last().len())
                * digits.last() == Self::rev_digits_to_nat(digits),
        decreases digits.len(),
    {
        let remainder = digits.drop_first();
        if digits.len() == 1 {
            let rem_nat = Self::rev_digits_to_nat(remainder);
            lemma_pow0(10);
        } else {
            assert(digits.drop_last().drop_first() == remainder.drop_last());
            lemma_pow_adds(10, 1, remainder.drop_last().len());
            lemma_pow1(10);
            lemma_mul_is_associative(
                10,
                pow(10, remainder.drop_last().len()),
                remainder.last() as int,
            );
            lemma_mul_is_distributive_add(
                10,
                Self::rev_digits_to_nat(remainder.drop_last()) as int,
                pow(10, remainder.drop_last().len()) * remainder.last(),
            );
            Self::rev_one_more(remainder);
        }
    }

    pub fn plus_one_rev(digits: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= digits.len() <= 100,
            forall|i: usize| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i as int] <= 9,
            digits.len() == 1 || digits@.last() > 0,
        ensures
            Self::rev_digits_to_nat(result@) == Self::rev_digits_to_nat(digits@) + 1,
            forall|j: int| 0 <= j < result@.len() ==> 0 <= #[trigger] result@[j] <= 9,
            result@.last() > 0,
    {
        let mut carry = 1;
        let mut result: Vec<i32> = Vec::with_capacity(digits.len() + 1);
        proof {
            lemma_pow0(10);
        }
        let mut last_sum_save: i32 = 0;
        let mut last_carry_in_save: i32 = 0;
        let mut last_digit_save: i32 = 0;
        let mut i = 0;
        while i < digits.len()
            invariant
                1 <= digits.len() <= 100,
                forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
                forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 9,
                0 <= carry <= 1,
                Self::rev_digits_to_nat(result@) + pow(10, i as nat) * carry
                    == Self::rev_digits_to_nat(digits@.take(i as int)) + 1,
                0 <= i <= digits.len(),
                i == result.len(),
                0 < i ==> 0 <= last_sum_save <= 18,
                0 < i ==> (carry as int) == (last_sum_save as int) / 10,
                0 < i ==> last_sum_save == last_carry_in_save + last_digit_save,
                0 < i ==> result@.last() == last_sum_save % 10,
                0 < i ==> last_digit_save == digits@[(i - 1) as int],
                0 < i ==> last_carry_in_save == 0 || last_carry_in_save == 1,
            decreases digits.len() - i,
        {
            let digit = digits[i];
            let sum = carry + digit;
            last_carry_in_save = carry;
            last_digit_save = digit;
            last_sum_save = sum;
            proof {
                assert(last_sum_save == last_carry_in_save + last_digit_save);
            }
            let result_clone = result.clone();
            proof {
                let digits_onemore = digits@.take(i + 1);
                let digits_to_i = digits@.take(i as int);
                let pow10len = pow(10, i as nat);
                assert(digits_onemore.drop_last() == digits_to_i);
                Self::rev_one_more(digits_onemore);
                lemma_mul_is_distributive_add(pow10len, carry as int, digit as int);
                lemma_mul_is_distributive_add(pow10len, (sum % 10) as int, 10 * (sum / 10));
                lemma_mul_is_associative(pow10len, 10, (sum / 10) as int);
                lemma_pow_adds(10, i as nat, 1);
                lemma_pow1(10);
            }
            carry = sum / 10;
            result.push(sum % 10);
            proof {
                Self::rev_one_more(result@);
                assert(result_clone@ == result@.drop_last());
            }
            i += 1;
        }
        let result_clone = result.clone();
        proof {
            digits@.lemma_take_len();
            let result_carry = result@.push(carry);
            assert(result_carry.drop_last() == result@);
            Self::rev_one_more(result_carry);
        }
        let ghost r_pre_extra = result@;
        let digits_len = digits.len();
        if carry == 1 {
            result.push(carry);
        }
        proof {
            assert(r_pre_extra.len() == digits@.len());
            assert(forall|j: int| 0 <= j < r_pre_extra.len() ==> 0 <= #[trigger] r_pre_extra[j] <= 9);
            if carry == 1 {
                assert(result@ == r_pre_extra.push(1));
                assert forall|j: int| 0 <= j < result@.len() implies 0 <= #[trigger] result@[j] <= 9 by {
                    if j < r_pre_extra.len() {
                        assert(result@[j] == r_pre_extra[j]);
                    } else {
                        assert(j == r_pre_extra.len());
                        assert(result@[j] == 1);
                    }
                };
                assert(result@.last() == 1);
            } else {
                assert(result@ == r_pre_extra);
                assert forall|j: int| 0 <= j < result@.len() implies 0 <= #[trigger] result@[j] <= 9 by {
                    assert(0 <= r_pre_extra[j] <= 9);
                };
                assert(carry == 0);
                assert((carry as int) == (last_sum_save as int) / 10);
                assert((last_sum_save as int) / 10 == 0);
                assert(last_sum_save <= 9);
                assert(last_sum_save == last_carry_in_save + last_digit_save);
                assert((last_sum_save as int) == (last_carry_in_save as int) + (last_digit_save as int));
                assert(r_pre_extra.last() == last_sum_save % 10);
                assert(last_sum_save <= 9);
                assert(last_sum_save == last_sum_save % 10);
                if digits_len == 1 {
                    assert(last_carry_in_save == 1);
                    assert(last_digit_save == digits@[0]);
                    assert(last_sum_save == 1 + digits@[0]);
                    assert(0 <= digits@[0] <= 9);
                    assert(last_sum_save >= 1);
                } else {
                    assert(last_digit_save == digits@[digits@.len() - 1]);
                    assert(digits@[digits@.len() - 1] > 0);
                    assert(last_carry_in_save == 0 || last_carry_in_save == 1);
                    assert(last_sum_save >= 1);
                }
                assert(r_pre_extra.last() > 0);
            }
        }
        result
    }

    pub fn plus_one(digits: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= digits.len() <= 100,
            forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
            digits.len() == 1 || digits[0] > 0,
        ensures
            result[0] > 0,
            forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 9,
            Self::digits_to_nat(result@) == Self::digits_to_nat(digits@) + 1,
    {
        let rev_dig = rev(digits);
        let result_rev = Self::plus_one_rev(rev_dig);
        let result = rev(result_rev);
        proof {
            assert(rev_dig@ == digits@.reverse());
            Self::rev_digits_rev(digits@);
            assert(Self::rev_digits_to_nat(rev_dig@) == Self::digits_to_nat(digits@));
            assert(Self::rev_digits_to_nat(result_rev@) == Self::rev_digits_to_nat(rev_dig@) + 1);
            assert(Self::rev_digits_to_nat(result_rev@) == Self::digits_to_nat(digits@) + 1);
            assert(result@ == result_rev@.reverse());
            assert forall|j: int| 0 <= j < result@.len() implies 0 <= #[trigger] result@[j] <= 9 by {
                lemma_seq_reverse_index_i32(result_rev@, j);
                assert(0 <= result_rev@[result_rev@.len() - 1 - j] <= 9);
                assert(result@[j] == result_rev@[result_rev@.len() - 1 - j]);
            };
            Self::rev_digits_rev(result@);
            assert(result@.reverse() =~= result_rev@);
            assert(Self::digits_to_nat(result@) == Self::rev_digits_to_nat(result_rev@));
            assert(Self::digits_to_nat(result@) == Self::digits_to_nat(digits@) + 1);
            lemma_seq_reverse_index_i32(result_rev@, 0);
            assert(result@[0] == result_rev@.last());
            assert(result@[0] > 0);
        }
        result
    }
}

} 
