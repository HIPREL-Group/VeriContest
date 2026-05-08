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
        decreases i,
    {
        i -= 1;
        result.push(v[i]);
    }
    result
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
        let mut last_sum_save: i32 = 0;
        let mut last_carry_in_save: i32 = 0;
        let mut last_digit_save: i32 = 0;
        let mut i = 0;
        while i < digits.len()
            decreases digits.len() - i,
        {
            let digit = digits[i];
            let sum = carry + digit;
            last_carry_in_save = carry;
            last_digit_save = digit;
            last_sum_save = sum;
            let result_clone = result.clone();
            carry = sum / 10;
            result.push(sum % 10);
            i += 1;
        }
        let result_clone = result.clone();
        let digits_len = digits.len();
        if carry == 1 {
            result.push(carry);
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
        result
    }
}

}
