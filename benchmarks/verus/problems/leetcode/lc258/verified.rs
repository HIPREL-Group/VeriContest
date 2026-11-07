use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_of_digits(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            (n % 10) + Self::sum_of_digits(n / 10)
        }
    }

    pub proof fn lemma_digit_sum_bounded(n: nat)
        ensures
            n >= 10 ==> Self::sum_of_digits(n) < n,
            n < 10 ==> Self::sum_of_digits(n) == n,
            n > 0 ==> Self::sum_of_digits(n) > 0,
        decreases n,
    {
        if n >= 10 {
            Self::lemma_digit_sum_bounded(n / 10);
        }
    }

    pub open spec fn digit_root_recursive(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            proof {
                Self::lemma_digit_sum_bounded(n);
            }
            Self::digit_root_recursive(Self::sum_of_digits(n))
        }
    }

    pub proof fn lemma_sum_of_digits_mod_9(n: nat)
        ensures
            Self::sum_of_digits(n) % 9 == n % 9,
        decreases n,
    {
        if n < 10 {
        } else {
            let last_digit = n % 10;
            let rest = n / 10;

            Self::lemma_sum_of_digits_mod_9(rest);
        }
    }

    pub proof fn lemma_congruent_same_digit_root(a: nat, b: nat)
        requires
            a > 0,
            b > 0,
            a % 9 == b % 9,
        ensures
            Self::digit_root_recursive(a) == Self::digit_root_recursive(b),
        decreases a + b,
    {
        Self::lemma_digit_sum_bounded(a);
        Self::lemma_digit_sum_bounded(b);
        if a < 10 && b < 10 {
        } else if a < 10 {
            Self::lemma_sum_of_digits_mod_9(b);
            Self::lemma_congruent_same_digit_root(a, Self::sum_of_digits(b));
        } else if b < 10 {
            Self::lemma_sum_of_digits_mod_9(a);
            Self::lemma_congruent_same_digit_root(Self::sum_of_digits(a), b);
        } else {
            Self::lemma_sum_of_digits_mod_9(a);
            Self::lemma_sum_of_digits_mod_9(b);
            Self::lemma_congruent_same_digit_root(Self::sum_of_digits(a), Self::sum_of_digits(b));
        }
    }

    pub proof fn theorem_digit_root_formula(n: nat)
        ensures
            n > 0 ==> Self::digit_root_recursive(n) == if n % 9 == 0 {
                9
            } else {
                n % 9
            },
            n == 0 ==> Self::digit_root_recursive(n) == 0,
    {
        let m = n % 9;

        if m == 0 {
            Self::lemma_sum_of_digits_mod_9(n);
            if n != 0 {
                Self::lemma_congruent_same_digit_root(n, 9);
            }
        } else {
            Self::lemma_sum_of_digits_mod_9(n);
            Self::lemma_congruent_same_digit_root(n, m);
        }
    }

    pub fn add_digits(n: i32) -> (result: i32)
        requires
            0 <= n <= i32::MAX,
        ensures
            result == Self::digit_root_recursive(n as nat),
            0 <= result <= 9,
    {
        proof {
            Self::theorem_digit_root_formula(n as nat);
        }
        if n == 0 {
            0
        } else if n % 9 == 0 {
            9
        } else {
            n % 9
        }
    }
}

} 
