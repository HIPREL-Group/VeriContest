use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum(n: nat) -> nat
        decreases n,
    {
        if n < 10 {
            n
        } else {
            (n % 10) + Self::digit_sum(n / 10)
        }
    }

    proof fn lemma_digit_sum_le(n: nat)
        ensures
            Self::digit_sum(n) <= n,
            n > 0 ==> Self::digit_sum(n) >= 1,
        decreases n,
    {
        if n >= 10 {
            Self::lemma_digit_sum_le(n / 10);
        }
    }

    pub fn sum_of_the_digits_of_harshad_number(x: i32) -> (res: i32)
        requires
            1 <= x <= 100,
        ensures
            Self::digit_sum(x as nat) > 0,
            x as nat % Self::digit_sum(x as nat) == 0 ==> res == Self::digit_sum(x as nat),
            x as nat % Self::digit_sum(x as nat) != 0 ==> res == -1i32,
    {
        let mut s: u32 = 0;
        let mut t: u32 = x as u32;

        proof {
            Self::lemma_digit_sum_le(x as nat);
        }

        while t > 0
            invariant
                Self::digit_sum(x as nat) == s as nat + Self::digit_sum(t as nat),
                s as nat <= Self::digit_sum(x as nat),
                Self::digit_sum(x as nat) <= 100,
                t <= 100,
            decreases t,
        {
            let d = t % 10;
            s += d;
            t = t / 10;
        }

        proof {
            Self::lemma_digit_sum_le(x as nat);
        }

        if x as u32 % s == 0 {
            s as i32
        } else {
            -1
        }
    }
}

}
