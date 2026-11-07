use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_count_10(n: int) -> nat
        recommends
            1 <= n <= 1_000_000_000,
    {
        if n >= 1_000_000_000 {
            10
        } else if n >= 100_000_000 {
            9
        } else if n >= 10_000_000 {
            8
        } else if n >= 1_000_000 {
            7
        } else if n >= 100_000 {
            6
        } else if n >= 10_000 {
            5
        } else if n >= 1_000 {
            4
        } else if n >= 100 {
            3
        } else if n >= 10 {
            2
        } else {
            1
        }
    }

    pub open spec fn alternating_suffix_sum(rem: nat, digits: nat, sign: int) -> int
        decreases digits,
    {
        if digits == 0 {
            0
        } else {
            sign * (rem % 10) as int
                + Self::alternating_suffix_sum(rem / 10, (digits - 1) as nat, -sign)
        }
    }

    pub open spec fn alternating_digit_sum_spec(n: nat) -> int
        recommends
            1 <= n <= 1_000_000_000,
    {
        let d = Self::digit_count_10(n as int);
        let s = if d % 2 == 0 { -1 } else { 1 };
        Self::alternating_suffix_sum(n, d, s)
    }

    pub fn alternate_digit_sum(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::alternating_digit_sum_spec(n as nat),
    {
        let mut digits: i32;
        if n >= 1_000_000_000 {
            digits = 10;
        } else if n >= 100_000_000 {
            digits = 9;
        } else if n >= 10_000_000 {
            digits = 8;
        } else if n >= 1_000_000 {
            digits = 7;
        } else if n >= 100_000 {
            digits = 6;
        } else if n >= 10_000 {
            digits = 5;
        } else if n >= 1_000 {
            digits = 4;
        } else if n >= 100 {
            digits = 3;
        } else if n >= 10 {
            digits = 2;
        } else {
            digits = 1;
        }

        proof {
            assert(digits as int == Self::digit_count_10(n as int));
        }

        let mut rem: i32 = n;
        let mut sign: i32;
        if digits % 2 == 0 {
            sign = -1;
        } else {
            sign = 1;
        }
        let mut ans: i32 = 0;

        while digits > 0
            invariant
                1 <= n as int <= 1_000_000_000,
                0 <= rem,
                0 <= digits <= 10,
                sign == 1 || sign == -1,
                -9 * (10 - digits as int) <= ans as int <= 9 * (10 - digits as int),
                ans as int + Self::alternating_suffix_sum(rem as nat, digits as nat, sign as int)
                    == Self::alternating_digit_sum_spec(n as nat),
            decreases digits,
        {
            let old_ans = ans;
            let old_digits = digits;
            let old_rem = rem;
            let old_sign = sign;
            let digit = rem % 10;
            proof {
                assert(0 <= digit <= 9);
                assert(Self::alternating_suffix_sum(old_rem as nat, old_digits as nat, old_sign as int)
                    == old_sign as int * (old_rem as int % 10)
                        + Self::alternating_suffix_sum((old_rem / 10) as nat, (old_digits - 1) as nat, -(old_sign as int)));
                assert(-9 <= old_sign * digit <= 9);
                assert(-9 * (10 - (old_digits as int - 1))
                    <= old_ans + old_sign * digit
                    <= 9 * (10 - (old_digits as int - 1))) by (nonlinear_arith)
                    requires
                        -9 * (10 - old_digits as int) <= old_ans <= 9 * (10 - old_digits as int),
                        -9 <= old_sign * digit <= 9,
                ;
            }
            ans = ans + sign * digit;
            rem = rem / 10;
            sign = -sign;
            digits = digits - 1;
            proof {
                assert(ans as int + Self::alternating_suffix_sum(rem as nat, digits as nat, sign as int)
                    == Self::alternating_digit_sum_spec(n as nat));
            }
        }

        proof {
            assert(digits == 0);
            assert(ans as int + Self::alternating_suffix_sum(rem as nat, digits as nat, sign as int)
                == Self::alternating_digit_sum_spec(n as nat));
            assert(Self::alternating_suffix_sum(rem as nat, 0, sign as int) == 0);
            assert(ans as int == Self::alternating_digit_sum_spec(n as nat));
        }

        ans
    }
}

}
