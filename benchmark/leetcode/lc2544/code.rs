impl Solution {
    pub fn alternate_digit_sum(n: i32) -> i32 {
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

        let mut rem: i32 = n;
        let mut sign: i32;
        if digits % 2 == 0 {
            sign = -1;
        } else {
            sign = 1;
        }
        let mut ans: i32 = 0;

        while digits > 0 {
            let old_ans = ans;
            let old_digits = digits;
            let old_rem = rem;
            let old_sign = sign;
            let digit = rem % 10;
            ans = ans + sign * digit;
            rem = rem / 10;
            sign = -sign;
            digits = digits - 1;
        }

        ans
    }
}
