impl Solution {
    fn digit_contrib(orig: u128, digit: u128) -> i32
    {
        if digit == 0 {
            0
        } else if orig % digit == 0 {
            1
        } else {
            0
        }
    }

    pub fn count_digits(num: i32) -> i32
    {
        let orig = num as u128;
        let mut rem = orig;
        let mut digits: u8 = 10;
        let mut count: i32 = 0;
        while digits > 0
        {
            let old_count = count;
            let old_digits = digits;
            let old_rem = rem;
            let digit = rem % 10;
            let add = Self::digit_contrib(orig, digit);
            count = count + add;
            rem = rem / 10;
            digits = digits - 1;
        }
        count
    }
}

