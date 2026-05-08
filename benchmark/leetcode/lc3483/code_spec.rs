use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn need_digit(num: int, d: int) -> int {
        (if num / 100 == d { 1int } else { 0int })
            + (if (num / 10) % 10 == d { 1int } else { 0int })
            + (if num % 10 == d { 1int } else { 0int })
    }

    pub open spec fn count_digit_prefix(s: Seq<i32>, d: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_digit_prefix(s, d, end - 1)
                + if s[end - 1] as int == d { 1int } else { 0int }
        }
    }

    pub open spec fn bad_digit_prefix(s: Seq<i32>, num: int, d_end: int) -> int
        decreases d_end,
    {
        if d_end <= 0 {
            0
        } else {
            let d = d_end - 1;
            Self::bad_digit_prefix(s, num, d)
                + if Self::need_digit(num, d) <= Self::count_digit_prefix(s, d, s.len() as int) {
                    0int
                } else {
                    1int
                }
        }
    }

    pub open spec fn valid_number(s: Seq<i32>, num: int) -> bool {
        100 <= num <= 998 && num % 2 == 0 && Self::bad_digit_prefix(s, num, 10) == 0
    }

    pub open spec fn count_valid_from(s: Seq<i32>, num: int) -> int
        decreases if num < 1000 { 1000 - num } else { 0 },
    {
        if num >= 1000 {
            0
        } else {
            (if Self::valid_number(s, num) { 1int } else { 0int })
                + Self::count_valid_from(s, num + 2)
        }
    }

    pub fn total_numbers(digits: Vec<i32>) -> (result: i32)
        requires
            3 <= digits.len() <= 10,
            forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            result as int == Self::count_valid_from(digits@, 100),
    {
        let mut ans: i32 = 0;
        let mut num: i32 = 100;
        while num < 1000 {
            let mut violations: i32 = 0;
            let mut d: i32 = 0;
            while d < 10 {
                let mut need: i32 = 0;
                if num / 100 == d {
                    need += 1;
                }
                if (num / 10) % 10 == d {
                    need += 1;
                }
                if num % 10 == d {
                    need += 1;
                }

                let mut have: i32 = 0;
                let mut i: usize = 0;
                while i < digits.len() {
                    if digits[i] == d {
                        have += 1;
                    }
                    i += 1;
                }

                if need > have {
                    violations += 1;
                }
                d += 1;
            }

            if violations == 0 {
                ans += 1;
            }
            num += 2;
        }
        ans
    }
}

}
