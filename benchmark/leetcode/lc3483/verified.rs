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
        while num < 1000
            invariant
                3 <= digits.len() <= 10,
                forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
                100 <= num <= 1000,
                num % 2 == 0,
                0 <= ans <= (num - 100) / 2,
                ans as int == Self::count_valid_from(digits@, 100) - Self::count_valid_from(digits@, num as int),
            decreases 1000 - num,
        {
            let ghost old_num = num;
            let ghost old_ans = ans as int;
            let mut violations: i32 = 0;
            let mut d: i32 = 0;
            while d < 10
                invariant
                    3 <= digits.len() <= 10,
                    forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
                    100 <= num < 1000,
                    num % 2 == 0,
                    0 <= d <= 10,
                    0 <= violations <= d,
                    violations as int == Self::bad_digit_prefix(digits@, num as int, d as int),
                decreases 10 - d,
            {
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
                while i < digits.len()
                    invariant
                        3 <= digits.len() <= 10,
                        forall |j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
                        0 <= d < 10,
                        0 <= i <= digits.len(),
                        0 <= have <= i,
                        have as int == Self::count_digit_prefix(digits@, d as int, i as int),
                    decreases digits.len() - i,
                {
                    let ghost old_i = i;
                    if digits[i] == d {
                        have += 1;
                    }
                    proof {
                        assert(Self::count_digit_prefix(digits@, d as int, (old_i + 1) as int)
                            == Self::count_digit_prefix(digits@, d as int, old_i as int)
                                + if digits[old_i as int] == d { 1int } else { 0int });
                    }
                    i += 1;
                }

                proof {
                    assert(need as int == Self::need_digit(num as int, d as int));
                    assert(have as int == Self::count_digit_prefix(digits@, d as int, digits.len() as int));
                    assert(Self::bad_digit_prefix(digits@, num as int, (d + 1) as int)
                        == Self::bad_digit_prefix(digits@, num as int, d as int)
                            + if Self::need_digit(num as int, d as int)
                                <= Self::count_digit_prefix(digits@, d as int, digits.len() as int) {
                                0int
                            } else {
                                1int
                            });
                }

                if need > have {
                    violations += 1;
                }
                d += 1;
            }

            if violations == 0 {
                ans += 1;
            }

            proof {
                assert(d == 10);
                assert(violations as int == Self::bad_digit_prefix(digits@, num as int, 10));
                assert(Self::valid_number(digits@, num as int) <==> Self::bad_digit_prefix(digits@, num as int, 10) == 0);
                assert(Self::count_valid_from(digits@, num as int)
                    == (if Self::valid_number(digits@, num as int) { 1int } else { 0int })
                        + Self::count_valid_from(digits@, num as int + 2));
                if violations == 0 {
                    assert(Self::valid_number(digits@, num as int));
                    assert(ans as int == old_ans + 1);
                } else {
                    assert(!Self::valid_number(digits@, num as int));
                    assert(ans as int == old_ans);
                }
                assert(ans as int == Self::count_valid_from(digits@, 100) - Self::count_valid_from(digits@, num as int + 2));
            }

            num += 2;
        }

        proof {
            assert(num == 1000);
            assert(Self::count_valid_from(digits@, 1000) == 0);
            assert(ans as int == Self::count_valid_from(digits@, 100));
        }

        ans
    }
}

}
