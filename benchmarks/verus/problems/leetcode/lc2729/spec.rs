use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_digit3_spec(num: int, d: int) -> int {
        (if num / 100 == d { 1int } else { 0int })
            + (if (num / 10) % 10 == d { 1int } else { 0int })
            + (if num % 10 == d { 1int } else { 0int })
    }

    pub open spec fn count_digit_all_spec(n: int, d: int) -> int {
        Self::count_digit3_spec(n, d)
            + Self::count_digit3_spec(2 * n, d)
            + Self::count_digit3_spec(3 * n, d)
    }

    pub open spec fn is_fascinating_spec(n: int) -> bool {
        100 <= n <= 999
            && 100 <= 2 * n <= 999
            && 100 <= 3 * n <= 999
            && Self::count_digit_all_spec(n, 1) == 1
            && Self::count_digit_all_spec(n, 2) == 1
            && Self::count_digit_all_spec(n, 3) == 1
            && Self::count_digit_all_spec(n, 4) == 1
            && Self::count_digit_all_spec(n, 5) == 1
            && Self::count_digit_all_spec(n, 6) == 1
            && Self::count_digit_all_spec(n, 7) == 1
            && Self::count_digit_all_spec(n, 8) == 1
            && Self::count_digit_all_spec(n, 9) == 1
    }

    pub fn is_fascinating(n: i32) -> (result: bool)
        requires
            100 <= n <= 999,
        ensures
            result == Self::is_fascinating_spec(n as int),
    {
    }
}

}
