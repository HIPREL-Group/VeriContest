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

    fn count_digit3_exec(num: i32, d: i32) -> (res: i32)
        requires
            100 <= num <= 999,
            1 <= d <= 9,
        ensures
            res as int == Self::count_digit3_spec(num as int, d as int),
    {
        let h = num / 100;
        let t = (num / 10) % 10;
        let o = num % 10;
        let mut c = 0;
        if h == d {
            c = c + 1;
        }
        if t == d {
            c = c + 1;
        }
        if o == d {
            c = c + 1;
        }
        c
    }

    pub fn is_fascinating(n: i32) -> (result: bool)
        requires
            100 <= n <= 999,
        ensures
            result == Self::is_fascinating_spec(n as int),
    {
        let n2 = n * 2;
        let n3 = n * 3;
        if !(100 <= n2 && n2 <= 999 && 100 <= n3 && n3 <= 999) {
            return false;
        }
        let c1 = Self::count_digit3_exec(n, 1) + Self::count_digit3_exec(n2, 1) + Self::count_digit3_exec(n3, 1);
        let c2 = Self::count_digit3_exec(n, 2) + Self::count_digit3_exec(n2, 2) + Self::count_digit3_exec(n3, 2);
        let c3 = Self::count_digit3_exec(n, 3) + Self::count_digit3_exec(n2, 3) + Self::count_digit3_exec(n3, 3);
        let c4 = Self::count_digit3_exec(n, 4) + Self::count_digit3_exec(n2, 4) + Self::count_digit3_exec(n3, 4);
        let c5 = Self::count_digit3_exec(n, 5) + Self::count_digit3_exec(n2, 5) + Self::count_digit3_exec(n3, 5);
        let c6 = Self::count_digit3_exec(n, 6) + Self::count_digit3_exec(n2, 6) + Self::count_digit3_exec(n3, 6);
        let c7 = Self::count_digit3_exec(n, 7) + Self::count_digit3_exec(n2, 7) + Self::count_digit3_exec(n3, 7);
        let c8 = Self::count_digit3_exec(n, 8) + Self::count_digit3_exec(n2, 8) + Self::count_digit3_exec(n3, 8);
        let c9 = Self::count_digit3_exec(n, 9) + Self::count_digit3_exec(n2, 9) + Self::count_digit3_exec(n3, 9);
        c1 == 1 && c2 == 1 && c3 == 1 && c4 == 1 && c5 == 1 && c6 == 1 && c7 == 1 && c8 == 1 && c9 == 1
    }
}

}
