use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_digit(nums: Seq<i32>, digit: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_digit(nums, digit, end - 1)
                + if nums[end - 1] as int == digit { 1int } else { 0int }
        }
    }

    pub open spec fn need_count(num: int, digit: int) -> int {
        let h = num / 100;
        let t = (num / 10) % 10;
        let u = num % 10;
        (if h == digit { 1int } else { 0int })
            + (if t == digit { 1int } else { 0int })
            + (if u == digit { 1int } else { 0int })
    }

    pub open spec fn can_form_spec(nums: Seq<i32>, num: int) -> bool {
        100 <= num < 1000
            && num % 2 == 0
            && forall |d: int| 0 <= d <= 9 ==> Self::need_count(num, d) <= Self::count_digit(nums, d, nums.len() as int)
    }

    pub open spec fn collect_even_steps(nums: Seq<i32>, steps: int) -> Seq<i32>
        decreases steps,
    {
        if steps <= 0 {
            seq![]
        } else {
            let prev = Self::collect_even_steps(nums, steps - 1);
            let num = 100 + 2 * (steps - 1);
            if Self::can_form_spec(nums, num) {
                prev.push(num as i32)
            } else {
                prev
            }
        }
    }

    fn count_digit_exec(nums: &Vec<i32>, digit: i32) -> (c: i32)
        ensures
            c as int == Self::count_digit(nums@, digit as int, nums.len() as int),
    {
        let n = nums.len();
        let mut i: usize = 0;
        let mut c: i32 = 0;
        while i < n {
            if nums[i] == digit {
                c = c + 1;
            }
            i = i + 1;
        }
        c
    }

    fn need_count_exec(num: i32, digit: i32) -> (c: i32)
        requires
            100 <= num < 1000,
            0 <= digit <= 9,
        ensures
            c as int == Self::need_count(num as int, digit as int),
    {
        let h = num / 100;
        let t = (num / 10) % 10;
        let u = num % 10;
        let mut c: i32 = 0;
        if h == digit {
            c = c + 1;
        }
        if t == digit {
            c = c + 1;
        }
        if u == digit {
            c = c + 1;
        }
        c
    }

    fn can_form_exec(nums: &Vec<i32>, num: i32) -> (ok: bool)
        requires
            100 <= num < 1000,
            num % 2 == 0,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 9,
        ensures
            ok == Self::can_form_spec(nums@, num as int),
    {
        let mut d: i32 = 0;
        let mut ok = true;
        while d <= 9 {
            let need = Self::need_count_exec(num, d);
            let have = Self::count_digit_exec(nums, d);
            if need > have {
                ok = false;
            }
            d = d + 1;
        }
        ok
    }

    pub fn find_even_numbers(digits: Vec<i32>) -> (result: Vec<i32>)
        requires
            3 <= digits.len() <= 100,
            forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            result@ == Self::collect_even_steps(digits@, 450),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut step: i32 = 0;
        while step < 450 {
            let num = 100 + 2 * step;
            if Self::can_form_exec(&digits, num) {
                result.push(num);
            }
            step = step + 1;
        }
        result
    }
}

}
