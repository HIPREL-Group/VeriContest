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

    pub fn find_even_numbers(digits: Vec<i32>) -> (result: Vec<i32>)
        requires
            3 <= digits.len() <= 100,
            forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            result@ == Self::collect_even_steps(digits@, 450),
    {
    }
}

}
