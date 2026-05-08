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

    pub open spec fn min_digit_sum(nums: Seq<i32>, end: int) -> nat
        decreases end,
    {
        if end <= 1 {
            Self::digit_sum(nums[0] as nat)
        } else {
            let prev = Self::min_digit_sum(nums, end - 1);
            let cur = Self::digit_sum(nums[end - 1] as nat);
            if cur < prev { cur } else { prev }
        }
    }

    pub fn min_element(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
        ensures
            res as nat == Self::min_digit_sum(nums@, nums.len() as int),
    {
        let mut min_val: i32 = i32::MAX;
        for i in 0..nums.len()
        {
            let mut s: u32 = 0;
            let mut x: u32 = nums[i] as u32;
            while x > 0
            {
                let d = x % 10;
                s += d;
                x = x / 10;
            }
            if i == 0 || (s as i32) < min_val {
                min_val = s as i32;
            }
        }
        min_val
    }
}

}
