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

    proof fn lemma_digit_sum_le(n: nat)
        ensures
            Self::digit_sum(n) <= n,
            n > 0 ==> Self::digit_sum(n) >= 1,
        decreases n,
    {
        if n >= 10 {
            Self::lemma_digit_sum_le(n / 10);
        }
    }

    proof fn lemma_digit_sum_while(n: nat, s: nat, x: nat)
        requires
            Self::digit_sum(n) == s + Self::digit_sum(x),
            x > 0,
        ensures
            Self::digit_sum(n) == (s + x % 10) + Self::digit_sum(x / 10),
        decreases x,
    {
    }

    proof fn lemma_min_digit_sum_le(nums: Seq<i32>, end: int)
        requires
            end >= 1,
            end <= nums.len(),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
        ensures
            1 <= Self::min_digit_sum(nums, end) <= 10000,
        decreases end,
    {
        Self::lemma_digit_sum_le(nums[0] as nat);
        if end > 1 {
            Self::lemma_min_digit_sum_le(nums, end - 1);
            Self::lemma_digit_sum_le(nums[end - 1] as nat);
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
            invariant
                1 <= nums.len() <= 100,
                forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
                i == 0 ==> min_val == i32::MAX,
                i > 0 ==> min_val as nat == Self::min_digit_sum(nums@, i as int),
                i > 0 ==> 1 <= min_val <= 10000,
        {
            let mut s: u32 = 0;
            let mut x: u32 = nums[i] as u32;

            proof {
                Self::lemma_digit_sum_le(nums@[i as int] as nat);
            }

            while x > 0
                invariant
                    0 <= i < nums.len(),
                    Self::digit_sum(nums@[i as int] as nat) == s as nat + Self::digit_sum(x as nat),
                    s as nat <= Self::digit_sum(nums@[i as int] as nat),
                    Self::digit_sum(nums@[i as int] as nat) <= 10000,
                    x <= 10000,
                    1 <= nums@[i as int] <= 10000,
                decreases x,
            {
                proof {
                    Self::lemma_digit_sum_while(nums@[i as int] as nat, s as nat, x as nat);
                    Self::lemma_digit_sum_le(x as nat);
                }
                let d = x % 10;
                s += d;
                x = x / 10;
            }

            proof {
                Self::lemma_min_digit_sum_le(nums@, i as int + 1);
            }

            if i == 0 || (s as i32) < min_val {
                min_val = s as i32;
            }
        }
        min_val
    }
}

}
