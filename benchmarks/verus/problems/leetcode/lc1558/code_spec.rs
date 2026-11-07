use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    pub open spec fn popcount(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 } else { (n % 2) + Self::popcount(n / 2) }
    }

    
    
    pub open spec fn bit_length(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 } else { 1 + Self::bit_length(n / 2) }
    }

    pub open spec fn sum_popcount(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 } else { Self::sum_popcount(s, end - 1) + Self::popcount(s[end - 1] as int) }
    }

    pub open spec fn max_bit_length(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            let prev = Self::max_bit_length(s, end - 1);
            let curr = Self::bit_length(s[end - 1] as int);
            if curr > prev { curr } else { prev }
        }
    }

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    pub fn min_operations(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000,
        ensures
            result as int == Self::sum_popcount(nums@, nums@.len() as int) +
                if Self::max_bit_length(nums@, nums@.len() as int) > 0 {
                    Self::max_bit_length(nums@, nums@.len() as int) - 1
                } else {
                    0int
                },
    {
        let mut ones: i32 = 0;
        let mut max_len: i32 = 0;
        let n = nums.len();
        let mut i: usize = 0;
        while i < n {
            let mut val = nums[i];
            let mut bits: i32 = 0;
            let mut len: i32 = 0;
            while val > 0 {
                if val % 2 == 1 {
                    bits = bits + 1;
                }
                val = val / 2;
                len = len + 1;
            }
            ones = ones + bits;
            if len > max_len {
                max_len = len;
            }
            i = i + 1;
        }
        if max_len > 0 {
            ones + max_len - 1
        } else {
            ones
        }
    }
}

}
