use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_divisor(n: int, d: int) -> bool 
    {
        d > 0 && d < n && n % d == 0
    }

    pub open spec fn sum_divisors_up_to(n: int, k: int) -> int
        decreases k, 
    {
        if k <= 0 {
            0
        } else if Self::is_divisor(n, k) {
            k + Self::sum_divisors_up_to(n, k - 1)
        } else {
            Self::sum_divisors_up_to(n, k - 1)
        }
    }

    pub fn check_perfect_number(num: i32) -> (res: bool) 
        requires
            1 <= num <= 100_000_000, 
        ensures
            res == (num == Self::sum_divisors_up_to(num as int, num - 1))
    {
        
    }
}

}