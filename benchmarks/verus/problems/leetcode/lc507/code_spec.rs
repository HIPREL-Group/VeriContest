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

    pub fn get_sum(n: i32) -> (res: i64)
        requires
            1 <= n <= 100_000_000,
        ensures
            res == Self::sum_divisors_up_to(n as int, n - 1),
    {
        let nn: i64 = n as i64;
        let mut sum: i64 = 0;
        let mut i: i64 = 1;

        while i * i <= nn
        {
            if nn % i == 0 {
                let comp: i64 = nn / i;
                sum = sum + i;
                if i != comp {
                    sum = sum + comp;
                }
            }

            i = i + 1;
        }

        sum - nn
    }

    pub fn check_perfect_number(num: i32) -> (res: bool) 
        requires
            1 <= num <= 100_000_000, 
        ensures
            res == (num == Self::sum_divisors_up_to(num as int, num - 1))
    {
        if (num as i64) == Self::get_sum(num) {
            true
        }
        else {
            false
        }
    }
}

}