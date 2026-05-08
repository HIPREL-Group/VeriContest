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

    proof fn lemma_sum_within_bounds(n: int, k: int)
        requires
            2 <= n,
            0 <= k < n,
        ensures
            Self::sum_divisors_up_to(n, k) <= k * (k + 1) / 2,
        decreases k, 
    {
        reveal_with_fuel(Solution::sum_divisors_up_to, 2);
        if k <= 0 {
        } else {
            Self::lemma_sum_within_bounds(n, k - 1);
            if Self::is_divisor(n, k) {
                assert(k < n);
                assert(k + (k - 1) * k / 2 == k * (k + 1) / 2) by (nonlinear_arith)
                    requires k > 0;
            } else {
                assert((k - 1) * k / 2 <= k * (k + 1) / 2) by (nonlinear_arith)
                    requires k > 0;
            }
        }
    }

    pub fn get_sum(n: i32) -> (res: i64)
        requires 
            1 <= n <= 100_000_000, 
        ensures
            res == Self::sum_divisors_up_to(n as int, n - 1), 
    {
        let mut sum: i64 = 0;
        let mut i: i32 = 1;
        
        while i < n
            invariant
                1 <= i <= n,
                1 <= n <= 100_000_000,
                sum == Self::sum_divisors_up_to(n as int, i - 1),
                0 <= sum <= (i - 1) * i / 2,
            decreases n - i, 
        {
            proof {
                Self::lemma_sum_within_bounds(n as int, i - 1);
            }
            
            if n % i == 0 {
                assert(sum + i as i64 <= i * (i + 1) / 2) by (nonlinear_arith)
                    requires
                        sum <= (i - 1) * i / 2,
                        i >= 1, 
                {}
                
                assert(i * (i + 1) / 2 < i64::MAX) by (nonlinear_arith)
                    requires
                        i < n,
                        n <= 100_000_000, 
                {}

                sum = sum + i as i64;
            }
            
            proof {
                Self::lemma_sum_within_bounds(n as int, i as int);
            }
            
            i = i + 1;
        }
        
        sum
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