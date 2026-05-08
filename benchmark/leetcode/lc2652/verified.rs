use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (if n % 3 == 0 || n % 5 == 0 || n % 7 == 0 { n } else { 0int }) + Self::sum_spec(n - 1)
        }
    }

    pub fn sum_of_multiples(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result == Self::sum_spec(n as int),
    {
        let mut sum: i32 = 0;
        let mut i: i32 = n;
        let limit = n;
        
        while i > 0
            invariant
                1 <= n <= 1000,
                0 <= i <= limit,
                limit == n,
                0 <= sum <= (limit - i) * 1000,
                sum as int + Self::sum_spec(i as int) == Self::sum_spec(limit as int),
            decreases i,
        {
            if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
                sum += i;
            }
            i -= 1;
        }
        sum
    }
}

}
