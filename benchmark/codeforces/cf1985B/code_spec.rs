use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_multiples(x: int, n: int) -> int
        recommends
            1 <= x,
            1 <= n,
    {
        let k = n / x;
        x * k * (k + 1) / 2
    }

    pub fn sum_multiples_exec(x: i32, n: i32) -> (s: i32)
        requires
            2 <= x <= n,
            2 <= n <= 100,
    {
        let k = n / x;
        x * k * (k + 1) / 2
    }

    pub fn max_multiples_sum_x(n: i32) -> (result: i32)
        requires
            2 <= n <= 100,
        ensures
            2 <= result <= n,
            forall |x: int|
                2 <= x <= n as int ==> Self::sum_multiples(result as int, n as int)
                    >= #[trigger] Self::sum_multiples(x, n as int),
    {
        let mut best_x: i32 = 2;
        let mut best_sum: i32 = Solution::sum_multiples_exec(2, n);
        let mut x: i32 = 3;
        while x <= n {
            let s = Solution::sum_multiples_exec(x, n);
            if s > best_sum {
                best_sum = s;
                best_x = x;
            }
            x = x + 1;
        }
        best_x
    }
}

}
