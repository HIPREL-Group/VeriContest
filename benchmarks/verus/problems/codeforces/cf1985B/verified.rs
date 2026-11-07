use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
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
        ensures
            s as int == Self::sum_multiples(x as int, n as int),
    {
        let k = n / x;
        proof {
            assert(2 <= x <= n);
            assert(k == n / x);
            lemma_fundamental_div_mod(n as int, x as int);
            assert((k as int) == n as int / x as int);
            assert((k as int) * (x as int) <= (n as int));
            assert(0 <= k);
            assert((k as int) * 2 <= (k as int) * (x as int)) by (nonlinear_arith)
                requires
                    0 <= k as int,
                    2 <= x as int,
            {
            }
            assert((k as int) * 2 <= (n as int));
            assert(k <= n / 2);
            assert(n <= 100);
            assert(k <= 50);
            assert((x as int) <= 100);
            assert((k as int) <= 50);
            let a_int = (x as int) * (k as int);
            assert(a_int <= (n as int));
            assert((n as int) <= 100);
            let b_int = (k as int) + 1;
            assert(b_int <= 51);
            assert(a_int * b_int <= (n as int) * 51) by (nonlinear_arith)
                requires
                    0 <= a_int,
                    0 <= b_int,
                    a_int <= (n as int),
                    b_int <= 51,
            {
            }
        }
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
        while x <= n
            invariant
                2 <= n <= 100,
                3 <= x <= n + 1,
                2 <= best_x < x,
                best_sum as int == Self::sum_multiples(best_x as int, n as int),
                forall |t: int|
                    2 <= t < x ==> Self::sum_multiples(best_x as int, n as int)
                        >= #[trigger] Self::sum_multiples(t, n as int),
            decreases
                n - x + 1,
        {
            let s = Solution::sum_multiples_exec(x, n);
            if s > best_sum {
                best_sum = s;
                best_x = x;
            }
            x = x + 1;
        }
        proof {
            assert(x == n + 1);
            assert(forall |xi: int|
                2 <= xi <= n as int ==> Self::sum_multiples(best_x as int, n as int)
                    >= #[trigger] Self::sum_multiples(xi, n as int));
        }
        best_x
    }
}

}
