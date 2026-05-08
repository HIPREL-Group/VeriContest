use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn deposit(day: int) -> int {
        (day - 1) / 7 + (day - 1) % 7 + 1
    }

    pub open spec fn total_spec(n: int) -> int
        decreases n,
    {
        if n <= 0 { 0 }
        else { Self::total_spec(n - 1) + Self::deposit(n) }
    }

    proof fn deposit_bound(day: int)
        requires 1 <= day <= 1000,
        ensures 1 <= Self::deposit(day) <= day,
    {
    }

    proof fn total_spec_bound(n: int)
        requires 0 <= n <= 1000,
        ensures 0 <= Self::total_spec(n) <= n * n,
        decreases n,
    {
        if n > 0 {
            Self::total_spec_bound(n - 1);
            Self::deposit_bound(n);
            assert((n - 1) * (n - 1) + n <= n * n) by(nonlinear_arith)
                requires n >= 1,
            {}
        }
    }

    pub fn total_money(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result as int == Self::total_spec(n as int),
    {
        let mut total: i32 = 0;
        let mut i: i32 = 1;

        while i <= n
            invariant
                1 <= i <= n + 1,
                1 <= n <= 1000,
                total as int == Self::total_spec((i - 1) as int),
                0 <= total <= 1_000_000,
            decreases n - i + 1,
        {
            proof {
                Self::deposit_bound(i as int);
                Self::total_spec_bound(i as int);
                assert(i as int * (i as int) <= 1_000_000) by(nonlinear_arith)
                    requires 1 <= i <= 1000i32,
                {}
            }
            let k = i - 1;
            total = total + k / 7 + k % 7 + 1;
            i = i + 1;
        }

        total
    }
}

}
