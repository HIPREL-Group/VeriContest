use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_steps(n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else if n % 2 == 0 {
            1 + Self::spec_steps(n / 2)
        } else {
            1 + Self::spec_steps(n - 1)
        }
    }

    proof fn spec_steps_nonneg(n: int)
        requires
            n >= 0,
        ensures
            Self::spec_steps(n) >= 0,
        decreases n,
    {
        if n > 0 {
            if n % 2 == 0 {
                Self::spec_steps_nonneg(n / 2);
            } else {
                Self::spec_steps_nonneg(n - 1);
            }
        }
    }

    proof fn spec_steps_bound(n: int)
        requires
            n >= 0,
        ensures
            Self::spec_steps(n) <= 2 * n,
        decreases n,
    {
        if n > 0 {
            if n % 2 == 0 {
                Self::spec_steps_bound(n / 2);
            } else {
                Self::spec_steps_bound(n - 1);
            }
        }
    }

    pub fn number_of_steps(num: i32) -> (result: i32)
        requires
            0 <= num <= 1_000_000,
        ensures
            result == Self::spec_steps(num as int),
    {
        let mut n = num;
        let mut steps = 0i32;

        proof {
            Self::spec_steps_bound(num as int);
        }

        while n > 0
            invariant
                0 <= n <= 1_000_000,
                0 <= steps <= 2_000_000,
                steps as int + Self::spec_steps(n as int) == Self::spec_steps(num as int),
                Self::spec_steps(num as int) <= 2_000_000,
            decreases n,
        {
            proof {
                if n as int % 2 == 0 {
                    Self::spec_steps_nonneg(n as int / 2);
                } else {
                    Self::spec_steps_nonneg(n as int - 1);
                }
            }
            if n % 2 == 0 {
                n = n / 2;
            } else {
                n = n - 1;
            }
            steps = steps + 1;
        }
        steps
    }
}

}
