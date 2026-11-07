use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_value(x: int) -> int {
        if x < 0 { -x } else { x }
    }

    pub open spec fn tri(n: int) -> int {
        n * (n + 1) / 2
    }

    pub open spec fn valid_steps(target_abs: int, n: int) -> bool {
        0 <= target_abs
            && 0 <= n
            && Self::tri(n) >= target_abs
            && (Self::tri(n) - target_abs) % 2 == 0
    }

    pub fn reach_number(target: i32) -> (res: i32)
        requires
            -1_000_000_000 <= target <= 1_000_000_000,
            target != 0,
        ensures
            Self::valid_steps(Self::abs_value(target as int), res as int),
            forall|m: int| 0 <= m < res as int ==> !#[trigger] Self::valid_steps(Self::abs_value(target as int), m),
    {
        let target_abs = if target < 0 { -target } else { target };
        let mut step: i32 = 0;
        let mut sum: i32 = 0;
        while sum < target_abs
        {
            step += 1;
            sum += step;
        }
        if (sum - target_abs) % 2 != 0 {
            step += 1;
            sum += step;
            if (sum - target_abs) % 2 != 0 {
                step += 1;
                sum += step;
            }
        }
        step
    }
}

}
