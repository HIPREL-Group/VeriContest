use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow_int(a: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        1int
    } else {
        a * pow_int(a, k - 1)
    }
}

pub open spec fn in_generated_set(n: int, a: int, b: int) -> bool {
    (a == 1 && (n - 1) % b == 0) || (a > 1 && exists|k: int|
        k >= 0 && #[trigger] pow_int(a, k) <= n && (n - pow_int(a, k)) % b == 0)
}

impl Solution {
    pub fn n_in_generated_set(n: i64, a: i64, b: i64) -> (res: bool)
        requires
            1 <= n <= 1_000_000_000,
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
        ensures
            res == in_generated_set(n as int, a as int, b as int),
    {
        if a == 1 {
            (n - 1) % b == 0
        } else {
            let mut pow: i64 = 1;
            while pow <= n {
                if (n - pow) % b == 0 {
                    return true;
                }
                if pow > n / a {
                    return false;
                }
                pow = pow * a;
            }
            false
        }
    }
}

}
