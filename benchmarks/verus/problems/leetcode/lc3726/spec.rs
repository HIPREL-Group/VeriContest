use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn remove_zeros_acc(m: int, place: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::remove_zeros_acc(m / 10, place, acc)
            } else {
                Self::remove_zeros_acc(m / 10, place * 10, acc + d * place)
            }
        }
    }

    pub open spec fn remove_zeros_spec(n: int) -> int {
        Self::remove_zeros_acc(n, 1, 0)
    }

    pub fn remove_zeros(n: i64) -> (res: i64)
        requires
            1 <= n <= 1_000_000_000_000_000,
        ensures
            res as int == Self::remove_zeros_spec(n as int),
    {
    }
}

}
