use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn concat_non_zero_acc(m: int, place: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::concat_non_zero_acc(m / 10, place, acc)
            } else {
                Self::concat_non_zero_acc(m / 10, place * 10, acc + d * place)
            }
        }
    }

    pub open spec fn sum_non_zero_acc(m: int, acc: int) -> int
        decreases m,
    {
        if m <= 0 {
            acc
        } else {
            let d = m % 10;
            if d == 0 {
                Self::sum_non_zero_acc(m / 10, acc)
            } else {
                Self::sum_non_zero_acc(m / 10, acc + d)
            }
        }
    }

    pub open spec fn concat_non_zero(n: int) -> int {
        Self::concat_non_zero_acc(n, 1, 0)
    }

    pub open spec fn sum_non_zero(n: int) -> int {
        Self::sum_non_zero_acc(n, 0)
    }

    pub fn sum_and_multiply(n: i32) -> (res: i64)
        requires
            0 <= n <= 1_000_000_000,
        ensures
            res as int == Self::concat_non_zero(n as int) * Self::sum_non_zero(n as int),
    {
    }
}

} 
