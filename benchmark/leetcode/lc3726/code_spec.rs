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
        let mut m: i64 = n;
        let mut place: i64 = 1;
        let mut res: i64 = 0;
        while m > 0 {
            let digit: i64 = m % 10;
            if digit != 0 {
                res = res + digit * place;
                place = place * 10;
            }
            m = m / 10;
        }
        res
    }
}

}
