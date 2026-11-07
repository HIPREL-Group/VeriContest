use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modv() -> int {
        1000000007
    }

    pub open spec fn lim(i: int, j: int) -> int
        recommends
            1 <= i <= 1000,
            0 <= j <= 1000,
    {
        if j < i - 1 { j } else { i - 1 }
    }

    pub open spec fn inv_count(i: int, j: int) -> int
        decreases if i < 0 { 0nat } else { i as nat }, 1nat, 0nat,
    {
        if i < 0 || i > 1000 || j < 0 || j > 1000 {
            0
        } else if i == 0 {
            if j == 0 { 1 } else { 0 }
        } else {
            Self::prefix(i, j, Self::lim(i, j) + 1)
        }
    }

    pub open spec fn prefix(i: int, j: int, t: int) -> int
        decreases if i < 0 { 0nat } else { i as nat }, 0nat, if t < 0 { 0nat } else { t as nat },
    {
        if i <= 0 || j < 0 || j > 1000 || t <= 0 {
            0
        } else {
            (Self::prefix(i, j, t - 1) + Self::inv_count(i - 1, j - (t - 1))) % Self::modv()
        }
    }

    pub fn k_inverse_pairs(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            0 <= k <= 1000,
        ensures
            0 <= (result as int),
            (result as int) < Self::modv(),
            result as int == Self::inv_count(n as int, k as int),
    {
    }
}

}
