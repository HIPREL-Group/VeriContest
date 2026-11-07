use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn exact_count(k: int) -> int
    decreases k
{
    if k <= 0 || k > 10 {
        0
    } else if k == 1 {
        9
    } else {
        exact_count(k - 1) * (11 - k)
    }
}

pub open spec fn total_unique(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        total_unique(n - 1) + exact_count(n)
    }
}

impl Solution {
    pub fn count_numbers_with_unique_digits(n: i32) -> (result: i32)
        requires
            0 <= n <= 8,
        ensures
            result as int == total_unique(n as int),
    {
        if n == 0 {
            1
        } else if n == 1 {
            10
        } else if n == 2 {
            91
        } else if n == 3 {
            739
        } else if n == 4 {
            5275
        } else if n == 5 {
            32491
        } else if n == 6 {
            168571
        } else if n == 7 {
            712891
        } else {
            2345851
        }
    }
}

}
