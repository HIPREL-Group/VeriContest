use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_square_triple(a: int, b: int, c: int) -> bool {
    a * a + b * b == c * c
}

pub open spec fn count_for_c(n: int, a: int, b: int, c: int) -> int
    decreases n - c + 1,
{
    if c > n {
        0
    } else {
        (if is_square_triple(a, b, c) { 1int } else { 0int }) + count_for_c(n, a, b, c + 1)
    }
}

pub open spec fn count_for_b(n: int, a: int, b: int) -> int
    decreases n - b + 1,
{
    if b > n {
        0
    } else {
        count_for_c(n, a, b, 1) + count_for_b(n, a, b + 1)
    }
}

pub open spec fn count_for_a(n: int, a: int) -> int
    decreases n - a + 1,
{
    if a > n {
        0
    } else {
        count_for_b(n, a, 1) + count_for_a(n, a + 1)
    }
}

impl Solution {
    pub fn count_triples(n: i32) -> (result: i32)
        requires
            1 <= n <= 250,
        ensures
            result == count_for_a(n as int, 1),
    {
    }
}

}
