use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn divides(d: int, n: int) -> bool {
    d > 0 && n > 0 && n % d == 0
}

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && (forall|d: int| 2 <= d < n ==> !divides(d, n))
}

impl Solution {
    pub fn is_next_prime(n: u32, m: u32) -> (result: bool)
        requires
            2 <= n < m <= 50,
            is_prime(n as int),
        ensures
            result == (is_prime(m as int) && (forall|k: int| n < k < m ==> !is_prime(k))),
    {
    }
}

}
