use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_lucky_digits(n: u64) -> nat
    decreases n,
{
    if n == 0 {
        0nat
    } else {
        let d = (n % 10) as nat;
        let prev = count_lucky_digits(n / 10);
        if d == 4 || d == 7 { prev + 1nat } else { prev }
    }
}

pub open spec fn is_lucky_count(c: nat) -> bool {
    c == 4nat || c == 7nat
}

impl Solution {
    pub fn nearly_lucky(n: u64) -> (res: bool)
        requires
            1 <= n <= 1_000_000_000_000_000_000u64,
        ensures
            res == is_lucky_count(count_lucky_digits(n)),
    {
    }
}

}
