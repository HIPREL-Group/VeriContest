use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn round_sum(n: int) -> int { n * (n + 1) / 2 }





pub open spec fn after_full_rounds(n: int, m: int) -> int {
    if round_sum(n) > 0 { m % round_sum(n) } else { m }
}

pub open spec fn final_remainder(n: int, rem: int, walrus: int) -> int
    decreases (n + 1) - walrus,
{
    if walrus < 1 || walrus > n || rem < walrus {
        rem
    } else {
        final_remainder(n, rem - walrus, walrus + 1)
    }
}

impl Solution {
    pub fn presenter_chips(n: u32, m: u32) -> (result: u32)
        requires
            1 <= n <= 50,
            1 <= m <= 10000,
        ensures
            result as int == final_remainder(n as int, after_full_rounds(n as int, m as int), 1),
            result < n,
    {
    }
}

}
