use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_position(pos: int, n: int, a: int, b: int) -> bool {
    pos - 1 >= a && n - pos <= b
}

pub open spec fn count_valid_positions(k: int, n: int, a: int, b: int) -> nat
    decreases k,
{
    if k <= 0 {
        0nat
    } else {
        count_valid_positions(k - 1, n, a, b)
            + if is_valid_position(k, n, a, b) { 1nat } else { 0nat }
    }
}

impl Solution {
    pub fn count_positions(n: i32, a: i32, b: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            0 <= a < n,
            0 <= b < n,
        ensures
            result as int == count_valid_positions(n as int, n as int, a as int, b as int),
            result >= 0,
            result <= n,
    {
        let min_pos = if a + 1 >= n - b { a + 1 } else { n - b };
        n - min_pos + 1
    }
}

}
