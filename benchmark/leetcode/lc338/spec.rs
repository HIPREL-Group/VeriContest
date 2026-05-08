use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn popcount(x: int) -> int
        decreases x,
    {
        if x <= 0 { 0 } else { (x % 2) + Self::popcount(x / 2) }
    }

    pub fn count_bits(n: i32) -> (res: Vec<i32>)
        requires
            0 <= n <= 100000,
        ensures
            res.len() == n + 1,
            forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] as int == Self::popcount(i),
    {
    }
}

}
