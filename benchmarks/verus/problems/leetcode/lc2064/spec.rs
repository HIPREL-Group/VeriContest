use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div(x: int, d: int) -> int {
        (x + d - 1) / d
    }

    pub open spec fn stores_needed_prefix(quantities: Seq<i32>, x: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::stores_needed_prefix(quantities, x, n - 1)
                + Self::ceil_div(quantities[n - 1] as int, x)
        }
    }

    pub open spec fn stores_needed(quantities: Seq<i32>, x: int) -> int {
        Self::stores_needed_prefix(quantities, x, quantities.len() as int)
    }

    pub fn minimized_maximum(n: i32, quantities: Vec<i32>) -> (ans: i32)
        requires
            1 <= quantities.len() <= n <= 100000,
            forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
        ensures
            1 <= ans <= 100000,
            Self::stores_needed(quantities@, ans as int) <= n as int,
            forall |x: int| 1 <= x < ans ==> #[trigger] Self::stores_needed(quantities@, x) > n as int,
    {
    }
}

}
