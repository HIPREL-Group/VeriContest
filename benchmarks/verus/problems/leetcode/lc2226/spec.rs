use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pieces_prefix(candies: Seq<i32>, x: int, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::pieces_prefix(candies, x, n - 1) + (candies[n - 1] as int) / x
        }
    }

    pub open spec fn alloc_possible(candies: Seq<i32>, x: int, k: int) -> bool {
        if x <= 0 {
            true
        } else {
            Self::pieces_prefix(candies, x, candies.len() as int) >= k
        }
    }

    pub open spec fn max_elem_prefix(candies: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 1 {
            candies[0] as int
        } else {
            let p = Self::max_elem_prefix(candies, n - 1);
            let c = candies[n - 1] as int;
            if p >= c { p } else { c }
        }
    }

    pub open spec fn max_elem(candies: Seq<i32>) -> int {
        Self::max_elem_prefix(candies, candies.len() as int)
    }

    pub fn maximum_candies(candies: Vec<i32>, k: i64) -> (ans: i32)
        requires
            1 <= candies.len() <= 100000,
            forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
            1 <= k <= 1000000000000,
        ensures
            0 <= ans <= Self::max_elem(candies@),
            Self::alloc_possible(candies@, ans as int, k as int),
            forall |x: int| ans < x <= Self::max_elem(candies@) ==> !#[trigger] Self::alloc_possible(candies@, x, k as int),
    {
    }
}

}
