use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn max_profit(prices: Vec<i32>) -> (res: i32)
        requires
            1 <= prices.len() <= 100_000,
            forall |i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10_000,
        ensures
            res >= 0,
            forall |i: int, j: int| 0 <= i < j < prices.len()
                ==> prices[j] - prices[i] <= res,
            (res == 0) ||
                (exists |i: int, j: int| (0 <= i < j < prices.len()) &&
                    (prices[j] - prices[i] == res)),
    {

    }
}

}