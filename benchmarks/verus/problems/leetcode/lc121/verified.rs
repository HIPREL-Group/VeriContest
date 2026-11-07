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
        let mut buy = prices[0];
        let mut profit = 0;
        for i in 1..prices.len()
            invariant
                1 <= prices.len() <= 100_000,
                forall |k: int| 0 <= k < prices.len() ==> 0 <= #[trigger] prices[k] <= 10_000,
                0 <= buy <= 10_000,
                forall |k: int| 0 <= k < i ==> buy <= prices[k],
                exists |k: int| 0 <= k < i && prices[k] == buy,
                0 <= profit,
                forall |ii: int, jj: int| 0 <= ii < jj < i
                    ==> prices[jj] - prices[ii] <= profit,
                profit > 0 ==> exists |ii: int, jj: int| (0 <= ii < jj < i)
                    && (prices[jj] - prices[ii] == profit),
        {
            if prices[i] < buy {
                buy = prices[i];
            } else if prices[i] - buy > profit {
                profit = prices[i] - buy;
            }
        }
        profit
    }
}

}