use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn spec_cash(prices: Seq<i32>, fee: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            0
        } else {
            Self::spec_max(
                Self::spec_cash(prices, fee, i - 1),
                Self::spec_hold(prices, fee, i - 1) + prices[i] as int - fee
            )
        }
    }

    pub open spec fn spec_hold(prices: Seq<i32>, fee: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            -(prices[0] as int)
        } else {
            Self::spec_max(
                Self::spec_hold(prices, fee, i - 1),
                Self::spec_cash(prices, fee, i - 1) - prices[i] as int
            )
        }
    }

    pub fn max_profit(prices: Vec<i32>, fee: i32) -> (res: i32)
        requires
            1 <= prices.len() <= 50_000,
            forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] < 50_000,
            0 <= fee < 50_000,
        ensures
            res as int == Self::spec_cash(prices@, fee as int, (prices.len() - 1) as int),
    {
        let mut cash: i32 = 0;
        let mut hold: i32 = -prices[0];
        let n = prices.len();
        for i in 1..n {
            let prev_cash = cash;
            let prev_hold = hold;
            if prev_hold + prices[i] - fee > prev_cash {
                cash = prev_hold + prices[i] - fee;
            }
            if prev_cash - prices[i] > prev_hold {
                hold = prev_cash - prices[i];
            }
        }
        cash
    }
}

}
