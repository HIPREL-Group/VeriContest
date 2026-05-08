use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min_prefix(prices: Seq<i32>, i: int) -> int
        decreases i
    {
        if i <= 0 { prices[0] as int }
        else {
            let rest = Self::min_prefix(prices, i - 1);
            if (prices[i] as int) < rest { prices[i] as int } else { rest }
        }
    }

    pub open spec fn forward_max(prices: Seq<i32>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0 }
        else {
            let sell_today = prices[i] as int - Self::min_prefix(prices, i);
            let prev = Self::forward_max(prices, i - 1);
            if sell_today > prev { sell_today } else { prev }
        }
    }

    pub open spec fn max_suffix(prices: Seq<i32>, i: int) -> int
        decreases prices.len() - i
    {
        if i >= prices.len() - 1 { prices[prices.len() as int - 1] as int }
        else {
            let rest = Self::max_suffix(prices, i + 1);
            if (prices[i] as int) > rest { prices[i] as int } else { rest }
        }
    }

    pub open spec fn backward_max(prices: Seq<i32>, i: int) -> int
        decreases prices.len() - i
    {
        if i >= prices.len() - 1 { 0 }
        else {
            let buy_today = Self::max_suffix(prices, i) - prices[i] as int;
            let next = Self::backward_max(prices, i + 1);
            if buy_today > next { buy_today } else { next }
        }
    }

    pub open spec fn best_combined(prices: Seq<i32>, k: int) -> int
        decreases prices.len() - k
    {
        if k >= prices.len() { 0 }
        else {
            let here = Self::forward_max(prices, k) + Self::backward_max(prices, k);
            let rest = Self::best_combined(prices, k + 1);
            if here > rest { here } else { rest }
        }
    }

    pub fn max_profit(prices: Vec<i32>) -> (result: i32)
        requires
            1 <= prices.len() <= 100_000,
            forall |i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 100_000,
        ensures
            result >= 0,
            result as int == Self::best_combined(prices@, 0),
    {
    }
}

} 
