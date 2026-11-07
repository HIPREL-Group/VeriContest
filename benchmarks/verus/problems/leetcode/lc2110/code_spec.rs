use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn run_length(prices: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if i >= prices.len() {
        0
    } else if prices[i - 1] - prices[i] == 1 {
        run_length(prices, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn total_periods(prices: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        total_periods(prices, n - 1) + run_length(prices, n - 1)
    }
}

impl Solution {
    pub fn get_descent_periods(prices: Vec<i32>) -> (total: i64)
        requires
            1 <= prices.len() <= 100_000,
            forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100_000,
        ensures
            total == total_periods(prices@, prices.len() as int),
    {
        let n = prices.len();
        let mut total: i64 = 0;
        let mut run_len: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if i > 0 && prices[i - 1] - prices[i] == 1 {
                run_len += 1;
            } else {
                run_len = 1;
            }
            total += run_len;
            i += 1;
        }
        total
    }
}

} 
