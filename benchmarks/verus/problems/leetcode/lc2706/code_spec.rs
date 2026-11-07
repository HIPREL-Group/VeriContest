use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn buy_choco(prices: Vec<i32>, money: i32) -> (result: i32)
        requires
            2 <= prices.len() <= 50,
            forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100,
            1 <= money <= 100,
        ensures
            (result == money && forall |i: int, j: int| 0 <= i < prices.len() && 0 <= j < prices.len() && i != j ==> #[trigger] prices[i] + #[trigger] prices[j] > money) ||
            (0 <= result <= money && 
             exists |i: int, j: int| 0 <= i < prices.len() && 0 <= j < prices.len() && i != j && money - (#[trigger] prices[i] + #[trigger] prices[j]) == result &&
             forall |i: int, j: int| 0 <= i < prices.len() && 0 <= j < prices.len() && i != j ==> money - (#[trigger] prices[i] + #[trigger] prices[j]) <= result
            ),
    {
        let n: usize = prices.len();
        let mut min_sum: i32 = 1000;
        let mut i: usize = 0;
        
        while i < n {
            let mut j: usize = 0;
            while j < n {
                if i != j {
                    let cost = prices[i] + prices[j];
                    if cost < min_sum {
                        min_sum = cost;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        
        if min_sum <= money {
            money - min_sum
        } else {
            money
        }
    }
}

}
