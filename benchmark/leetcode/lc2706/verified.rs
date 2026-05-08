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
        
        while i < n
            invariant
                n == prices.len(),
                2 <= n <= 50,
                0 <= i <= n,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] prices[k] <= 100,
                2 <= min_sum <= 1000,
                min_sum != 1000 ==> exists |a: int, b: int| 0 <= a < i && 0 <= b < n && a != b && #[trigger] prices[a] + #[trigger] prices[b] == min_sum,
                forall |a: int, b: int| 0 <= a < i && 0 <= b < n && a != b ==> #[trigger] prices[a] + #[trigger] prices[b] >= min_sum,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < n
                invariant
                    n == prices.len(),
                    2 <= n <= 50,
                    0 <= i < n,
                    0 <= j <= n,
                    forall |k: int| 0 <= k < n ==> 1 <= #[trigger] prices[k] <= 100,
                    2 <= min_sum <= 1000,
                    min_sum != 1000 ==> (
                        (exists |a: int, b: int| 0 <= a < i && 0 <= b < n && a != b && #[trigger] prices[a] + #[trigger] prices[b] == min_sum) ||
                        (exists |b: int| 0 <= b < j && i as int != b && #[trigger] prices[i as int] + #[trigger] prices[b] == min_sum)
                    ),
                    forall |a: int, b: int| 0 <= a < i && 0 <= b < n && a != b ==> #[trigger] prices[a] + #[trigger] prices[b] >= min_sum,
                    forall |b: int| 0 <= b < j && i as int != b ==> #[trigger] prices[i as int] + #[trigger] prices[b] >= min_sum,
                decreases n - j,
            {
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
            assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies money - (#[trigger] prices[a] + #[trigger] prices[b]) <= money - min_sum by {
                assert(prices[a] + prices[b] >= min_sum);
            };
            money - min_sum
        } else {
            money
        }
    }
}

}
