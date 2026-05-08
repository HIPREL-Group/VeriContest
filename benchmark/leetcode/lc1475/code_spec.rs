use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn first_le(prices: Seq<i32>, i: int, j: int) -> int
        decreases prices.len() - j,
    {
        if j >= prices.len() {
            prices.len() as int
        } else if prices[j] <= prices[i] {
            j
        } else {
            Self::first_le(prices, i, j + 1)
        }
    }

    pub open spec fn expected_price(prices: Seq<i32>, i: int) -> int {
        let j = Self::first_le(prices, i, i + 1);
        if j < prices.len() as int {
            prices[i] as int - prices[j] as int
        } else {
            prices[i] as int
        }
    }

    pub fn final_prices(prices: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= prices.len() <= 500,
            forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 1000,
        ensures
            result.len() == prices.len(),
            forall|i: int|
                0 <= i < result.len() ==> #[trigger] result[i] as int == Self::expected_price(
                    prices@,
                    i,
                ),
    {
        let n = prices.len();
        let mut answer: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            answer.push(prices[idx]);
            idx += 1;
        }
        let mut stack: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            while stack.len() > 0 && prices[i] <= prices[stack[stack.len() - 1]] {
                let top_idx = stack[stack.len() - 1];
                answer.set(top_idx, prices[top_idx] - prices[i]);
                stack.pop();
            }
            stack.push(i);
            i += 1;
        }
        answer
    }
}

}
