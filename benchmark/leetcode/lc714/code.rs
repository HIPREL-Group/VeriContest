impl Solution {
    pub fn max_profit(prices: Vec<i32>, fee: i32) -> i32 {
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
