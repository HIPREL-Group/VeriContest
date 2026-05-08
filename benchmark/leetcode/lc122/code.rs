impl Solution {
    pub fn max_profit(prices: Vec<i32>) -> i32 
    {
        let mut buy = prices[0];
        let mut profit = 0;
        
        for i in 1..prices.len() 
        {
            if prices[i] < buy {
                buy = prices[i];
            } else if prices[i] - buy > 0 {
                profit = profit + (prices[i] - buy);
                buy = prices[i];
            }
        }
        profit
    }
}
