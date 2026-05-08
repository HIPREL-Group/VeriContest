impl Solution {
    pub fn max_profit(prices: Vec<i32>) -> i32 {
        let n = prices.len();

        let mut forward: Vec<i32> = Vec::with_capacity(n);
        forward.push(0i32);
        let mut min_price = prices[0];
        for i in 1..n {
            if prices[i] < min_price { min_price = prices[i]; }
            let profit = prices[i] - min_price;
            let prev = forward[i - 1];
            let val = if profit > prev { profit } else { prev };
            forward.push(val);
        }

        let mut backward: Vec<i32> = Vec::with_capacity(n);
        for i in 0..n {
            backward.push(0i32);
        }
        let mut max_price = prices[n - 1];
        for i in 1..n {
            let idx = n - 1 - i;
            if prices[idx] > max_price { max_price = prices[idx]; }
            let profit = max_price - prices[idx];
            let next = backward[idx + 1];
            let val = if profit > next { profit } else { next };
            backward[idx] = val;
        }

        let mut res: i32 = 0;
        for i in 0..n {
            let total = forward[i] + backward[i];
            if total > res { res = total; }
        }
        res
    }
}
