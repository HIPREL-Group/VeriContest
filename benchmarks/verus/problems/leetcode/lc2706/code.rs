impl Solution {
    pub fn buy_choco(prices: Vec<i32>, money: i32) -> i32 {
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
