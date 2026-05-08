pub struct Solution;

impl Solution {
    pub fn get_descent_periods(prices: Vec<i32>) -> i64 {
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
