impl Solution {
    pub fn final_prices(prices: Vec<i32>) -> Vec<i32> {
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
                answer[top_idx] = prices[top_idx] - prices[i];
                stack.pop();
            }
            stack.push(i);
            i += 1;
        }
        answer
    }
}
