impl Solution {
    pub fn sum_multiples_exec(x: i32, n: i32) -> i32 {
        let k = n / x;
        x * k * (k + 1) / 2
    }

    pub fn max_multiples_sum_x(n: i32) -> i32 {
        let mut best_x: i32 = 2;
        let mut best_sum: i32 = Solution::sum_multiples_exec(2, n);
        let mut x: i32 = 3;
        while x <= n {
            let s = Solution::sum_multiples_exec(x, n);
            if s > best_sum {
                best_sum = s;
                best_x = x;
            }
            x = x + 1;
        }
        best_x
    }
}
