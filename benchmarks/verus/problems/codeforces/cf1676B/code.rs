impl Solution {
    pub fn min_operations_to_equal(candies: Vec<i64>) -> i64 {
        let n = candies.len();
        let mut min_val = candies[0];
        let mut i: usize = 1;
        while i < n {
            if candies[i] < min_val {
                min_val = candies[i];
            }
            i += 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < n {
            ans += candies[i] - min_val;
            i += 1;
        }
        ans
    }
}
