impl Solution {
    pub fn consecutive_numbers_sum(n: i32) -> i32 {
        let n64: i64 = n as i64;
        let mut count: i32 = 0;
        let mut k: i64 = 1;
        let mut sum: i64 = 0;
        while sum < n64 {
            let r: i64 = (n64 - sum) % k;
            if r == 0 {
                count = count + 1;
            }
            sum = sum + k;
            k = k + 1;
        }
        count
    }
}