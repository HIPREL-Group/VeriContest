impl Solution {
    pub fn sum_odd_length_subarrays(arr: Vec<i32>) -> i32 {
        let n = arr.len();
        let mut total: i64 = 0;
        let mut start: usize = 0;
        while start < n {
            let mut sum: i32 = 0;
            let mut end: usize = start;
            let total_before_start: i64 = total;
            while end < n {
                sum += arr[end];
                let len = end - start + 1;
                if len % 2 == 1 {
                    total += sum as i64;
                }
                end += 1;
            }
            start += 1;
        }
        total as i32
    }
}
