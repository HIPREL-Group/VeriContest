impl Solution {
    pub fn is_valley(n: usize, a: Vec<i64>) -> i64 {
        let mut count: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let block_start = i;
            while i < n && a[i] == a[block_start] {
                i += 1;
            }
            let block_end = i - 1;
            let left_ok = block_start == 0 || a[block_start - 1] > a[block_start];
            let right_ok = block_end == n - 1 || a[block_end] < a[block_end + 1];
            if left_ok && right_ok {
                count += 1;
            }
        }
        count
    }
}
