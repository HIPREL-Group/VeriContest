impl Solution {
    pub fn find_poisoned_duration(time_series: Vec<i32>, duration: i32) -> i32 {
        let n = time_series.len();
        let mut total: i64 = 0i64;
        let mut i: usize = 0;
        while i < n {
            if i + 1 < n {
                let gap: i64 = time_series[i + 1] as i64 - time_series[i] as i64;
                let contrib: i64 = if gap < duration as i64 { gap } else { duration as i64 };
                total += contrib;
            } else {
                total += duration as i64;
            }
            i += 1;
        }
        total as i32
    }
}
