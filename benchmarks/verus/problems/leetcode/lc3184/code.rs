impl Solution {
    pub fn count_complete_day_pairs(hours: Vec<i32>) -> i32 {
        let mut count: i32 = 0;
        let n = hours.len();
        for i in 0..n {
            let mut inner: i32 = 0;
            for j in (i + 1)..n {
                if (hours[i] as u32 + hours[j] as u32) % 24 == 0 {
                    inner += 1;
                }
            }
            count += inner;
        }
        count
    }
}
