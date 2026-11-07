impl Solution {
    fn bouquets_by_day(bloom_day: &Vec<i32>, day: i32, k: i32) -> i32
    {
        let mut tokens: i32 = 0;
        let mut i: usize = 0;
        while i < bloom_day.len()
        {
            if bloom_day[i] <= day {
                tokens += 1;
            } else {
                tokens = (tokens / k) * k;
            }
            i += 1;
        }
        tokens / k
    }

    fn required_flowers(m: i32, k: i32) -> u64
    {
        let mut total: u64 = 0;
        let mut i: i32 = 0;
        while i < m
        {
            total = total + (k as u64);
            i += 1;
        }
        total
    }

    pub fn min_days(bloom_day: Vec<i32>, m: i32, k: i32) -> i32
    {
        let n = bloom_day.len();
        let need = Self::required_flowers(m, k);
        if need > n as u64 {
            return -1;
        }

        let mut max_day = bloom_day[0];
        let mut i: usize = 1;
        while i < n
        {
            if bloom_day[i] > max_day {
                max_day = bloom_day[i];
            }
            i += 1;
        }

        let mut left: i32 = 1;
        let mut right: i32 = max_day;

        while left < right
        {
            let mid = left + (right - left) / 2;
            let made = Self::bouquets_by_day(&bloom_day, mid, k);
            if made >= m {
                right = mid;
            } else {
                left = mid + 1;
            }
        }

        left
    }
}
