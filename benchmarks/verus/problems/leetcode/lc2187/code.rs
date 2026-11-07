impl Solution {
    fn can_finish(time: &Vec<i32>, t: i64, total: i32) -> bool {
        let mut trips: i64 = 0;
        let target = total as i64;
        let mut i: usize = 0;
        while i < time.len() {
            let add = t / (time[i] as i64);
            if trips >= target - add {
                trips = target;
            } else {
                trips = trips + add;
            }
            i = i + 1;
        }
        trips == target
    }

    pub fn minimum_time(time: Vec<i32>, total_trips: i32) -> i64 {
        let mut left: i64 = 1;
        let mut right: i64 = 100000000000000;
        while left < right {
            let mid = left + (right - left) / 2;
            if Self::can_finish(&time, mid, total_trips) {
                right = mid;
            } else {
                left = mid + 1;
            }
        }
        left
    }
}
