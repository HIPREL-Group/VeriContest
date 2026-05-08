impl Solution {
    pub fn wait_minutes(now: i32, alarm: i32) -> i32 {
        if alarm >= now {
            alarm - now
        } else {
            alarm + 1440 - now
        }
    }

    pub fn min_wait_minutes(now: i32, alarms: Vec<i32>) -> i32 {
        let n = alarms.len();
        let mut best = Self::wait_minutes(now, alarms[0]);
        let mut i: usize = 1;
        while i < n {
            let d = Self::wait_minutes(now, alarms[i]);
            if d < best {
                best = d;
            }
            i = i + 1;
        }
        best
    }
}
