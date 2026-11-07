impl Solution {
    pub fn button_with_longest_time(events: Vec<Vec<i32>>) -> i32 {
        let n = events.len();
        let mut best_idx: i32 = events[0][0];
        let mut best_time: i32 = events[0][1];
        let mut prev_time: i32 = events[0][1];
        let mut i: usize = 1;
        while i < n {
            let current_idx: i32 = events[i][0];
            let current_time: i32 = events[i][1] - prev_time;
            if current_time > best_time {
                best_time = current_time;
                best_idx = current_idx;
            } else if current_time == best_time && current_idx < best_idx {
                best_idx = current_idx;
            }
            prev_time = events[i][1];
            i = i + 1;
        }
        best_idx
    }
}
