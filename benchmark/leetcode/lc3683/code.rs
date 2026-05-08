impl Solution {
    pub fn earliest_time(tasks: Vec<Vec<i32>>) -> i32 {
        let n = tasks.len();
        let mut best = tasks[0][0] + tasks[0][1];
        let mut i: usize = 1;
        while i < n {
            let cur = tasks[i][0] + tasks[i][1];
            if cur < best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
