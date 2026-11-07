impl Solution {
    pub fn hardest_worker(n: i32, logs: Vec<Vec<i32>>) -> i32 {
        let mut best_id: i32 = logs[0][0];
        let mut best_dur: i32 = logs[0][1];
        let mut prev: i32 = logs[0][1];
        let mut i: usize = 1;

        while i < logs.len() {
            let id: i32 = logs[i][0];
            let cur: i32 = logs[i][1];
            let dur: i32 = cur - prev;

            if dur > best_dur || (dur == best_dur && id < best_id) {
                best_dur = dur;
                best_id = id;
            }

            prev = cur;
            i = i + 1;
        }

        best_id
    }
}
