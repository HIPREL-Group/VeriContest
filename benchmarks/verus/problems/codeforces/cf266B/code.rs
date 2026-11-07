impl Solution {
    pub fn queue_after_seconds(queue: Vec<i32>, t: u32) -> Vec<i32> {
        let n = queue.len();
        let mut cur = queue;
        let mut sec: u32 = 0;
        while sec < t {
            let mut next: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                next.push(0i32);
                j = j + 1;
            }
            let mut i: usize = 0;
            while i < n {
                let v = if i + 1 < n && cur[i] == 1 && cur[i + 1] == 0 {
                    0
                } else if i > 0 && cur[i - 1] == 1 && cur[i] == 0 {
                    1
                } else {
                    cur[i]
                };
                next[i] = v;
                i = i + 1;
            }
            cur = next;
            sec = sec + 1;
        }
        cur
    }
}
