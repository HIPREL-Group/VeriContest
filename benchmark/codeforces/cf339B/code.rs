impl Solution {
    pub fn total_steps(n: i64, targets: Vec<i64>) -> i64 {
        let mut total: i128 = 0;
        let mut cur: i64 = 1;
        let mut i: usize = 0;
        while i < targets.len() {
            let t = targets[i];
            if t >= cur {
                total = total + (t as i128 - cur as i128);
            } else {
                total = total + (n as i128 - cur as i128 + t as i128);
            }
            cur = t;
            i = i + 1;
        }
        total as i64
    }
}
