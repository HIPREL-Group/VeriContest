impl Solution {
    pub fn number_of_weeks(milestones: Vec<i32>) -> i64 {
        let n = milestones.len();
        let mut total: i64 = 0;
        let mut max_val: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let m = milestones[i] as i64;
            total = total + m;
            if m > max_val {
                max_val = m;
            }
            i += 1;
        }
        let rest = total - max_val;
        if rest >= max_val {
            total
        } else {
            2 * rest + 1
        }
    }
}
