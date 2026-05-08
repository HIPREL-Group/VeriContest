impl Solution {
    pub fn can_shower(s: i64, m: i64, l: Vec<i64>, r: Vec<i64>) -> bool {
        let n = l.len();
        let mut max_gap: i64 = l[0];
        let mut i: usize = 0;
        while i < n {
            let end_pos: i64 = if i + 1 == n { m } else { l[i + 1] };
            let gap = end_pos - r[i];
            if gap > max_gap {
                max_gap = gap;
            }
            i = i + 1;
        }
        max_gap >= s
    }
}
