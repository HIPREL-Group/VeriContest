impl Solution {
    pub fn can_send_all_messages(m: Vec<i64>, f: i64, a: i64, b: i64) -> bool {
        let n = m.len();
        let mut spent: i64 = 0;
        let mut prev: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let cur = m[i];
            let gap = m[i] - prev;
            let keep = gap * a;
            let step = if keep < b { keep } else { b };
            spent = spent + step;
            prev = m[i];
            i = i + 1;
        }
        spent < f
    }
}
