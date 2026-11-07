impl Solution {
    pub fn count_accommodation_rooms(p: Vec<i64>, q: Vec<i64>) -> usize {
        let n = p.len();
        let mut cnt = 0usize;
        let mut i = 0usize;
        while i < n {
            let fits = q[i] - p[i] >= 2;
            if fits {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}
