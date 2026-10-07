impl Solution {
    pub fn good_pair_indices(a: Vec<i64>) -> (i64, i64) {
        let n = a.len();
        let mut min_i = 0usize;
        let mut max_i = 0usize;
        let mut i = 1usize;
        while i < n {
            if a[i] < a[min_i] {
                min_i = i;
            }
            if a[i] > a[max_i] {
                max_i = i;
            }
            i = i + 1;
        }
        ((min_i + 1) as i64, (max_i + 1) as i64)
    }
}
