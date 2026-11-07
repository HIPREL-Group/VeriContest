impl Solution {
    pub fn max_odd_subarrays(n: usize, p: Vec<i64>) -> usize {
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i + 1 < n {
            if p[i] > p[i + 1] {
                count += 1;
                i += 2;
            } else {
                i += 1;
            }
        }
        count
    }
}
