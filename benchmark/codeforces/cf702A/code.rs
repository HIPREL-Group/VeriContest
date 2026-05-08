impl Solution {
    pub fn max_increasing_subarray_len(n: usize, a: Vec<i64>) -> usize {
        let mut best = 1usize;
        let mut cur = 1usize;
        let mut i = 1usize;
        while i < n {
            if a[i] > a[i - 1] {
                cur = cur + 1;
            } else {
                cur = 1;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
