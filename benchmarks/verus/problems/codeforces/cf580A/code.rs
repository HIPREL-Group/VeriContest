impl Solution {
    pub fn longest_non_decreasing_run(a: Vec<i64>) -> usize {
        let n = a.len();
        let mut best = 1usize;
        let mut cur = 1usize;
        let mut i = 1usize;
        while i < n {
            if a[i] >= a[i - 1] {
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
