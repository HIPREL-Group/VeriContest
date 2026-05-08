impl Solution {
    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> usize {
        let mut cur: i64 = 0;
        let mut j: usize = 0;
        while j < k {
            cur = cur + s[j];
            j += 1;
        }

        let mut best: i64 = cur;
        let mut left: usize = 0;

        while left + k < n {
            let next = cur - s[left] + s[left + k];
            cur = next;
            left += 1;
            if cur < best {
                best = cur;
            }
        }

        best as usize
    }
}