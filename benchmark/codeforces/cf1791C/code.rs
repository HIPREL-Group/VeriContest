impl Solution {
    pub fn shortest_original(n: usize, s: Vec<i64>) -> usize {
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            if s[left] + s[right] != 1 {
                return right - left + 1;
            }
            left += 1;
            right -= 1;
        }
        if left > right {
            0
        } else {
            right - left + 1
        }
    }
}
