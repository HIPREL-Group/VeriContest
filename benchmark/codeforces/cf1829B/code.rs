impl Solution {
    pub fn longest_blank_space(a: &Vec<i32>) -> i32 {
        let n = a.len();
        let mut best: i32 = 0;
        let mut cur: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 0 {
                cur = cur + 1;
            } else {
                cur = 0;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}
