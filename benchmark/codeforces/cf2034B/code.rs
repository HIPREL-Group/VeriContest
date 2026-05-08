impl Solution {
    pub fn min_timar_operations(s: Vec<i32>, m: usize, k: usize) -> i64 {
        let n = s.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let mut cnt: usize = 0;
        let mut skip: usize = 0;
        while i < n {
            if skip > 0 {
                skip = skip - 1;
                cnt = 0;
            } else if s[i] == 0 {
                if cnt + 1 == m {
                    ans = ans + 1;
                    cnt = 0;
                    skip = k - 1;
                } else {
                    cnt = cnt + 1;
                }
            } else {
                cnt = 0;
            }
            i = i + 1;
        }
        ans
    }
}
