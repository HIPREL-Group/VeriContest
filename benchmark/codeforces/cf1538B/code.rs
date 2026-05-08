impl Solution {
    pub fn min_friends_for_equal_candies(a: Vec<i64>) -> i32 {
        let n = a.len();
        let ni = n as i64;
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            sum = sum + a[i];
            i = i + 1;
        }
        if sum % ni != 0 {
            return -1;
        }
        let t = sum / ni;
        let mut cnt: i32 = 0;
        i = 0;
        while i < n {
            if a[i] > t {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}
