impl Solution {
    pub fn count_bad_prices(a: Vec<i32>) -> i32 {
        let n = a.len();
        if n <= 1 {
            return 0;
        }
        let mut cnt: i32 = 0;
        let mut cur_min = a[n - 1];
        let mut i: usize = n - 2;
        loop {
            if a[i] > cur_min {
                cnt = cnt + 1;
            }
            if a[i] < cur_min {
                cur_min = a[i];
            }
            if i == 0 {
                break;
            }
            i = i - 1;
        }
        cnt
    }
}
