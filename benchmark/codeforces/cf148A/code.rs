impl Solution {
    pub fn count_damaged(k: i32, l: i32, m: i32, n: i32, d: i32) -> i32 {
        let mut count = 0i32;
        let mut i = 1i32;
        while i <= d {
            if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }
}
