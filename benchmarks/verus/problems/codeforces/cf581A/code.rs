impl Solution {
    pub fn hipster_sock_days(a: i64, b: i64) -> (i64, i64) {
        let fashion: i64;
        let diff: i64;
        if a <= b {
            fashion = a;
            diff = b - a;
        } else {
            fashion = b;
            diff = a - b;
        }
        let same = diff / 2;
        (fashion, same)
    }
}
