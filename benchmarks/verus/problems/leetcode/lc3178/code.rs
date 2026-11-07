impl Solution {
    pub fn number_of_child(n: i32, k: i32) -> i32 {
        let m = 2 * n - 2;
        let t = k % m;
        if t < n {
            t
        } else {
            2 * n - t - 2
        }
    }
}
