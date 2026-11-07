impl Solution {
    pub fn pass_the_pillow(n: i32, time: i32) -> i32 {
        let m = 2 * n - 2;
        let t = time % m;
        if t < n {
            t + 1
        } else {
            2 * n - t - 1
        }
    }
}
