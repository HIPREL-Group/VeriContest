impl Solution {
    pub fn two_egg_drop(n: i32) -> i32 {
        let mut n = n;
        let mut ans: i32 = 0;
        while n > 0 {
            ans += 1;
            n -= ans;
        }
        ans
    }
}
