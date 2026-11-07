impl Solution {
    pub fn count_monobit(n: i32) -> i32 {
        let mut count: i32 = 0;
        let mut value: i32 = 0;
        while value <= n {
            count = count + 1;
            value = value * 2 + 1;
        }
        count
    }
}
