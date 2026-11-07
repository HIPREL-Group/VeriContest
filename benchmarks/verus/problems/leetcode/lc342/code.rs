impl Solution {
    pub fn is_power_of_four(n: i32) -> bool {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 4 == 0 {
                x = x / 4;
            }
            x == 1
        }
    }
}
