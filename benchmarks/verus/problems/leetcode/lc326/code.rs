impl Solution {
    pub fn is_power_of_three(n: i32) -> bool {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 3 == 0 {
                x = x / 3;
            }
            x == 1
        }
    }
}
