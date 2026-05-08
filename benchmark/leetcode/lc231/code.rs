impl Solution {
    pub fn is_power_of_two(n: i32) -> bool {
        if n <= 0 {
            false
        } else {
            let mut x = n;
            while x > 1 && x % 2 == 0 {
                x = x / 2;
            }
            x == 1
        }
    }
}
