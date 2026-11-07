impl Solution {
    pub fn add_digits(n: i32) -> i32 {
        if n == 0 {
            0
        } else if n % 9 == 0 {
            9
        } else {
            n % 9
        }
    }
}
