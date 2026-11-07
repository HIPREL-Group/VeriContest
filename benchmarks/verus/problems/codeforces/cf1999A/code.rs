impl Solution {
    pub fn two_digit_digit_sum(n: i32) -> i32 {
        let tens = n / 10;
        let ones = n % 10;
        tens + ones
    }
}
