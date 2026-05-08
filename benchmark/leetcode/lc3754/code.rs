impl Solution {
    pub fn sum_and_multiply(n: i32) -> i64 {
        let mut m: i64 = n as i64;
        let mut place: i64 = 1;
        let mut x: i64 = 0;
        let mut sum: i64 = 0;

        while m > 0 {
            let digit: i64 = m % 10;
            if digit != 0 {
                x = x + digit * place;
                place = place * 10;
                sum = sum + digit;
            }
            m = m / 10;
        }

        x * sum
    }
}
