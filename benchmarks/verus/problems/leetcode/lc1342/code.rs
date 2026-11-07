impl Solution {
    pub fn number_of_steps(num: i32) -> i32 {
        let mut n = num;
        let mut steps = 0i32;
        while n > 0 {
            if n % 2 == 0 {
                n = n / 2;
            } else {
                n = n - 1;
            }
            steps = steps + 1;
        }
        steps
    }
}
