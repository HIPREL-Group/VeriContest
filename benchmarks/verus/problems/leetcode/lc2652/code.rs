impl Solution {
    pub fn sum_of_multiples(n: i32) -> i32 {
        let mut sum: i32 = 0;
        let mut i: i32 = n;
        while i > 0 {
            if i % 3 == 0 || i % 5 == 0 || i % 7 == 0 {
                sum += i;
            }
            i -= 1;
        }
        sum
    }
}
