impl Solution {
    pub fn sum_base(n: i32, k: i32) -> i32 {
        let mut sum: i32 = 0;
        let mut cur: i32 = n;
        while cur > 0 {
            sum = sum + cur % k;
            cur = cur / k;
        }
        sum
    }
}
