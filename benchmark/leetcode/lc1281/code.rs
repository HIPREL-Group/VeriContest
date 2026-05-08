impl Solution {
    pub fn subtract_product_and_sum(n: i32) -> i32 {
        let mut num: i32 = n;
        let mut product: i64 = 1;
        let mut sum: i64 = 0;
        let mut cnt: u32 = 0;

        while cnt < 6 {
            let digit = num % 10;
            product = product * digit as i64;
            sum = sum + digit as i64;
            num = num / 10;
            cnt = cnt + 1;
        }

        (product - sum) as i32
    }
}
