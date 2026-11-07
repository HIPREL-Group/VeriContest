impl Solution {
    pub fn distribute_candies(n: i32, limit: i32) -> i32 {
        let mut a: i32 = 0;
        let mut total: i32 = 0;
        while a <= limit {
            let mut b: i32 = 0;
            while b <= limit {
                let c = n - a - b;
                if 0 <= c && c <= limit {
                    total = total + 1;
                }
                b = b + 1;
            }
            a = a + 1;
        }
        total
    }
}
