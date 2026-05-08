impl Solution {
    pub fn remove_zeros(n: i64) -> i64 {
        let mut m: i64 = n;
        let mut place: i64 = 1;
        let mut res: i64 = 0;
        while m > 0 {
            let digit: i64 = m % 10;
            if digit != 0 {
                res = res + digit * place;
                place = place * 10;
            }
            m = m / 10;
        }
        res
    }
}
