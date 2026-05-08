impl Solution {
    pub fn decimal_representation(n: i32) -> Vec<i32> {
        let mut m: i64 = n as i64;
        let mut place: i64 = 1;
        let mut asc: Vec<i32> = Vec::new();
        while m > 0 {
            let digit: i64 = m % 10;
            if digit != 0 {
                asc.push((digit * place) as i32);
            }
            m = m / 10;
            place = place * 10;
        }
        let mut result: Vec<i32> = Vec::with_capacity(asc.len());
        let mut i: usize = asc.len();
        while i > 0 {
            i = i - 1;
            let x = asc[i];
            result.push(x);
        }
        result
    }
}
