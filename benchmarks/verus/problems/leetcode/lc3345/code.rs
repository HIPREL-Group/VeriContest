impl Solution {
    fn digit_product_exec(x: i32) -> i32 {
        if x < 10 {
            x
        } else {
            let tens = x / 10;
            let ones = x % 10;
            let mut p: i32 = 0;
            let mut k: i32 = 0;
            while k < ones {
                p = p + tens;
                k = k + 1;
            }
            p
        }
    }

    pub fn smallest_number(n: i32, t: i32) -> i32 {
        let mut candidate = n;
        while candidate < 100 {
            let product = Self::digit_product_exec(candidate);
            if product % t == 0 {
                return candidate;
            }
            candidate += 1;
        }
        100
    }
}
