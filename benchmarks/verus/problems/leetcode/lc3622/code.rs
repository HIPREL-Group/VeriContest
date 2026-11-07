impl Solution {
    fn digit_sum_exec(x: u32) -> u32 {
        if x == 0 {
            0
        } else {
            let d = x % 10;
            let q = x / 10;
            let s = Self::digit_sum_exec(q);
            if q == 0 {
                d
            } else {
                d + s
            }
        }
    }

    fn digit_product_exec(x: u32) -> u32 {
        if x == 0 {
            1
        } else {
            let d = x % 10;
            let q = x / 10;
            let p = Self::digit_product_exec(q);
            if q == 0 {
                d
            } else {
                d * p
            }
        }
    }

    pub fn check_divisibility(n: i32) -> bool {
        let x = n as u32;
        let s = Self::digit_sum_exec(x);
        let p = Self::digit_product_exec(x);
        let denom = s + p;
        x % denom == 0
    }
}
