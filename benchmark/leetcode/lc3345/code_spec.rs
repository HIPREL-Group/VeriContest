use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_product(n: int) -> int
        recommends
            1 <= n <= 100,
    {
        if n < 10 {
            n
        } else if n < 100 {
            (n / 10) * (n % 10)
        } else {
            0
        }
    }

    fn digit_product_exec(x: i32) -> (product: i32)
        requires
            1 <= x <= 99,
        ensures
            product as int == Self::digit_product(x as int),
            0 <= product <= 81,
    {
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

    pub fn smallest_number(n: i32, t: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            1 <= t <= 10,
        ensures
            n <= result <= 100,
            Self::digit_product(result as int) % t as int == 0,
            forall|m: int| n as int <= m < result as int ==> #[trigger] (Self::digit_product(m) % t as int) != 0,
    {
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

}
