use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pow2_spec(exp: int) -> int
        decreases exp,
    {
        if exp <= 0 { 1 } else { 2 * Self::pow2_spec(exp - 1) }
    }

    pub open spec fn bit_price_upto(num: int, i: int) -> int {
        let n = num + 1;
        let block = Self::pow2_spec(i);
        let half = Self::pow2_spec(i - 1);
        let full = (n / block) * half;
        let rem = n % block;
        full + if rem > half { rem - half } else { 0 }
    }

    pub open spec fn total_price_upto(num: int, x: int, i: int) -> int
        decreases 61 - i,
    {
        if i > 60 {
            0
        } else {
            (if i % x == 0 { Self::bit_price_upto(num, i) } else { 0 })
                + Self::total_price_upto(num, x, i + 1)
        }
    }

    pub open spec fn count_price_upto_spec(num: int, x: int) -> int {
        if num < 0 { 0 } else { Self::total_price_upto(num, x, 1) }
    }

    pub open spec fn find_maximum_number_spec(k: int, x: int, result: int) -> bool {
        &&& 1 <= k <= 1_000_000_000_000_000
        &&& 1 <= x <= 8
        &&& 0 <= result <= 1_152_921_504_606_846_975
        &&& Self::count_price_upto_spec(result, x) <= k
        &&& forall |candidate: int|
            0 <= candidate <= 1_152_921_504_606_846_975
                && Self::count_price_upto_spec(candidate, x) <= k
            ==> candidate <= result
    }

    fn pow2(exp: i32) -> (result: i64)
        requires
            0 <= exp <= 60,
    {
        let mut p = 1i64;
        let mut t = 0i32;
        while t < exp {
            p = p.checked_mul(2).unwrap_or(i64::MAX);
            t += 1;
        }
        p
    }

    fn count_price_upto(num: i64, x: i32) -> (result: i64)
        requires
            0 <= num,
            1 <= x <= 8,
    {
        let n = if num == i64::MAX { i64::MAX } else { num + 1 };
        let mut i = 1i32;
        let mut total = 0i64;
        while i <= 60 {
            if i % x == 0 {
                let block = Self::pow2(i);
                let half = Self::pow2(i - 1);
                let full = (n / block).checked_mul(half).unwrap_or(0);
                let rem = n % block;
                let extra = if rem > half { rem.checked_sub(half).unwrap_or(0) } else { 0 };
                let add = full.checked_add(extra).unwrap_or(i64::MAX);
                total = total.checked_add(add).unwrap_or(i64::MAX);
            }
            i += 1;
        }
        total
    }

    pub fn find_maximum_number(k: i64, x: i32) -> (result: i64)
        requires
            1 <= k <= 1_000_000_000_000_000,
            1 <= x <= 8,
        ensures
            Self::find_maximum_number_spec(k as int, x as int, result as int),
            0 <= result as int <= 1_152_921_504_606_846_975,
    {
        let upper = 1_152_921_504_606_846_975i64;
        let mut low = 0i64;
        let mut high = upper;
        let mut ans = 0i64;
        while low <= high {
            let mid = low + (high - low) / 2;
            let price = Self::count_price_upto(mid, x);
            if price <= k {
                ans = mid;
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        }
        ans
    }
}

}
