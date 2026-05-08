impl Solution {
    fn pow2(exp: i32) -> i64 {
        let mut p = 1i64;
        let mut t = 0i32;
        while t < exp {
            p = p.checked_mul(2).unwrap_or(i64::MAX);
            t += 1;
        }
        p
    }

    fn count_price_upto(num: i64, x: i32) -> i64 {
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

    pub fn find_maximum_number(k: i64, x: i32) -> i64 {
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
