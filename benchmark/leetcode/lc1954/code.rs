impl Solution {
    pub fn minimum_perimeter(needed_apples: i64) -> i64 {
        let mut lo: i64 = 1;
        let mut hi: i64 = 100_000;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let apples_mid = 2 * mid * (mid + 1) * (2 * mid + 1);
            if apples_mid >= needed_apples {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        lo * 8
    }
}
