impl Solution {
    pub fn judge_square_sum(c: i32) -> bool
    {
        let c64: i64 = c as i64;

        let mut lo: i64 = 0;
        let mut hi: i64 = if c64 <= 46340 { c64 } else { 46340 };
        while lo <= hi
        {
            let mid: i64 = lo + (hi - lo) / 2;
            let sq: i64 = mid * mid;
            if sq <= c64 {
                lo = mid + 1;
            } else {
                hi = mid - 1;
            }
        }
        let right_init: i64 = hi;

        let mut left: i64 = 0;
        let mut right: i64 = right_init;

        while left <= right
        {
            let sum: i64 = left * left + right * right;
            if sum == c64 {
                return true;
            }
            if sum < c64 {
                left += 1;
            } else {
                right -= 1;
            }
        }
        false
    }
}
