impl Solution {
    pub fn is_perfect_square(num: i32) -> bool {
        let n: i64 = num as i64;        
        let (mut l, mut r) = (1i64, n);

        while l <= r {
            let mid: i64 = l + (r - l) / 2;
            let sq: i64 = mid * mid;
            if sq == n {
                return true;
            } else if sq < n {
                l = mid + 1;
            } else {
                r = mid - 1;
            }
        }
        false
    }
}