impl Solution {
    pub fn min_doors_to_lock(l: i32, r: i32, L: i32, R: i32) -> i32 {
        let ma = if l > L {
            l
        } else {
            L
        };
        let mi = if r < R {
            r
        } else {
            R
        };
        let inter = mi - ma + 1;
        if inter <= 0 {
            1
        } else {
            let mut ans: i32 = inter - 1;
            if l != L {
                ans = ans + 1;
            }
            if r != R {
                ans = ans + 1;
            }
            ans
        }
    }
}
