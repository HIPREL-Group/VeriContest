impl Solution {
    pub fn pivot_integer(n: i32) -> i32 {
        let n_u = n as usize;
        let mut x: usize = 1;
        while x <= n_u {
            let mut left: i32 = 0;
            let mut i: usize = 1;
            while i <= x {
                left = left + i as i32;
                i = i + 1;
            }
            let mut right: i32 = 0;
            i = x;
            while i <= n_u {
                right = right + i as i32;
                i = i + 1;
            }
            if left == right {
                return x as i32;
            }
            x = x + 1;
        }
        -1
    }
}
