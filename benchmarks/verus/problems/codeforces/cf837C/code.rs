impl Solution {
    pub fn fits_oriented(w1: i32, h1: i32, w2: i32, h2: i32, a: i32, b: i32) -> bool {
        (w1 + w2 <= a && h1 <= b && h2 <= b) ||
        (h1 + h2 <= b && w1 <= a && w2 <= a)
    }

    pub fn fits(x1: i32, y1: i32, x2: i32, y2: i32, a: i32, b: i32) -> bool {
        Solution::fits_oriented(x1, y1, x2, y2, a, b) ||
        Solution::fits_oriented(y1, x1, x2, y2, a, b) ||
        Solution::fits_oriented(x1, y1, y2, x2, a, b) ||
        Solution::fits_oriented(y1, x1, y2, x2, a, b)
    }

    pub fn two_seals(n: usize, a: i32, b: i32, x: Vec<i32>, y: Vec<i32>) -> i32 {
        let mut ans: i32 = 0;
        let mut i = 0;
        while i < n {
            let mut j = i + 1;
            while j < n {
                let is_fit = Solution::fits(x[i], y[i], x[j], y[j], a, b);
                if is_fit {
                    let xi = x[i]; let yi = y[i]; let xj = x[j]; let yj = y[j];
                    let area_val: i32 = xi * yi + xj * yj;
                    if area_val > ans {
                        ans = area_val;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        ans
    }
}
