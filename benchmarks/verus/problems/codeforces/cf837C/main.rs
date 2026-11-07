use std::io::{self, BufRead};

struct Solution;

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

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(line1)) = lines.next() {
        let parts: Vec<usize> = line1.split_whitespace().filter_map(|s| s.parse().ok()).collect();
        if parts.len() >= 3 {
            let n = parts[0];
            let a = parts[1] as i32;
            let b = parts[2] as i32;
            let mut x = Vec::new();
            let mut y = Vec::new();
            for _ in 0..n {
                if let Some(Ok(line)) = lines.next() {
                    let p: Vec<i32> = line.split_whitespace().filter_map(|s| s.parse().ok()).collect();
                    if p.len() >= 2 {
                        x.push(p[0]);
                        y.push(p[1]);
                    }
                }
            }
            println!("{}", Solution::two_seals(n, a, b, x, y));
        }
    }
}
