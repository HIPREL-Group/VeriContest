use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> i64 {
        let mut min_x = xs[0];
        let mut max_x = xs[0];
        let mut i = 1usize;
        while i < 4 {
            if xs[i] < min_x {
                min_x = xs[i];
            }
            if xs[i] > max_x {
                max_x = xs[i];
            }
            i = i + 1;
        }
        let mut min_y = ys[0];
        let mut max_y = ys[0];
        let mut j = 1usize;
        while j < 4 {
            if ys[j] < min_y {
                min_y = ys[j];
            }
            if ys[j] > max_y {
                max_y = ys[j];
            }
            j = j + 1;
        }
        let sx = max_x - min_x;
        let sy = max_y - min_y;
        sx * sy
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let mut xs: Vec<i64> = Vec::new();
        let mut ys: Vec<i64> = Vec::new();
        let mut r = 0usize;
        while r < 4 {
            let line = lines.next().unwrap().unwrap();
            let mut parts = line.split_whitespace();
            let xi: i64 = parts.next().unwrap().parse().unwrap();
            let yi: i64 = parts.next().unwrap().parse().unwrap();
            xs.push(xi);
            ys.push(yi);
            r = r + 1;
        }
        let ans = Solution::axis_aligned_square_area(xs, ys);
        println!("{}", ans);
        k = k + 1;
    }
}
