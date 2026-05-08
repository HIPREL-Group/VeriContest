use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn beautiful_year(n: i32) -> i32 {
        let mut y = n + 1;
        while y <= 9999 {
            let d0 = y % 10;
            let d1 = (y / 10) % 10;
            let d2 = (y / 100) % 10;
            let d3 = (y / 1000) % 10;
            if d0 != d1 && d0 != d2 && d0 != d3 && d1 != d2 && d1 != d3 && d2 != d3 {
                return y;
            }
            y += 1;
        }
        y
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: i32 = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let ans = Solution::beautiful_year(n);
    println!("{}", ans);
}
