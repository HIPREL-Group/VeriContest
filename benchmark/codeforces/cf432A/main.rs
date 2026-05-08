use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_teams(n: usize, k: i32, y: Vec<i64>) -> i32 {
        let mut cnt: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if y[i] <= (5 - k) as i64 {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        (cnt / 3) as i32
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let first = lines.next().unwrap().unwrap();
    let mut parts = first.split_whitespace();
    let n: usize = parts.next().unwrap().parse().unwrap();
    let k: i32 = parts.next().unwrap().parse().unwrap();
    let y: Vec<i64> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::max_teams(n, k, y);
    println!("{}", ans);
}
