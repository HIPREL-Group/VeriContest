use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn celex_distinct_sums(x1: i64, y1: i64, x2: i64, y2: i64) -> i64 {
        let dx = x2 - x1;
        let dy = y2 - y1;
        dx * dy + 1
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut ti = 0usize;
    while ti < t {
        let line = lines.next().unwrap().unwrap();
        let mut parts = line.split_whitespace();
        let x1: i64 = parts.next().unwrap().parse().unwrap();
        let y1: i64 = parts.next().unwrap().parse().unwrap();
        let x2: i64 = parts.next().unwrap().parse().unwrap();
        let y2: i64 = parts.next().unwrap().parse().unwrap();
        let ans = Solution::celex_distinct_sums(x1, y1, x2, y2);
        println!("{}", ans);
        ti = ti + 1;
    }
}
