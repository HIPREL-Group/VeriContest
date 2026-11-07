use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn frog_position_after_jumps(a: i64, b: i64, k: i64) -> i64 {
        let na = (k + 1) / 2;
        let nb = k / 2;
        na * a - nb * b
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let line = lines.next().unwrap().unwrap();
        let mut parts = line.split_whitespace();
        let a: i64 = parts.next().unwrap().parse().unwrap();
        let b: i64 = parts.next().unwrap().parse().unwrap();
        let k: i64 = parts.next().unwrap().parse().unwrap();
        let ans = Solution::frog_position_after_jumps(a, b, k);
        println!("{}", ans);
        i = i + 1;
    }
}
