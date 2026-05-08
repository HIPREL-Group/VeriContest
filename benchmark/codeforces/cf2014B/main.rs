use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn major_oak_leaves_even(n: i64, k: i64) -> bool {
        let yr_lo = n - k + 1;
        let odds = (n + 1) / 2 - yr_lo / 2;
        odds % 2 == 0
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
        let n: i64 = parts.next().unwrap().parse().unwrap();
        let k: i64 = parts.next().unwrap().parse().unwrap();
        let yes = Solution::major_oak_leaves_even(n, k);
        if yes {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
