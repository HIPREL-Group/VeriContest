use std::io;

struct Solution;

impl Solution {
    pub fn min_flagstones(n: u64, m: u64, a: u64) -> u64 {
        let rows = (n + a - 1) / a;
        let cols = (m + a - 1) / a;
        rows * cols
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let parts: Vec<u64> = line
        .split_whitespace()
        .map(|s| s.parse().expect("integer"))
        .collect();
    let n = parts[0];
    let m = parts[1];
    let a = parts[2];
    println!("{}", Solution::min_flagstones(n, m, a));
}
