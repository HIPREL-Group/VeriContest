use std::io;

struct Solution;

impl Solution {
    pub fn kth_even_odds(n: u64, k: u64) -> u64 {
        let count_odds = (n + 1) / 2;
        if k <= count_odds {
            2 * k - 1
        } else {
            2 * (k - count_odds)
        }
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
    let k = parts[1];
    println!("{}", Solution::kth_even_odds(n, k));
}
