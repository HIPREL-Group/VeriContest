use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn hipster_sock_days(a: i64, b: i64) -> (i64, i64) {
        let fashion: i64;
        let diff: i64;
        if a <= b {
            fashion = a;
            diff = b - a;
        } else {
            fashion = b;
            diff = a - b;
        }
        let same = diff / 2;
        (fashion, same)
    }
}

fn main() {
    let stdin = io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).unwrap();
    let mut it = line.split_whitespace();
    let a: i64 = it.next().unwrap().parse().unwrap();
    let b: i64 = it.next().unwrap().parse().unwrap();
    let (x, y) = Solution::hipster_sock_days(a, b);
    println!("{} {}", x, y);
}
