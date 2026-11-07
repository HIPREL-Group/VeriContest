use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn longest_non_decreasing_run(a: Vec<i64>) -> usize {
        let n = a.len();
        let mut best = 1usize;
        let mut cur = 1usize;
        let mut i = 1usize;
        while i < n {
            if a[i] >= a[i - 1] {
                cur = cur + 1;
            } else {
                cur = 1;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let mut a: Vec<i64> = Vec::with_capacity(n);
    for s in line.split_whitespace() {
        a.push(s.parse().unwrap());
    }
    let ans = Solution::longest_non_decreasing_run(a);
    println!("{}", ans);
}
