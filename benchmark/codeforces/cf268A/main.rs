use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_host_guest_uniforms(home: Vec<i32>, away: Vec<i32>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i < n {
            let mut j = 0usize;
            while j < n {
                if i != j && home[i] == away[j] {
                    count += 1;
                }
                j += 1;
            }
            i += 1;
        }
        count
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut home: Vec<i32> = Vec::with_capacity(n);
    let mut away: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let parts: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        home.push(parts[0]);
        away.push(parts[1]);
    }
    let ans = Solution::count_host_guest_uniforms(home, away, n);
    println!("{}", ans);
}
