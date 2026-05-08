use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_passengers(exits: Vec<i32>, entries: Vec<i32>) -> i32 {
        let n = exits.len();
        let mut max_val = 0i32;
        let mut current = 0i32;
        let mut i = 0usize;
        while i < n {
            current = current - exits[i] + entries[i];
            if current > max_val {
                max_val = current;
            }
            i += 1;
        }
        max_val
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut exits: Vec<i32> = Vec::with_capacity(n);
    let mut entries: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        exits.push(parts[0]);
        entries.push(parts[1]);
    }
    let ans = Solution::max_passengers(exits, entries);
    println!("{}", ans);
}
