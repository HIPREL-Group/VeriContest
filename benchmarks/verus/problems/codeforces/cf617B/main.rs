use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn chocolate_ways(n: usize, a: Vec<i32>) -> i128 {
        let mut ans: u128 = 1;
        let mut prev: i64 = -1;
        let mut seen: usize = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 1 {
                if prev >= 0 {
                    let gap = i as u128 - prev as u128;
                    ans = ans * gap;
                }
                prev = i as i64;
                seen = seen + 1;
            }
            i = i + 1;
        }
        if seen == 0 {
            0
        } else if seen == 1 {
            1
        } else {
            ans as i128
        }
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    lock.read_line(&mut line).expect("read line");
    let n: usize = line.trim().parse().expect("n");
    line.clear();
    lock.read_line(&mut line).expect("read line");
    let mut a: Vec<i32> = Vec::new();
    for s in line.split_whitespace() {
        a.push(s.parse::<i32>().expect("integer"));
    }
    println!("{}", Solution::chocolate_ways(n, a));
}
