use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn total_road_width(a: Vec<i32>, n: usize, h: i32) -> i32 {
        let mut sum = 0i32;
        let mut i = 0usize;
        while i < n {
            if a[i] <= h {
                sum += 1;
            } else {
                sum += 2;
            }
            i += 1;
        }
        sum
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let first: Vec<usize> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let n = first[0];
    let h: i32 = first[1] as i32;
    let a: Vec<i32> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let ans = Solution::total_road_width(a, n, h);
    println!("{}", ans);
}
