use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn inverse_presents(p: Vec<i32>, n: usize) -> Vec<i32> {
        let mut result = Vec::new();
        let mut i = 0usize;
        while i < n {
            result.push(0i32);
            i += 1;
        }
        i = 0usize;
        while i < n {
            let idx = (p[i] as usize) - 1;
            result[idx] = (i + 1) as i32;
            i += 1;
        }
        result
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let p: Vec<i32> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let result = Solution::inverse_presents(p, n);
    let out: Vec<String> = result.iter().map(|x| x.to_string()).collect();
    println!("{}", out.join(" "));
}
