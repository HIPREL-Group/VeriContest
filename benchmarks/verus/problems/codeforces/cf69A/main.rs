use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_equilibrium(vec: Vec<i32>, n: usize) -> bool {
        let mut sum_x = 0i64;
        let mut sum_y = 0i64;
        let mut sum_z = 0i64;
        let mut i = 0usize;
        while i < n {
            sum_x += vec[3 * i] as i64;
            sum_y += vec[3 * i + 1] as i64;
            sum_z += vec[3 * i + 2] as i64;
            i += 1;
        }
        sum_x == 0 && sum_y == 0 && sum_z == 0
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut vec: Vec<i32> = Vec::with_capacity(3 * n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        vec.push(parts[0]);
        vec.push(parts[1]);
        vec.push(parts[2]);
    }
    let ans = Solution::is_equilibrium(vec, n);
    println!("{}", if ans { "YES" } else { "NO" });
}
