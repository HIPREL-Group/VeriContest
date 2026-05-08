use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_accommodation_rooms(p: Vec<i64>, q: Vec<i64>) -> usize {
        let n = p.len();
        let mut cnt = 0usize;
        let mut i = 0usize;
        while i < n {
            let fits = q[i] - p[i] >= 2;
            if fits {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut p: Vec<i64> = Vec::with_capacity(n);
    let mut q: Vec<i64> = Vec::with_capacity(n);
    let mut idx = 0usize;
    while idx < n {
        let line = lines.next().unwrap().unwrap();
        let mut parts = line.split_whitespace();
        let pi: i64 = parts.next().unwrap().parse().unwrap();
        let qi: i64 = parts.next().unwrap().parse().unwrap();
        p.push(pi);
        q.push(qi);
        idx = idx + 1;
    }
    let ans = Solution::count_accommodation_rooms(p, q);
    println!("{}", ans);
}
