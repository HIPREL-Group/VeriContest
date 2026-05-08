use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_vacations(n: usize, k: usize, q: i64, a: Vec<i64>) -> i64 {
        let mut pos: usize = 0;
        let mut total: i64 = 0;
        while pos < n {
            if a[pos] > q {
                pos += 1;
            } else {
                let start = pos;
                while pos < n && a[pos] <= q {
                    pos += 1;
                }
                let seg_len = pos - start;
                if seg_len >= k {
                    let x = (seg_len - k) as i64 + 1;
                    total += x * (x + 1) / 2;
                }
            }
        }
        total
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            for _ in 0..t {
                let nkq = lines.next().unwrap().unwrap();
                let mut nkq_it = nkq.split_whitespace();
                let n: usize = nkq_it.next().unwrap().parse().unwrap();
                let k: usize = nkq_it.next().unwrap().parse().unwrap();
                let q: i64 = nkq_it.next().unwrap().parse().unwrap();
                let a_line = lines.next().unwrap().unwrap();
                let a: Vec<i64> = a_line
                    .split_whitespace()
                    .map(|s| s.parse().unwrap())
                    .collect();
                let ans = Solution::count_vacations(n, k, q, a);
                println!("{}", ans);
            }
        }
    }
}
