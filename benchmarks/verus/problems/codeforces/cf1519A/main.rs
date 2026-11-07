use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn beans_distributable(r: i64, b: i64, d: i64) -> bool {
        let mn = if r <= b { r } else { b };
        let mx = if r <= b { b } else { r };
        if mx == mn {
            true
        } else {
            let q = (mx - 1) / mn;
            q <= d
        }
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i64> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        let r = parts[0];
        let b = parts[1];
        let d = parts[2];
        let ans = Solution::beans_distributable(r, b, d);
        if ans {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
