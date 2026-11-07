use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn pluses_minuses_total_steps(deltas: Vec<i32>) -> i64 {
        let n = deltas.len();
        let mut ans: i64 = n as i64;
        let mut cur: i64 = 0;
        let mut mn: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let i0 = i;
            cur = cur + deltas[i0] as i64;
            if cur < mn {
                ans = ans + (i0 + 1) as i64;
                mn = cur;
            }
            i = i + 1;
        }
        ans
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut out = String::new();
    for _ in 0..t {
        let s = lines.next().unwrap().unwrap();
        let mut deltas: Vec<i32> = Vec::new();
        for ch in s.trim().chars() {
            if ch == '+' {
                deltas.push(1);
            } else {
                deltas.push(-1);
            }
        }
        let r = Solution::pluses_minuses_total_steps(deltas);
        out.push_str(&format!("{}\n", r));
    }
    print!("{}", out);
}
