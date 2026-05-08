use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn leftmost_below(n: usize, b: Vec<i64>) -> bool {
        let mut pm: i64 = b[0];
        let mut i: usize = 1;
        while i < n {
            let m: i64 = pm;
            if !(b[i] - m < m) {
                return false;
            }
            if b[i] < pm {
                pm = b[i];
            }
            i = i + 1;
        }
        true
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut out = String::new();
    for _ in 0..t {
        let n_line = lines.next().unwrap().unwrap();
        let n: usize = n_line.trim().parse().unwrap();
        let b_line = lines.next().unwrap().unwrap();
        let mut b: Vec<i64> = Vec::new();
        for part in b_line.split_whitespace() {
            b.push(part.parse().unwrap());
        }
        let ok = Solution::leftmost_below(n, b);
        if ok {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }
    print!("{}", out);
}
