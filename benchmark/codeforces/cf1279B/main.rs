use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> i32 {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + a[i];
            i = i + 1;
        }
        if total <= s {
            return 0;
        }
        let mut pref: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            pref = pref + a[j];
            if pref > s {
                let mut best_i: usize = 0;
                let mut t: usize = 1;
                while t <= j {
                    if a[t] > a[best_i] {
                        best_i = t;
                    }
                    t = t + 1;
                }
                return (best_i + 1) as i32;
            }
            j = j + 1;
        }
        0
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut out = String::new();
    for _ in 0..t {
        let ns_line = lines.next().unwrap().unwrap();
        let mut ns_it = ns_line.split_whitespace();
        let n: usize = ns_it.next().unwrap().parse().unwrap();
        let s: i64 = ns_it.next().unwrap().parse().unwrap();
        let a_line = lines.next().unwrap().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut parts = a_line.split_whitespace();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = parts.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::verse_for_santa(n, s, a);
        out.push_str(&format!("{}\n", ans));
    }
    print!("{}", out);
}
