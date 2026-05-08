use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn impossible_face_counts(total: i64, maxima: Vec<i64>) -> Vec<i64> {
        let n = maxima.len();
        let mut sum_all = 0i64;
        let mut i = 0usize;
        while i < n {
            sum_all += maxima[i];
            i += 1;
        }
        let mut res = Vec::new();
        i = 0;
        while i < n {
            let mut lo = total - (sum_all - maxima[i]);
            if lo < 1 {
                lo = 1;
            }
            let mut hi = total - (n as i64 - 1);
            if hi > maxima[i] {
                hi = maxima[i];
            }
            let bad = if hi < lo {
                maxima[i]
            } else if hi == maxima[i] {
                lo - 1
            } else {
                lo - 1 + maxima[i] - hi
            };
            res.push(bad);
            i += 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n: usize = it.next().expect("n").parse().expect("parse n");
    let total: i64 = it.next().expect("A").parse().expect("parse A");
    let mut maxima = Vec::new();
    let mut i = 0usize;
    while i < n {
        maxima.push(it.next().expect("di").parse().expect("parse di"));
        i += 1;
    }
    let ans = Solution::impossible_face_counts(total, maxima);
    let mut out = String::new();
    let mut j = 0usize;
    while j < ans.len() {
        if j > 0 {
            out.push(' ');
        }
        out.push_str(&ans[j].to_string());
        j += 1;
    }
    println!("{}", out);
}
