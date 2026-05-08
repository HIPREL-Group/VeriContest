use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_median(n: usize, k: i64, a: Vec<i64>) -> i64 {
        let m = n / 2;
        let mut lo: i64 = a[m];
        let mut hi: i64 = a[m] + k;
        while lo < hi {
            let mid_val: i64 = lo + (hi - lo + 1) / 2;
            let mut cost: i64 = 0;
            let mut i: usize = m;
            while i < n {
                if mid_val > a[i] {
                    cost = cost + (mid_val - a[i]);
                }
                i = i + 1;
            }
            if cost <= k {
                lo = mid_val;
            } else {
                hi = mid_val - 1;
            }
        }
        lo
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let first_line = lines.next().unwrap().unwrap();
    let mut it = first_line.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let k: i64 = it.next().unwrap().parse().unwrap();
    let second_line = lines.next().unwrap().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut parts = second_line.split_whitespace();
    let mut i: usize = 0;
    while i < n {
        let v: i64 = parts.next().unwrap().parse().unwrap();
        a.push(v);
        i = i + 1;
    }
    a.sort();
    println!("{}", Solution::max_median(n, k, a));
}
