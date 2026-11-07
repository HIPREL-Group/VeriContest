use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn max_loving_petals(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut total = 0i32;
        let mut min_odd = 101i32;
        let mut i = 0usize;
        while i < n {
            total = total + a[i];
            if a[i] % 2 == 1 {
                if a[i] < min_odd {
                    min_odd = a[i];
                }
            }
            i = i + 1;
        }
        let r = if total % 2 == 1 {
            total
        } else {
            if min_odd == 101 {
                0
            } else {
                total - min_odd
            }
        };
        r
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let mut parts = line.split_whitespace();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut j = 0usize;
    while j < n {
        let x: i32 = parts.next().unwrap().parse().unwrap();
        a.push(x);
        j = j + 1;
    }
    let ans = Solution::max_loving_petals(a);
    println!("{}", ans);
}
