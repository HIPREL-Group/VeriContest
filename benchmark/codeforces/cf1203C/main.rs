use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_common_divisors(n: usize, a: Vec<i64>) -> i64 {
        let mut g: i64 = a[0];
        let mut i: usize = 1;
        while i < n {
            let mut x: i64 = g;
            let mut y: i64 = a[i];
            while y != 0 {
                let t: i64 = y;
                y = x % y;
                x = t;
            }
            g = x;
            i = i + 1;
        }
        let mut count: i64 = 0;
        let mut d: i64 = 1;
        while d <= g / d {
            if g % d == 0 {
                count = count + 1;
                if d != g / d {
                    count = count + 1;
                }
            }
            d = d + 1;
        }
        count
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let a_line = lines.next().unwrap().unwrap();
    let mut a: Vec<i64> = Vec::new();
    let mut parts = a_line.split_whitespace();
    let mut i: usize = 0;
    while i < n {
        let v: i64 = parts.next().unwrap().parse().unwrap();
        a.push(v);
        i = i + 1;
    }
    println!("{}", Solution::count_common_divisors(n, a));
}
