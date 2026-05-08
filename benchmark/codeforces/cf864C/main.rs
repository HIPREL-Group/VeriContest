use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_bus_refuels(a: i64, b: i64, f: i64, k: usize) -> i64 {
        let mut ans: i64 = 0;
        let mut have: i64 = b;
        let mut i: usize = 0;
        while i < k {
            let x: i64;
            let y: i64;
            if i % 2 == 0 {
                x = f;
                y = a - f;
            } else {
                x = a - f;
                y = f;
            }
            if have < x {
                return -1;
            }
            have = have - x;
            if i < k - 1 {
                if have < y {
                    ans = ans + 1;
                    have = b;
                } else if have < 2 * y {
                    ans = ans + 1;
                    have = b;
                }
            } else {
                if have < y {
                    ans = ans + 1;
                    have = b;
                }
            }
            if have < y {
                return -1;
            }
            have = have - y;
            i = i + 1;
        }
        ans
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let line = lines.next().unwrap().unwrap();
    let mut parts = line.split_whitespace();
    let a: i64 = parts.next().unwrap().parse().unwrap();
    let b: i64 = parts.next().unwrap().parse().unwrap();
    let f: i64 = parts.next().unwrap().parse().unwrap();
    let k: usize = parts.next().unwrap().parse().unwrap();
    let ans = Solution::min_bus_refuels(a, b, f, k);
    println!("{}", ans);
}
