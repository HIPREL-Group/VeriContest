use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn polycarp_coins(n: i64) -> (i64, i64) {
        let k_lo = n / 3;
        let d_lo = n - 3 * k_lo;
        let k_hi = (n + 2) / 3;
        let c2 = if k_hi != k_lo && 2 * k_hi <= n {
            let t = n - 3 * k_hi;
            let d_hi = if t < 0 {
                -t
            } else {
                t
            };
            if d_hi < d_lo {
                k_hi
            } else {
                k_lo
            }
        } else {
            k_lo
        };
        let c1 = n - 2 * c2;
        (c1, c2)
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let n: i64 = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let (c1, c2) = Solution::polycarp_coins(n);
        println!("{} {}", c1, c2);
        i = i + 1;
    }
}
