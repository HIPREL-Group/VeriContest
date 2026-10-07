use std::io::{self, BufRead};

struct Solution;

impl Solution {
    fn gcd_u64(a: u64, b: u64) -> u64 {
        if b == 0 {
            a
        } else {
            Self::gcd_u64(b, a % b)
        }
    }

    pub fn choose_alarm(x: Vec<i64>, p: Vec<i64>) -> (bool, i64, usize) {
        let n = x.len();
        let mut g: u64 = (x[1] - x[0]) as u64;
        let mut i: usize = 2;
        while i < n {
            let d: u64 = (x[i] - x[i - 1]) as u64;
            g = Self::gcd_u64(g, d);
            i = i + 1;
        }
        let mut jj: usize = 0;
        let m = p.len();
        while jj < m {
            let pv: u64 = p[jj] as u64;
            if g % pv == 0 {
                return (true, x[0], jj);
            }
            jj = jj + 1;
        }
        (false, 0i64, 0usize)
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let nm: Vec<i64> = lines
        .next()
        .unwrap()
        .unwrap()
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let n = nm[0] as usize;
    let m = nm[1] as usize;
    let x_line = lines.next().unwrap().unwrap();
    let mut x: Vec<i64> = Vec::new();
    let mut parts = x_line.split_whitespace();
    let mut a: usize = 0;
    while a < n {
        x.push(parts.next().unwrap().parse().unwrap());
        a = a + 1;
    }
    let p_line = lines.next().unwrap().unwrap();
    let mut p: Vec<i64> = Vec::new();
    parts = p_line.split_whitespace();
    a = 0;
    while a < m {
        p.push(parts.next().unwrap().parse().unwrap());
        a = a + 1;
    }
    let (ok, y, j) = Solution::choose_alarm(x, p);
    if ok {
        println!("YES");
        println!("{} {}", y, j + 1);
    } else {
        println!("NO");
    }
}
