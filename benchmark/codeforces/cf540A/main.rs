use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_lock_moves(n: usize, current: Vec<u8>, target: Vec<u8>) -> u32 {
        let mut sum: u32 = 0;
        let mut i: usize = 0;
        while i < n {
            let ca = current[i] as u32;
            let cb = target[i] as u32;
            let d = if ca >= cb {
                ca - cb
            } else {
                cb - ca
            };
            let add = if d <= 5 {
                d
            } else {
                10 - d
            };
            sum = sum + add;
            i = i + 1;
        }
        sum
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut current = Vec::with_capacity(n);
    let s = lines.next().unwrap().unwrap();
    let sb = s.trim().as_bytes();
    for j in 0..n {
        current.push(sb[j] - b'0');
    }
    let mut target = Vec::with_capacity(n);
    let t = lines.next().unwrap().unwrap();
    let tb = t.trim().as_bytes();
    for j in 0..n {
        target.push(tb[j] - b'0');
    }
    let ans = Solution::min_lock_moves(n, current, target);
    println!("{}", ans);
}
