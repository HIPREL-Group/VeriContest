use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_magnet_groups(magnets: Vec<u8>) -> u32 {
        let n = magnets.len();
        let mut groups = 1u32;
        let mut i = 1usize;
        while i < n {
            if magnets[i] != magnets[i - 1] {
                groups += 1;
            }
            i += 1;
        }
        groups
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut magnets = Vec::with_capacity(n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let s = line.trim();
        let val = if s == "01" { 0u8 } else { 1u8 };
        magnets.push(val);
    }
    let ans = Solution::count_magnet_groups(magnets);
    println!("{}", ans);
}
