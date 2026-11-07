use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_stones_to_remove(colors: Vec<u8>, n: usize) -> usize {
        let mut count = 0usize;
        let mut i = 0usize;
        while i + 1 < n {
            if colors[i] == colors[i + 1] {
                count += 1;
            }
            i += 1;
        }
        count
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let s = lines.next().unwrap().unwrap();
    let colors: Vec<u8> = s
        .trim()
        .bytes()
        .map(|b| match b {
            b'R' => 0u8,
            b'G' => 1u8,
            b'B' => 2u8,
            _ => 0u8,
        })
        .collect();
    let ans = Solution::min_stones_to_remove(colors, n);
    println!("{}", ans);
}
