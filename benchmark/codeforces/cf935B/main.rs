use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn fafa_and_gates(n: usize, s: Vec<i32>) -> i32 {
        let mut x = 0;
        let mut y = 0;
        let mut coins = 0;
        let mut i = 0;

        while i < n {
            let nxt = s[i];
            if i > 0 && x == y && s[i - 1] == nxt {
                coins += 1;
            }
            if nxt == 1 {
                x += 1;
            } else {
                y += 1;
            }
            i += 1;
        }

        coins
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(line1)) = lines.next() {
        if let Ok(n) = line1.trim().parse::<usize>() {
            if let Some(Ok(line2)) = lines.next() {
                let moves: Vec<i32> = line2
                    .trim()
                    .chars()
                    .map(|c| if c == 'R' { 1 } else { 0 })
                    .collect();
                let ans = Solution::fafa_and_gates(n, moves);
                println!("{}", ans);
            }
        }
    }
}
