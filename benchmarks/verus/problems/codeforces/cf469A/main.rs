use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn can_be_the_guy(n: i32, x_levels: Vec<i32>, y_levels: Vec<i32>) -> bool {
        let mut k = 1i32;
        while k <= n {
            let x_len = x_levels.len();
            let y_len = y_levels.len();
            let mut found = false;
            let mut i = 0usize;
            while i < x_len && !found {
                if x_levels[i] == k {
                    found = true;
                } else {
                    i += 1;
                }
            }
            if !found {
                i = 0;
                while i < y_len && !found {
                    if y_levels[i] == k {
                        found = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if !found {
                return false;
            }
            k += 1;
        }
        true
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: i32 = lines.next().unwrap().unwrap().trim().parse().expect("n");
    let line2: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
    let p = line2[0] as usize;
    let x_levels: Vec<i32> = line2[1..1 + p].to_vec();
    let line3: Vec<i32> = lines.next().unwrap().unwrap().split_whitespace().map(|s| s.parse().unwrap()).collect();
    let q = line3[0] as usize;
    let y_levels: Vec<i32> = line3[1..1 + q].to_vec();
    let ans = Solution::can_be_the_guy(n, x_levels, y_levels);
    if ans {
        println!("I become the guy.");
    } else {
        println!("Oh, my keyboard!");
    }
}
