use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn non_coprime_split(l: i32, r: i32) -> Option<(i32, i32)> {
        let mut s = l;
        while s <= r {
            if s >= 4 {
                if s % 2 == 0 {
                    return Some((2, s - 2));
                }
                let mut d: i32 = 3;
                while d <= s / d {
                    if s % d == 0 {
                        return Some((d, s - d));
                    }
                    d = d + 2;
                }
            }
            s = s + 1;
        }
        None
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut j: usize = 0;
    while j < t {
        let line = lines.next().unwrap().unwrap();
        let mut it = line.split_whitespace();
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        match Solution::non_coprime_split(l, r) {
            Some((a, b)) => {
                println!("{} {}", a, b);
            }
            None => {
                println!("-1");
            }
        }
        j = j + 1;
    }
}
