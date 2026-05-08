use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn animal_type(sticks: Vec<i32>) -> i32 {
        let mut cnt = Vec::new();
        let mut zi = 0usize;
        while zi < 10 {
            cnt.push(0i32);
            zi += 1;
        }
        let mut i = 0usize;
        while i < 6 {
            let idx = sticks[i] as usize;
            cnt[idx] = cnt[idx] + 1;
            i += 1;
        }
        let mut leg = 0i32;
        let mut v = 1i32;
        while v <= 9 {
            if cnt[v as usize] >= 4 {
                leg = v;
            }
            v += 1;
        }
        if leg == 0 {
            return 0;
        }
        let c = cnt[leg as usize];
        if c == 6 {
            return 2;
        }
        if c == 5 {
            return 1;
        }
        let mut ii = 0usize;
        let mut x = 0i32;
        let mut y = 0i32;
        let mut nrem = 0usize;
        while ii < 6 {
            if sticks[ii] != leg {
                if nrem == 0 {
                    x = sticks[ii];
                } else {
                    y = sticks[ii];
                }
                nrem += 1;
            }
            ii += 1;
        }
        if x == y {
            2
        } else {
            1
        }
    }
}

fn main() {
    let stdin = io::stdin();
    let line = stdin.lock().lines().next().unwrap().unwrap();
    let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let sticks = vec![parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]];
    let r = Solution::animal_type(sticks);
    if r == 1 {
        println!("Bear");
    } else if r == 2 {
        println!("Elephant");
    } else {
        println!("Alien");
    }
}
