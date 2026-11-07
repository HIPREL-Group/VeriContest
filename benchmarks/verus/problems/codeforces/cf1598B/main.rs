use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn groups(n: usize, days: Vec<Vec<bool>>) -> bool {
        let mut found = false;
        let mut d1: usize = 0;
        while d1 < 5 && !found {
            let mut d2: usize = d1 + 1;
            while d2 < 5 && !found {
                let mut either: usize = 0;
                let mut can_d1: usize = 0;
                let mut can_d2: usize = 0;
                let mut i: usize = 0;
                while i < n {
                    let c1 = days[i][d1];
                    let c2 = days[i][d2];
                    if c1 || c2 {
                        either += 1;
                    }
                    if c1 {
                        can_d1 += 1;
                    }
                    if c2 {
                        can_d2 += 1;
                    }
                    i += 1;
                }
                
                if either == n && can_d1 >= n / 2 && can_d2 >= n / 2 {
                    found = true;
                }
                d2 += 1;
            }
            d1 += 1;
        }
        found
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            for _ in 0..t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: usize = n_str.trim().parse().unwrap();
                    let mut days = Vec::new();
                    for _ in 0..n {
                        if let Some(Ok(line)) = lines.next() {
                            let parts: Vec<bool> = line.split_whitespace().map(|s| s == "1").collect();
                            days.push(parts);
                        }
                    }
                    if Solution::groups(n, days) {
                        println!("YES");
                    } else {
                        println!("NO");
                    }
                }
            }
        }
    }
}
