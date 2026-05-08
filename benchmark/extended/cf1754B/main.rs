use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn optimal_permutation(n: i32) -> Vec<i32> {
        let mut p: Vec<i32> = Vec::new();
        let h = n / 2;
        let mut i = 1;
        while i <= h {
            p.push(h + i);
            p.push(i);
            i = i + 1;
        }
        if n % 2 == 1 {
            p.push(n);
        }
        p
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<i32>() {
            let mut k = 0;
            while k < t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: i32 = n_str.trim().parse().unwrap();
                    let p = Solution::optimal_permutation(n);
                    let mut j = 0;
                    while j < p.len() {
                        if j > 0 {
                            print!(" ");
                        }
                        print!("{}", p[j]);
                        j = j + 1;
                    }
                    println!();
                }
                k = k + 1;
            }
        }
    }
}
