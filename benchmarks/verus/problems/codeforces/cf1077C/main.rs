use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn nice_indices(n: usize, a: Vec<i32>) -> Vec<i32> {
        let mut freq: Vec<i32> = Vec::new();
        let mut fi: usize = 0;
        while fi < 1_000_000 + 1 {
            freq.push(0i32);
            fi += 1;
        }
        let mut s: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let v = a[i] as usize;
            freq[v] = freq[v] + 1;
            s = s + a[i] as i64;
            i += 1;
        }
        let mut res: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let aj = a[j] as i64;
            let t = s - aj;
            if t % 2 == 0 {
                let need = t / 2;
                if need >= 1 && need <= 1_000_000 as i64 {
                    let need_u = need as usize;
                    let c = freq[need_u];
                    if aj == need {
                        if c >= 2 {
                            res.push((j + 1) as i32);
                        }
                    } else {
                        if c >= 1 {
                            res.push((j + 1) as i32);
                        }
                    }
                }
            }
            j += 1;
        }
        res
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(n_str)) = lines.next() {
        let n: usize = n_str.trim().parse().unwrap();
        let a: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let res = Solution::nice_indices(n, a);
        println!("{}", res.len());
        if !res.is_empty() {
            let mut k: usize = 0;
            while k < res.len() {
                if k > 0 {
                    print!(" ");
                }
                print!("{}", res[k]);
                k += 1;
            }
            println!();
        }
    }
}
