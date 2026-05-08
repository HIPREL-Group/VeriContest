use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn not_dividing_array(a: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut v = a;
        let mut i: usize = 0;
        while i < n {
            if v[i] == 1 {
                v[i] = 2;
            }
            i = i + 1;
        }
        let mut j: usize = 0;
        while j + 1 < n {
            let vj = v[j];
            let vj1 = v[j + 1];
            if vj1 % vj == 0 {
                let vj1_next: i32 = vj1 + 1;
                v[j + 1] = vj1_next;
            }
            j = j + 1;
        }
        v
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            let mut tc = 0usize;
            while tc < t {
                if let Some(Ok(n_str)) = lines.next() {
                    let n: usize = n_str.trim().parse().unwrap();
                    let mut a: Vec<i32> = Vec::new();
                    if let Some(Ok(line)) = lines.next() {
                        let parts: Vec<&str> = line.trim().split_whitespace().collect();
                        let mut p = 0usize;
                        while p < n {
                            let x: i32 = parts[p].parse().unwrap();
                            a.push(x);
                            p = p + 1;
                        }
                    }
                    let res = Solution::not_dividing_array(a);
                    let mut k = 0usize;
                    while k < res.len() {
                        if k > 0 {
                            print!(" ");
                        }
                        print!("{}", res[k]);
                        k = k + 1;
                    }
                    println!();
                }
                tc = tc + 1;
            }
        }
    }
}
