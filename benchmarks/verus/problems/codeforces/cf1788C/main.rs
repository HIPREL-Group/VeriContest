use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn matching_numbers(n: i32) -> Option<Vec<(i32, i32)>> {
        if n % 2 == 0 {
            return None;
        }
        let k: i32 = (3 * n + 3) / 2;
        let mut out: Vec<(i32, i32)> = Vec::new();
        let mut i: i32 = 1;
        while i <= (n + 1) / 2 {
            let a1: i32 = 2 * i - 1;
            let b1: i32 = k - i;
            out.push((a1, b1));
            i = i + 1;
        }
        let mut j: i32 = 1;
        while j <= (n - 1) / 2 {
            let a2: i32 = 2 * j;
            let b2: i32 = k + (n + 1) / 2 - j - 1;
            out.push((a2, b2));
            j = j + 1;
        }
        Some(out)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut c: usize = 0;
    while c < t {
        let n: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::matching_numbers(n);
        match ans {
            None => {
                println!("No");
            }
            Some(v) => {
                println!("Yes");
                let mut idx: usize = 0;
                while idx < v.len() {
                    let p = v[idx];
                    println!("{} {}", p.0, p.1);
                    idx = idx + 1;
                }
            }
        }
        c = c + 1;
    }
}
