use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn construct_game(n: i64, s: i64) -> Option<(Vec<i64>, i64)> {
        if s < 2 * n {
            return None;
        }
        let nu = n as usize;
        let mut a: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < nu - 1 {
            a.push(1i64);
            i = i + 1;
        }
        a.push(s - (n - 1));
        Some((a, n))
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i64 = it.next().unwrap().parse().unwrap();
    let s: i64 = it.next().unwrap().parse().unwrap();
    let r = Solution::construct_game(n, s);
    if r.is_none() {
        println!("NO");
    } else {
        let (a, k) = r.unwrap();
        println!("YES");
        let mut i = 0usize;
        while i < a.len() {
            if i > 0 {
                print!(" ");
            }
            print!("{}", a[i]);
            i = i + 1;
        }
        println!();
        println!("{}", k);
    }
}
