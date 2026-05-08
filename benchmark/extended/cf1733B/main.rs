use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn rule_of_league(n: i64, x: i64, y: i64) -> Option<Vec<i64>> {
        let lo = if x < y { x } else { y };
        let hi = if x > y { x } else { y };
        if lo != 0 {
            return None;
        }
        if hi == 0 {
            return None;
        }
        if (n - 1) % hi != 0 {
            return None;
        }
        let m = (n - 1) as usize;
        let mut w: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m {
            let ii = i as i64;
            let block = ii / hi;
            let win = 2 + block * hi;
            w.push(win);
            i = i + 1;
        }
        let out = Some(w);
        out
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let x: i64 = it.next().unwrap().parse().unwrap();
        let y: i64 = it.next().unwrap().parse().unwrap();
        let r = Solution::rule_of_league(n, x, y);
        if r.is_none() {
            println!("-1");
        } else {
            let w = r.unwrap();
            let mut j: usize = 0;
            while j < w.len() {
                if j > 0 {
                    print!(" ");
                }
                print!("{}", w[j]);
                j = j + 1;
            }
            println!();
        }
        tc = tc + 1;
    }
}
