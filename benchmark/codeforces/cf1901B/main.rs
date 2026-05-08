use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_chip_teleports(c: Vec<i64>) -> i64 {
        let n = c.len();
        let mut ans: i64 = c[0] - 1;
        let mut j: usize = 0;
        let bound = n - 1;
        while j < bound {
            let ci = c[j];
            let cip1 = c[j + 1];
            let add: i64 = if cip1 > ci {
                cip1 - ci
            } else {
                0
            };
            ans = ans + add;
            j = j + 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut c: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let x: i64 = it.next().unwrap().parse().unwrap();
            c.push(x);
            i = i + 1;
        }
        let ans = Solution::min_chip_teleports(c);
        println!("{}", ans);
        k = k + 1;
    }
}
