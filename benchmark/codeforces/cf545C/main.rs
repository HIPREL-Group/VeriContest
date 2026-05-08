use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_felled_trees(x: Vec<i64>, h: Vec<i64>) -> i64 {
        let n = x.len();
        if n == 1 {
            return 1i64;
        }
        let mut ans: i64 = 2;
        let mut last: i64 = x[0];
        let mut i: usize = 1;
        while i < n - 1 {
            let xi = x[i];
            let hi = h[i];
            if xi > last + hi {
                ans = ans + 1;
                last = xi;
            } else if xi + hi < x[i + 1] {
                ans = ans + 1;
                last = xi + hi;
            } else {
                last = xi;
            }
            i = i + 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut x: Vec<i64> = Vec::with_capacity(n);
    let mut h: Vec<i64> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n {
        let xi: i64 = it.next().unwrap().parse().unwrap();
        let hi: i64 = it.next().unwrap().parse().unwrap();
        x.push(xi);
        h.push(hi);
        j = j + 1;
    }
    let answer = Solution::max_felled_trees(x, h);
    println!("{}", answer);
}
