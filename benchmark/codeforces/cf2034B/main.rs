use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_timar_operations(s: Vec<i32>, m: usize, k: usize) -> i64 {
        let n = s.len();
        let mut ans: i64 = 0;
        let mut i: usize = 0;
        let mut cnt: usize = 0;
        let mut skip: usize = 0;
        while i < n {
            if skip > 0 {
                skip = skip - 1;
                cnt = 0;
            } else if s[i] == 0 {
                if cnt + 1 == m {
                    ans = ans + 1;
                    cnt = 0;
                    skip = k - 1;
                } else {
                    cnt = cnt + 1;
                }
            } else {
                cnt = 0;
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
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let m: usize = it.next().unwrap().parse().unwrap();
        let k: usize = it.next().unwrap().parse().unwrap();
        let line: &str = it.next().unwrap();
        let mut s: Vec<i32> = Vec::new();
        let mut p: usize = 0;
        while p < n {
            let ch = line.as_bytes()[p];
            if ch == 48 {
                s.push(0);
            } else {
                s.push(1);
            }
            p = p + 1;
        }
        let ans = Solution::min_timar_operations(s, m, k);
        println!("{}", ans);
        tc = tc + 1;
    }
}
