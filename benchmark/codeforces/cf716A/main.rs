use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn remaining_words(n: usize, c: i64, t: Vec<i64>) -> usize {
        let mut cnt = 1usize;
        let mut i = 1usize;
        while i < n {
            if t[i] - t[i - 1] <= c {
                cnt = cnt + 1;
            } else {
                cnt = 1;
            }
            i = i + 1;
        }
        cnt
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let c: i64 = it.next().unwrap().parse().unwrap();
    let mut t: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        t.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::remaining_words(n, c, t);
    println!("{}", ans);
}
