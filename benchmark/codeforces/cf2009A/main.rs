use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn minimize_value(a: i32, b: i32) -> i32 {
        let result = b - a;
        result
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::minimize_value(a, b);
        println!("{}", ans);
        k = k + 1;
    }
}
