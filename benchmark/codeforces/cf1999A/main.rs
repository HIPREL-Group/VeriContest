use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn two_digit_digit_sum(n: i32) -> i32 {
        let tens = n / 10;
        let ones = n % 10;
        tens + ones
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::two_digit_digit_sum(n);
        println!("{}", ans);
        k = k + 1;
    }
}
