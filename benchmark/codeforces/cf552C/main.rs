use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_balance(w: i64, m: i64) -> bool {
        if w == 2 {
            return true;
        }
        let mut current = m;
        let mut digits_left: i64 = 31;
        while current > 0 && digits_left > 0 {
            let rem = current % w;
            if rem == 0 {
                current = current / w;
                digits_left = digits_left - 1;
            } else if rem == 1 {
                current = (current - 1) / w;
                digits_left = digits_left - 1;
            } else if rem + 1 == w {
                current = (current + 1) / w;
                digits_left = digits_left - 1;
            } else {
                return false;
            }
        }
        current == 0
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut parts = input.split_whitespace();
    let w: i64 = parts.next().unwrap().parse().unwrap();
    let m: i64 = parts.next().unwrap().parse().unwrap();
    let answer = if Solution::can_balance(w, m) { "YES" } else { "NO" };
    println!("{}", answer);
}
