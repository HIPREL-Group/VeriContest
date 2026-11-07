use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn nearly_lucky(n: u64) -> bool {
        let mut count: u64 = 0;
        let mut x: u64 = n;
        while x > 0 {
            let d = x % 10;
            if d == 4 || d == 7 {
                count += 1;
            }
            x = x / 10;
        }
        count == 4 || count == 7
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let n: u64 = input.trim().parse().unwrap();
    if Solution::nearly_lucky(n) {
        println!("YES");
    } else {
        println!("NO");
    }
}
