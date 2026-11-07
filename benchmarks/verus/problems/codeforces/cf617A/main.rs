use std::io;

struct Solution;

impl Solution {
    pub fn min_steps(x: u64) -> u64 {
        (x + 4) / 5
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let x: u64 = line.trim().parse().expect("integer");
    println!("{}", Solution::min_steps(x));
}
