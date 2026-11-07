use std::io;

struct Solution;

impl Solution {
    pub fn count_positions(n: i32, a: i32, b: i32) -> i32 {
        let min_pos = if a + 1 >= n - b { a + 1 } else { n - b };
        n - min_pos + 1
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let parts: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let n = parts[0];
    let a = parts[1];
    let b = parts[2];
    println!("{}", Solution::count_positions(n, a, b));
}
