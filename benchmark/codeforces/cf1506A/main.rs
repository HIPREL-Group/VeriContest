use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn strange_table_number(n: u64, m: u64, x: u64) -> u64 {
        let row = (x - 1) % n + 1;
        let col = (x - 1) / n + 1;
        let ans = ((row - 1) as u128) * (m as u128) + (col as u128);
        ans as u64
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: u64 = it.next().unwrap().parse().unwrap();
        let m: u64 = it.next().unwrap().parse().unwrap();
        let x: u64 = it.next().unwrap().parse().unwrap();
        let ans = Solution::strange_table_number(n, m, x);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
