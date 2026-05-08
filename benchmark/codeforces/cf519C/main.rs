use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_training_teams(n: i64, m: i64) -> i64 {
        let mut ans = if n < m { n } else { m };
        let by_total = (n + m) / 3;
        if by_total < ans {
            ans = by_total;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i64 = it.next().unwrap().parse().unwrap();
    let m: i64 = it.next().unwrap().parse().unwrap();
    let ans = Solution::max_training_teams(n, m);
    println!("{}", ans);
}
