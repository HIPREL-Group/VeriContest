use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn total_steps(n: i64, targets: Vec<i64>) -> i64 {
        let mut total: i128 = 0;
        let mut cur: i64 = 1;
        let mut i: usize = 0;
        while i < targets.len() {
            let t = targets[i];
            if t >= cur {
                total = total + (t as i128 - cur as i128);
            } else {
                total = total + (n as i128 - cur as i128 + t as i128);
            }
            cur = t;
            i = i + 1;
        }
        total as i64
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();

    let n = nums[0];
    let m = nums[1] as usize;
    let targets = nums[2..2 + m].to_vec();

    let ans = Solution::total_steps(n, targets);
    println!("{}", ans);
}
