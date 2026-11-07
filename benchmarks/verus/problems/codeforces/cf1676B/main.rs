use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn min_operations_to_equal(candies: Vec<i64>) -> i64 {
        let n = candies.len();
        let mut min_val = candies[0];
        let mut i: usize = 1;
        while i < n {
            if candies[i] < min_val {
                min_val = candies[i];
            }
            i += 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < n {
            ans += candies[i] - min_val;
            i += 1;
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut candies: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let x: i64 = it.next().unwrap().parse().unwrap();
            candies.push(x);
        }
        let ans = Solution::min_operations_to_equal(candies);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
