use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_beauty_and_pair_count(flowers: Vec<i64>) -> (i64, i64) {
        let mut min_val = flowers[0];
        let mut max_val = flowers[0];
        let mut min_count = 1i64;
        let mut max_count = 1i64;
        let mut i = 1usize;
        while i < flowers.len() {
            let x = flowers[i];
            if x < min_val {
                min_val = x;
                min_count = 1;
            } else if x == min_val {
                min_count += 1;
            }
            if x > max_val {
                max_val = x;
                max_count = 1;
            } else if x == max_val {
                max_count += 1;
            }
            i += 1;
        }
        let diff = max_val - min_val;
        let n = flowers.len() as i64;
        let pair_count = if min_val == max_val {
            n * (n - 1) / 2
        } else {
            min_count * max_count
        };
        (diff, pair_count)
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();
    let n = nums[0] as usize;
    let flowers = nums[1..1 + n].to_vec();
    let ans = Solution::max_beauty_and_pair_count(flowers);
    println!("{} {}", ans.0, ans.1);
}
