use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_equal_sum_splits(nums: Vec<i64>) -> u64 {
        let n = nums.len();
        if n < 3 {
            return 0;
        }

        let mut total: i128 = 0;
        let mut idx: usize = 0;
        while idx < n {
            total = total + nums[idx] as i128;
            idx = idx + 1;
        }

        let target = total / 3;
        if target * 3 != total {
            return 0;
        }

        let mut prefix: i128 = 0;
        let mut seen_targets: u64 = 0;
        let mut answer: u64 = 0;
        idx = 0;
        while idx < n - 1 {
            prefix = prefix + nums[idx] as i128;
            if prefix == target + target {
                answer = answer + seen_targets;
            }
            if prefix == target {
                seen_targets = seen_targets + 1;
            }
            idx = idx + 1;
        }
        answer
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let mut nums: Vec<i64> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    while idx < n {
        nums.push(tokens.next().expect("array element").parse().expect("valid i64"));
        idx = idx + 1;
    }
    let answer = Solution::count_equal_sum_splits(nums);
    println!("{}", answer);
}
