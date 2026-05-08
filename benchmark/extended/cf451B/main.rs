use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn sort_the_array(nums: Vec<i64>) -> Option<(usize, usize)> {
        let n = nums.len();
        let mut left = 0usize;
        while left + 1 < n && nums[left] <= nums[left + 1] {
            left += 1;
        }
        if left + 1 == n {
            return Some((1, 1));
        }
        let mut right = n - 1;
        while right > 0 && nums[right - 1] <= nums[right] {
            right -= 1;
        }
        let mut i = 0usize;
        while i + 1 < n {
            let a = if left <= i && i <= right {
                nums[right - (i - left)]
            } else {
                nums[i]
            };
            let j = i + 1;
            let b = if left <= j && j <= right {
                nums[right - (j - left)]
            } else {
                nums[j]
            };
            if a > b {
                return None;
            }
            i += 1;
        }
        Some((left + 1, right + 1))
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let mut nums = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        nums.push(
            tokens
                .next()
                .expect("value")
                .parse::<i64>()
                .expect("valid i64"),
        );
        i += 1;
    }
    match Solution::sort_the_array(nums) {
        Some((l, r)) => {
            println!("yes");
            println!("{} {}", l, r);
        }
        None => {
            println!("no");
        }
    }
}
