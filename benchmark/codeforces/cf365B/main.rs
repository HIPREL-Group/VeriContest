use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn longest_fibonacci_segment(nums: Vec<i64>) -> usize {
        let n = nums.len();
        if n <= 2 {
            return n;
        }

        let mut best = 2usize;
        let mut cur = 2usize;
        let mut i = 2usize;
        while i < n {
            if nums[i] == nums[i - 1] + nums[i - 2] {
                cur = cur + 1;
            } else {
                cur = 2;
            }
            if cur > best {
                best = cur;
            }
            i = i + 1;
        }
        best
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        nums.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::longest_fibonacci_segment(nums);
    println!("{}", ans);
}
