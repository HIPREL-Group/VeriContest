use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_equal_outer_sum(nums: Vec<i64>) -> i64 {
        let n = nums.len();
        let mut pref: Vec<i64> = Vec::new();
        pref.push(0);
        let mut i = 0usize;
        while i < n {
            let next = pref[i] + nums[i];
            pref.push(next);
            i = i + 1;
        }
        let total = pref[n];
        let mut left = 0usize;
        let mut right = n;
        let mut ans = 0i64;
        while left <= right {
            let lsum = pref[left];
            let rsum = total - pref[right];
            if lsum < rsum {
                left = left + 1;
            } else if lsum > rsum {
                right = right - 1;
            } else {
                if lsum > ans {
                    ans = lsum;
                }
                left = left + 1;
            }
        }
        ans
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < n {
        let v: i64 = it.next().unwrap().parse().unwrap();
        nums.push(v);
        idx = idx + 1;
    }
    let out = Solution::max_equal_outer_sum(nums);
    println!("{}", out);
}
