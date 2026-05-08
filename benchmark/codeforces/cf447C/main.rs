use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn longest_subsegment_one_change_strict_inc(nums: Vec<i64>) -> i64 {
        let n: usize = nums.len();
        if n == 1 {
            return 1;
        }
        let mut pre: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            pre.push(1i32);
            j = j + 1;
        }
        j = 1;
        while j < n {
            if nums[j] > nums[j - 1] {
                pre[j] = pre[j - 1] + 1;
            }
            j = j + 1;
        }
        let mut suf: Vec<i32> = Vec::new();
        j = 0;
        while j < n {
            suf.push(1i32);
            j = j + 1;
        }
        j = n - 1;
        while j > 0 {
            j = j - 1;
            if nums[j] < nums[j + 1] {
                suf[j] = suf[j + 1] + 1;
            }
        }
        let mut ans: i32 = 1;
        j = 0;
        while j < n {
            if pre[j] > ans {
                ans = pre[j];
            }
            j = j + 1;
        }
        j = 0;
        while j < n {
            let left: i32 = if j == 0 {
                0
            } else {
                pre[j - 1]
            };
            let right: i32 = if j + 1 >= n {
                0
            } else {
                suf[j + 1]
            };
            let alo: i64 = if j == 0 {
                -2_000_000_000
            } else {
                nums[j - 1]
            };
            let ahi: i64 = if j + 1 >= n {
                2_000_000_000
            } else {
                nums[j + 1]
            };
            let cand: i32 = if alo + 1 < ahi {
                left + 1 + right
            } else {
                let m: i32 = if left > right {
                    left
                } else {
                    right
                };
                m + 1
            };
            if cand > ans {
                ans = cand;
            }
            j = j + 1;
        }
        ans as i64
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read");
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        nums.push(it.next().unwrap().parse::<i64>().unwrap());
        i = i + 1;
    }
    println!("{}", Solution::longest_subsegment_one_change_strict_inc(nums));
}
