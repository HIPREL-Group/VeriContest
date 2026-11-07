use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_k_segments_sum(nums: Vec<i64>, m: usize, k: usize) -> i128 {
        let n = nums.len();
        let window_count = n - m + 1;

        let mut window_sums: Vec<i128> = Vec::new();
        let mut start: usize = 0;
        while start < window_count {
            let mut current: i128 = 0;
            let mut i: usize = 0;
            while i < m {
                current = current + nums[start + i] as i128;
                i = i + 1;
            }
            window_sums.push(current);
            start = start + 1;
        }

        let mut i: usize = 0;
        let mut prev: Vec<i128> = Vec::new();
        while i <= n {
            prev.push(0);
            i = i + 1;
        }

        let mut taken: usize = 1;
        while taken <= k {
            let mut curr: Vec<i128> = Vec::new();
            i = 0;
            while i <= n {
                curr.push(-1);
                i = i + 1;
            }
            let mut idx: usize = n;
            while idx > 0 {
                let pos = idx - 1;
                let skip = curr[pos + 1];
                let take: i128;
                if m <= n - pos {
                    let tail = prev[pos + m];
                    if tail < 0 || pos >= window_count {
                        take = -1;
                    } else {
                        take = window_sums[pos] + tail;
                    }
                } else {
                    take = -1;
                }
                let best = if skip >= take { skip } else { take };
                curr[pos] = best;
                idx = pos;
            }
            prev = curr;
            taken = taken + 1;
        }

        let answer = prev[0];
        answer
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    let n: usize = tokens.next().expect("n").parse().expect("valid n");
    let m: usize = tokens.next().expect("m").parse().expect("valid m");
    let k: usize = tokens.next().expect("k").parse().expect("valid k");
    let mut nums: Vec<i64> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    while idx < n {
        nums.push(tokens.next().expect("array element").parse().expect("valid i64"));
        idx = idx + 1;
    }
    let result = Solution::max_k_segments_sum(nums, m, k);
    println!("{}", result);
}
