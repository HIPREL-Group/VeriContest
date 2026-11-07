use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_swaps_minimize_prefix_sum(p: Vec<i32>, n: usize, k: usize) -> i32 {
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        while i < k {
            if p[i] > k as i32 {
                cnt = cnt + 1;
            }
            i = i + 1;
        }
        cnt
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();
    let mut idx: usize = 0;
    let t = nums[idx] as usize;
    idx = idx + 1;
    let mut out = String::new();
    let mut c: usize = 0;
    while c < t {
        let n = nums[idx] as usize;
        idx = idx + 1;
        let k = nums[idx] as usize;
        idx = idx + 1;
        let mut p: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            p.push(nums[idx + j]);
            j = j + 1;
        }
        idx = idx + n;
        let ans = Solution::min_swaps_minimize_prefix_sum(p, n, k);
        out.push_str(&format!("{}\n", ans));
        c = c + 1;
    }
    print!("{}", out);
}
