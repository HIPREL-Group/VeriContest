use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_prefix_removals(n: usize, a: Vec<i32>) -> usize {
        let mut seen: Vec<bool> = Vec::new();
        let mut j: usize = 0;
        while j <= n {
            seen.push(false);
            j = j + 1;
        }
        let mut i: usize = n;
        while i > 0 {
            let x: usize = a[i - 1] as usize;
            if seen[x] {
                return i;
            }
            seen[x] = true;
            i = i - 1;
        }
        i
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
    let mut c: usize = 0;
    while c < t {
        let n = nums[idx] as usize;
        idx = idx + 1;
        let mut a: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            a.push(nums[idx + j]);
            j = j + 1;
        }
        idx = idx + n;
        let ans = Solution::min_prefix_removals(n, a);
        println!("{}", ans);
        c = c + 1;
    }
}
