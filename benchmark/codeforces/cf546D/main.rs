use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_scores_for_games(queries: Vec<(i32, i32)>) -> Vec<u64> {
        let mut spf: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i <= 5_000_000usize {
            spf.push(0usize);
            i = i + 1;
        }

        i = 2usize;
        while i <= 5_000_000usize {
            let mut j = i;
            while j <= 5_000_000usize {
                if spf[j] == 0usize {
                    spf[j] = i;
                }
                j = j + i;
            }
            i = i + 1;
        }

        i = 2usize;
        while i <= 5_000_000usize {
            let d = spf[i];
            let q = i / d;
            if q <= 1 {
                spf[i] = 1usize;
            } else {
                let omega_val = spf[q] + 1;
                spf[i] = omega_val;
            }
            i = i + 1;
        }

        let mut prefix: Vec<u64> = Vec::new();
        prefix.push(0u64);
        prefix.push(0u64);

        i = 2usize;
        while i <= 5_000_000usize {
            let value = spf[i] as u64;
            let total = prefix[i - 1] + value;
            prefix.push(total);
            i = i + 1;
        }

        let mut res = Vec::new();
        i = 0usize;
        while i < queries.len() {
            let (a, b) = queries[i];
            let answer = prefix[a as usize] - prefix[b as usize];
            res.push(answer);
            i = i + 1;
        }
        res
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i32> = input
        .split_whitespace()
        .map(|s| s.parse::<i32>().expect("integer"))
        .collect();

    let t = nums[0] as usize;
    let mut queries: Vec<(i32, i32)> = Vec::new();
    let mut i = 1usize;
    while i < 1 + 2 * t {
        queries.push((nums[i], nums[i + 1]));
        i += 2;
    }

    let ans = Solution::max_scores_for_games(queries);
    let mut out = String::new();
    let mut i = 0usize;
    while i < ans.len() {
        out.push_str(&format!("{}\n", ans[i]));
        i += 1;
    }
    print!("{}", out);
}
