# D. Robert Hood and Mrs Hood

Time limit: 2 seconds | Memory limit: 256 megabytes

Robin can choose a start day for each of two visits. Days are numbered from 1 to n.
Each visit lasts for d consecutive days, and all visit days must be within [1, n].

There are k jobs. Job i is active on all days from l_i to r_i inclusive.
A visit overlaps a job if at least one day of that visit intersects the job interval.

Robin wants:
- his brother's visit to overlap with the maximum number of distinct jobs,
- his mother's visit to overlap with the minimum number of distinct jobs.

If multiple start days are optimal, choose the earliest one.

## Input

The first line contains t (1 <= t <= 10^4) — the number of test cases.

For each test case:
- one line with n, d, k (1 <= n <= 10^5, 1 <= d, k <= n),
- then k lines, each with l_i and r_i (1 <= l_i <= r_i <= n).

It is guaranteed that the sum of n over all test cases does not exceed 2 * 10^5.

## Output

For each test case, print two integers:
- the best start day for the brother,
- the best start day for the mother.

Both start days must define visits fully contained in [1, n].

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

fn next_i32<'a, I: Iterator<Item = &'a str>>(it: &mut I) -> Option<i32> {
    it.next()?.parse().ok()
}

impl Solution {
    pub fn best_start_days(n: i32, d: i32, left: Vec<i32>, right: Vec<i32>) -> (i32, i32) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = match next_i32(&mut it) {
        Some(v) => v as usize,
        None => return,
    };

    let mut out = String::new();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let d: i32 = match next_i32(&mut it) {
            Some(v) => v,
            None => return,
        };
        let k: usize = match next_i32(&mut it) {
            Some(v) => v as usize,
            None => return,
        };

        let mut left: Vec<i32> = Vec::new();
        let mut right: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < k {
            let l: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            let r: i32 = match next_i32(&mut it) {
                Some(v) => v,
                None => return,
            };
            left.push(l);
            right.push(r);
            i = i + 1;
        }

        let ans = Solution::best_start_days(n, d, left, right);
        out.push_str(&format!("{} {}\n", ans.0, ans.1));

        case_id = case_id + 1;
    }

    print!("{}", out);
}
```
