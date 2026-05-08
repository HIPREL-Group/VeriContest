# D. Black and White Stripe

You are given a stripe of length `n` consisting of cells colored black (`B`) or white (`W`).
You can recolor any white cell to black in one move.

Find the minimum number of moves needed so that there exists at least one contiguous segment of length `k` consisting only of black cells.

Input format:
- The first line contains an integer `t` — number of test cases.
- For each test case:
  - A line with integers `n` and `k`.
  - A line with a string `s` of length `n`, characters are only `B` and `W`.

Output format:
- For each test case, output one integer: the minimum number of recolors.

Core observation:
- For any fixed window of length `k`, the recolors needed equal the number of `W` cells in that window.
- Therefore, the answer is the minimum number of whites among all length-`k` windows.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_recolors(n: usize, k: usize, s: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let k: usize = it.next().unwrap().parse().unwrap();
        let stripe = it.next().unwrap().as_bytes();

        let mut s: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            if stripe[i] == b'W' {
                s.push(1);
            } else {
                s.push(0);
            }
            i += 1;
        }

        let ans = Solution::min_recolors(n, k, s);
        println!("{}", ans);
        case_id += 1;
    }
}
```
