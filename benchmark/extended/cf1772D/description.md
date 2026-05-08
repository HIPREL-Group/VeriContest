# D. Absolute Sorting

Time limit per test: 1 second
Memory limit per test: 256 megabytes

You are given an array `a` of length `n`.

You need to choose an integer `x` (`0 <= x <= 10^9`) and build an array
`b` where `b[i] = |a[i] - x|`.

Find any such `x` for which array `b` is nondecreasing:
`b[0] <= b[1] <= ... <= b[n-1]`.
If no such `x` exists, output `-1`.

If multiple answers exist, output any of them.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn absolute_sorting(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut case_idx: usize = 0;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }
        let ans = Solution::absolute_sorting(a);
        println!("{}", ans);
        case_idx += 1;
    }
}
```
