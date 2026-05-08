# C. Make Equal Again

You are given an integer array `a` of length `n`.

You may perform at most one operation:
- choose integers `l`, `r`, `x` with `1 <= l <= r <= n`,
- set every element `a[i]` for `l <= i <= r` to `x`.

The cost of this operation is `r - l + 1` burles.

Find the minimum cost needed to make all array elements equal.

## Input

- The first line contains an integer `t` — the number of test cases.
- For each test case:
- the first line contains `n`.
- the second line contains `n` integers `a_1, a_2, ..., a_n`.

Typical constraints for this problem:
- `1 <= t <= 10^4`
- `1 <= n <= 2 * 10^5`
- `1 <= a_i <= n`
- the sum of `n` over all test cases does not exceed `2 * 10^5`.

## Output

For each test case, print one integer: the minimum number of burles.

## Key idea

If all elements must be equal after at most one segment assignment, the unchanged prefix and suffix (if any) must already be equal to the final value.
So we keep as many equal elements at the left and/or right border as possible and pay for the middle segment.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_cost_make_equal(a: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
        }
        let ans = Solution::min_cost_make_equal(a);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
