# D. Find the Different Ones!

You are given an array `a` of length `n` and `q` queries.

Each query gives `l` and `r` (`1 <= l < r <= n`). For every query, output two indices `i` and `j` such that:
- `l <= i <= r`
- `l <= j <= r`
- `a[i] != a[j]`

If no such pair exists, output `-1 -1`.

## Input

- The first line contains `t` (`1 <= t <= 10^4`) — the number of test cases.
- For each test case:
- The first line contains `n` (`2 <= n <= 2 * 10^5`).
- The second line contains `n` integers `a_1, a_2, ..., a_n` (`1 <= a_i <= 10^6`).
- The third line contains `q` (`1 <= q <= 2 * 10^5`).
- Each of the next `q` lines contains `l r` (`1 <= l < r <= n`).

Across all test cases:
- The sum of all `n` does not exceed `2 * 10^5`.
- The sum of all `q` does not exceed `2 * 10^5`.

## Output

For each query print either:
- two valid indices `i j` in `[l, r]` with `a[i] != a[j]`, or
- `-1 -1` if every element in `a[l..r]` is equal.

Blank lines between test cases are allowed.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_different_ones(a: Vec<i64>, queries: Vec<(usize, usize)>) -> Vec<(i32, i32)> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i += 1;
        }

        let q: usize = it.next().unwrap().parse().unwrap();
        let mut queries: Vec<(usize, usize)> = Vec::with_capacity(q);
        let mut j: usize = 0;
        while j < q {
            let l: usize = it.next().unwrap().parse().unwrap();
            let r: usize = it.next().unwrap().parse().unwrap();
            queries.push((l, r));
            j += 1;
        }

        let ans = Solution::find_different_ones(a, queries);
        let mut k: usize = 0;
        while k < ans.len() {
            out.push_str(&format!("{} {}\n", ans[k].0, ans[k].1));
            k += 1;
        }
        if tc + 1 < t {
            out.push('\n');
        }
        tc += 1;
    }
    print!("{}", out);
}
```
