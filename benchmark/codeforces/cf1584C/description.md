# C. Two Arrays

You are given two integer arrays `a` and `b`, each of length `n`.

One transformation of `a` is defined as follows:

1. Choose any integer `k` such that `0 <= k <= n`.
2. Choose `k` distinct indices of `a`.
3. Add `1` to each chosen element.
4. Permute the elements of `a` arbitrarily.

Determine whether it is possible to perform this transformation exactly once so that the resulting array is equal to `b`.

## Input

- The first line contains `t` (`1 <= t <= 100`) — number of test cases.
- For each test case:
  - A line with `n` (`1 <= n <= 100`).
  - A line with `n` integers `a_i` (`-100 <= a_i <= 100`).
  - A line with `n` integers `b_i` (`-100 <= b_i <= 100`).

## Output

For each test case, print `YES` if transformation is possible, otherwise print `NO`.

## Notes

- Case of letters in output is ignored by Codeforces.
- Problem source: Codeforces 1584C, rating 900.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();

    let t: usize = tokens.next().expect("t").parse().expect("valid t");
    let mut case_id: usize = 0;
    while case_id < t {
        let n: usize = tokens.next().expect("n").parse().expect("valid n");

        let mut a: Vec<i32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(tokens.next().expect("a_i").parse().expect("valid a_i"));
            i = i + 1;
        }

        let mut b: Vec<i32> = Vec::with_capacity(n);
        i = 0;
        while i < n {
            b.push(tokens.next().expect("b_i").parse().expect("valid b_i"));
            i = i + 1;
        }

        if Solution::can_transform(a, b) {
            println!("YES");
        } else {
            println!("NO");
        }

        case_id = case_id + 1;
    }
}
```
