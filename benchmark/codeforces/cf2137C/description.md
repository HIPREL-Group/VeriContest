# C. Maximum Even Sum

You are given two integers `a` and `b`.

Perform the following procedure:

1. Choose an integer `k` such that `k` divides `b`.
2. Replace `a` with `a * k` and replace `b` with `b / k`.

Find the greatest possible even value of `a + b` after this transformation.
If it is impossible to make `a + b` even, output `-1`.

## Input

The first line contains an integer `t` (`1 <= t <= 10^4`) — the number of test cases.

Each test case contains two integers `a` and `b` (`1 <= a, b <= a * b <= 10^18`).

## Output

For each test case, output one integer:

- the maximum even value of `a + b` after choosing a valid `k`, or
- `-1` if no valid choice yields an even sum.

## Example

Input:

```text
3
1 1
1 4
2 4
```

Output:

```text
2
4
6
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn maximum_even_sum(a: i128, b: i128) -> i128 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let a: i128 = it.next().unwrap().parse().unwrap();
        let b: i128 = it.next().unwrap().parse().unwrap();
        let ans = Solution::maximum_even_sum(a, b);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
