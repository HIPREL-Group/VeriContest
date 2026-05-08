# D. Gold Rush

Initially, there is one pile with `n` gold coins.

In one move, you can choose a pile with size divisible by `3` and split it into two piles:
- one pile of size `x / 3`
- one pile of size `2 * x / 3`

Given `n` and `m`, determine whether it is possible to obtain a pile with exactly `m` coins after performing zero or more moves.

## Input

The first line contains one integer `t` (`1 <= t <= 10^4`) - the number of test cases.

Each test case contains two integers `n` and `m` (`1 <= n, m <= 10^9`).

## Output

For each test case, print `YES` if it is possible to obtain a pile with exactly `m` coins, and `NO` otherwise.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_obtain(n: i64, m: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        if Solution::can_obtain(n, m) {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }

    print!("{}", out);
}
```
