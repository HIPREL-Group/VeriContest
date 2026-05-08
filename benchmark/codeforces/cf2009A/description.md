# A. Minimize!

Time limit: 1 second | Memory limit: 256 megabytes

You are given two integers $a$ and $b$ ($a \le b$). Over all integer values of $c$ such that $a \le c \le b$, find the minimum value of $(c-a) + (b-c)$.

## Input

The first line contains an integer $t$ ($1 \le t \le 55$) — the number of test cases.

Each test case contains two integers $a$ and $b$ ($1 \le a \le b \le 10$).

## Output

For each test case, output the minimum possible value of $(c-a) + (b-c)$ on a new line.

## Examples

**Input:**
```
3
1 2
3 10
5 5
```

**Output:**
```
1
7
0
```

## Note

In the first test case, choosing $c=1$ gives $(1-1) + (2-1) = 1$, which is minimal.

In the second test case, choosing $c=6$ gives $(6-3) + (10-6) = 7$, which is minimal.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn minimize_value(a: i32, b: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let a: i32 = it.next().unwrap().parse().unwrap();
        let b: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::minimize_value(a, b);
        println!("{}", ans);
        k = k + 1;
    }
}
```
