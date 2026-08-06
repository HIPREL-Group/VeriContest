# A. Minimize!

Time limit: 1 second | Memory limit: 256 megabytes

You are given two integers $$$a$$$ and $$$b$$$ ($$$a \leq b$$$). Over all possible integer values of $$$c$$$ ($$$a \leq c \leq b$$$), find the minimum value of $$$(c - a) + (b - c)$$$.

## Input

The first line contains $$$t$$$ ($$$1 \leq t \leq 55$$$) — the number of test cases. 

Each test case contains two integers $$$a$$$ and $$$b$$$ ($$$1 \leq a \leq b \leq 10$$$).

## Output

For each test case, output the minimum possible value of $$$(c - a) + (b - c)$$$ on a new line.

## Example

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

In the first test case, you can choose $$$c = 1$$$ and obtain an answer of $$$(1 - 1) + (2 - 1) = 1$$$. It can be shown this is the minimum value possible.

In the second test case, you can choose $$$c = 6$$$ and obtain an answer of $$$(6 - 3) + (10 - 6) = 7$$$. It can be shown this is the minimum value possible.

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
