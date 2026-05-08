# A+B Again?

Time limit: 1 second | Memory limit: 256 megabytes

Given a two-digit positive integer $$$n$$$, find the sum of its digits.

## Input

The first line contains an integer $$$t$$$ ($$$1 \leq t \leq 90$$$) — the number of test cases.

The only line of each test case contains a single two-digit positive integer $$$n$$$ ($$$10 \leq n \leq 99$$$).

## Output

For each test case, output a single integer — the sum of the digits of $$$n$$$.

## Examples

**Input:**
```
8
77
21
40
34
19
84
10
99
```

**Output:**
```
14
3
4
7
10
12
1
18
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn two_digit_digit_sum(n: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::two_digit_digit_sum(n);
        println!("{}", ans);
        k = k + 1;
    }
}
```
