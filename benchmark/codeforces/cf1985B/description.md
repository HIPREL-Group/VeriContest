# Maximum Multiple Sum

Time limit: 1 second | Memory limit: 256 megabytes

Given an integer $$$n$$$, find an integer $$$x$$$ such that:

- $$$2 \leq x \leq n$$$.
- The sum of multiples of $$$x$$$ that are less than or equal to $$$n$$$ is maximized. Formally, $$$x + 2x + 3x + \dots + kx$$$ where $$$kx \leq n$$$ is maximized over all possible values of $$$x$$$.

## Input

The first line contains $$$t$$$ ($$$1 \leq t \leq 100$$$) — the number of test cases.

Each test case contains a single integer $$$n$$$ ($$$2 \leq n \leq 100$$$).

## Output

For each test case, output an integer, the optimal value of $$$x$$$. It can be shown there is only one unique answer.

## Examples

**Input:**

```
2
3
15
```

**Output:**

```
3
2
```

## Note

For $$$n = 3$$$, the possible values of $$$x$$$ are $$$2$$$ and $$$3$$$. The sum of all multiples of $$$2$$$ less than or equal to $$$n$$$ is just $$$2$$$, and the sum of all multiples of $$$3$$$ less than or equal to $$$n$$$ is $$$3$$$. Therefore, $$$3$$$ is the optimal value of $$$x$$$.

For $$$n = 15$$$, the optimal value of $$$x$$$ is $$$2$$$. The sum of all multiples of $$$2$$$ less than or equal to $$$n$$$ is $$$2 + 4 + 6 + 8 + 10 + 12 + 14 = 56$$$, which can be proven to be the maximal over all other possible values of $$$x$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_multiples_sum_x(n: i32) -> i32 {
        
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
        let ans = Solution::max_multiples_sum_x(n);
        println!("{}", ans);
        k = k + 1;
    }
}
```
