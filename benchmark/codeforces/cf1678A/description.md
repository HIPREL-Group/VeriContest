# Tokitsukaze and All Zero Sequence

Time limit: 1 second | Memory limit: 256 megabytes

Tokitsukaze has a sequence $$$a$$$ of length $$$n$$$. For each operation, she selects two numbers $$$a_i$$$ and $$$a_j$$$ ($$$i \ne j$$$; $$$1 \leq i,j \leq n$$$).

- If $$$a_i = a_j$$$, change one of them to $$$0$$$.
- Otherwise change both of them to $$$\min(a_i, a_j)$$$.

Tokitsukaze wants to know the minimum number of operations to change all numbers in the sequence to $$$0$$$. It can be proved that the answer always exists.

## Input

The first line contains a single positive integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases.

For each test case, the first line contains a single integer $$$n$$$ ($$$2 \leq n \leq 100$$$) — the length of the sequence $$$a$$$.

The second line contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$0 \leq a_i \leq 100$$$) — the sequence $$$a$$$.

## Output

For each test case, print a single integer — the minimum number of operations to change all numbers in the sequence to $$$0$$$.

## Examples

**Input:**
```
3
3
1 2 3
3
1 2 2
3
1 2 0
```

**Output:**
```
4
3
2
```

## Note

In the first test case, one of the possible ways to change all numbers in the sequence to $$$0$$$:

In the $$$1$$$-st operation, $$$a_1  \lt  a_2$$$, after the operation, $$$a_2 = a_1 = 1$$$. Now the sequence $$$a$$$ is $$$[1,1,3]$$$.

In the $$$2$$$-nd operation, $$$a_1 = a_2 = 1$$$, after the operation, $$$a_1 = 0$$$. Now the sequence $$$a$$$ is $$$[0,1,3]$$$.

In the $$$3$$$-rd operation, $$$a_1  \lt  a_2$$$, after the operation, $$$a_2 = 0$$$. Now the sequence $$$a$$$ is $$$[0,0,3]$$$.

In the $$$4$$$-th operation, $$$a_2  \lt  a_3$$$, after the operation, $$$a_3 = 0$$$. Now the sequence $$$a$$$ is $$$[0,0,0]$$$.

So the minimum number of operations is $$$4$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_ops_to_all_zero(a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let n_line = lines.next().unwrap().unwrap();
        let n: usize = n_line.trim().parse().unwrap();
        let a_line = lines.next().unwrap().unwrap();
        let mut parts = a_line.split_whitespace();
        let mut a: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            let x: i32 = parts.next().unwrap().parse().unwrap();
            a.push(x);
            j = j + 1;
        }
        let ans = Solution::min_ops_to_all_zero(a);
        println!("{}", ans);
        k = k + 1;
    }
}
```
