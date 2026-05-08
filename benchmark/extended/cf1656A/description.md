# Good Pairs

Time limit: 1 second | Memory limit: 256 megabytes

You are given an array $$$a_1, a_2, \ldots, a_n$$$ of positive integers. A *good pair* is a pair of indices $$$(i, j)$$$ with $$$1 \leq i, j \leq n$$$ such that, for all $$$1 \leq k \leq n$$$, the following equality holds:

$$$$$$ |a_i - a_k| + |a_k - a_j| = |a_i - a_j|, $$$$$$ where $$$|x|$$$ denotes the absolute value of $$$x$$$.

Find a good pair. Note that $$$i$$$ can be equal to $$$j$$$.

## Input

The input consists of multiple test cases. The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases. Description of the test cases follows.

The first line of each test case contains an integer $$$n$$$ ($$$1 \leq n \leq 10^5$$$) — the length of the array.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$1 \leq a_i \leq 10^9$$$) where $$$a_i$$$ is the $$$i$$$-th element of the array.

The sum of $$$n$$$ for all test cases is at most $$$2 \cdot 10^5$$$.

## Output

For each test case, print a single line with two space-separated indices $$$i$$$ and $$$j$$$ which form a good pair of the array. The case $$$i=j$$$ is allowed. It can be shown that such a pair always exists. If there are multiple good pairs, print any of them.

## Examples

**Input:**
```
3
3
5 2 7
5
1 4 2 2 3
1
12
```

**Output:**
```
2 3
1 2
1 1
```

## Note

In the first case, for $$$i = 2$$$ and $$$j = 3$$$ the equality holds true for all $$$k$$$:
- $$$k = 1$$$: $$$|a_2 - a_1| + |a_1 - a_3| = |2 - 5| + |5 - 7| = 5 = |2 - 7| = |a_2-a_3|$$$,
- $$$k = 2$$$: $$$|a_2 - a_2| + |a_2 - a_3| = |2 - 2| + |2 - 7| = 5 = |2 - 7| = |a_2-a_3|$$$,
- $$$k = 3$$$: $$$|a_2 - a_3| + |a_3 - a_3| = |2 - 7| + |7 - 7| = 5 = |2 - 7| = |a_2-a_3|$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn good_pair_indices(a: Vec<i64>) -> (i64, i64) {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut tc = 0usize;
    while tc < t {
        let _n_line = lines.next().unwrap().unwrap();
        let a_line = lines.next().unwrap().unwrap();
        let a: Vec<i64> = a_line
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();
        let (i, j) = Solution::good_pair_indices(a);
        println!("{} {}", i, j);
        tc = tc + 1;
    }
}
```
