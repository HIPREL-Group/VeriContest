# Xenia and Ringroad

Time limit: 2 seconds | Memory limit: 256 megabytes

Xenia lives in a city that has $n$ houses built along the main ringroad. The ringroad is built in a circle, so the houses are numbered from 1 to $n$ in clockwise order. The ringroad is one-way and traffic runs in the clockwise direction.

Xenia has recently moved into the house number 1. She has a list of $m$ tasks to do. The $i$-th task is to visit house $a_i$. Xenia completes the tasks in order: first she goes to house $a_1$, then to $a_2$, and so on. Moving along the ringroad from house $x$ to house $y$ takes one unit of time if Xenia moves clockwise from $x$ to $y$ (so she never goes counter-clockwise).

Find the total time Xenia needs to complete all her tasks.

## Input

The first line contains two integers $n$ and $m$ ($2 \le n \le 10^5$, $1 \le m \le 10^5$). The second line contains $m$ integers $a_1, a_2, \ldots, a_m$ ($1 \le a_i \le n$).

## Output

Print a single integer — the time Xenia needs to complete all tasks.

## Examples

**Input:**
```
4 3
3 2 3
```

**Output:**
```
6
```

**Input:**
```
4 3
2 3 3
```

**Output:**
```
2
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn total_steps(n: i64, targets: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let nums: Vec<i64> = input
        .split_whitespace()
        .map(|s| s.parse::<i64>().expect("integer"))
        .collect();

    let n = nums[0];
    let m = nums[1] as usize;
    let targets = nums[2..2 + m].to_vec();

    let ans = Solution::total_steps(n, targets);
    println!("{}", ans);
}
```
