# Xenia and Ringroad

Time limit: 2 seconds | Memory limit: 256 megabytes

Xenia lives in a city that has $n$ houses built along the main ringroad. The ringroad houses are numbered 1 through $n$ in the clockwise order. The ringroad traffic is one way and also is clockwise.

Xenia has recently moved into the ringroad house number 1. As a result, she's got $m$ things to do. In order to complete the $i$-th task, she needs to be in the house number $a_i$ and complete all tasks with numbers less than $i$. Initially, Xenia is in the house number 1, find the minimum time she needs to complete all her tasks if moving from a house to a neighboring one along the ringroad takes one unit of time.

## Input

The first line contains two integers $n$ and $m$ $(2 ≤ n ≤ 10^5, 1 ≤ m ≤ 10^5)$. The second line contains $m$ integers $a_1, a_2, ..., a_m$ $(1 ≤ a_i ≤ n)$. Note that Xenia can have multiple consecutive tasks in one house.

## Output

Print a single integer — the time Xenia needs to complete all tasks.

Please, do not use the `%lld` specifier to read or write 64-bit integers in С++. It is preferred to use the `cin`, `cout` streams or the `%I64d` specifier.

## Examples

### Example 1

**Input:**
```
4 3
3 2 3
```
**Output:**
```
6
```

### Example 2

**Input:**
```
4 3
2 3 3
```
**Output:**
```
2
```

## Note

In the first test example the sequence of Xenia's moves along the ringroad looks as follows: $1 → 2 → 3 → 4 → 1 → 2 → 3$. This is optimal sequence. So, she needs 6 time units.

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
