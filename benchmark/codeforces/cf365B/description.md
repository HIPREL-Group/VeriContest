# The Fibonacci Segment

Time limit: 1000 ms | Memory limit: 256 MiB

You are given an array `a1, a2, ..., an`.

A segment `[l, r]` is called good if, for every `i` such that `l + 2 <= i <= r`, we have:

`ai = a(i-1) + a(i-2)`

The length of segment `[l, r]` is `r - l + 1`. A segment of length `1` or `2` is always good.

Find the maximum possible length of a good segment.

## Input

The first line contains one integer `n` (`1 <= n <= 100000`) — the number of elements in the array.

The second line contains `n` integers `a1, a2, ..., an` (`0 <= ai <= 10^9`).

## Output

Print one integer: the length of the longest good segment.

## Examples

**Input:**
```text
10
1 2 3 5 8 13 21 34 55 89
```

**Output:**
```text
10
```

**Input:**
```text
5
1 1 1 1 1
```

**Output:**
```text
2
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn longest_fibonacci_segment(nums: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut nums: Vec<i64> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        nums.push(it.next().unwrap().parse().unwrap());
        i = i + 1;
    }
    let ans = Solution::longest_fibonacci_segment(nums);
    println!("{}", ans);
}
```
