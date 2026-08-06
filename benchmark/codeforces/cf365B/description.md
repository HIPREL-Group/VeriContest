# The Fibonacci Segment

Time limit: 1 second | Memory limit: 256 megabytes

You have array $a_1, a_2, ..., a_n$. Segment $[l, r]$ ($1 ≤ l ≤ r ≤ n$) is good if $a_i = a_i - 1 + a_i - 2$, for all $i$ $(l + 2 ≤ i ≤ r)$.

Let's define $len([l, r]) = r - l + 1$, $len([l, r])$ is the length of the segment $[l, r]$. Segment $[l_1, r_1]$, is longer than segment $[l_2, r_2]$, if $len([l_1, r_1]) > len([l_2, r_2])$.

Your task is to find a good segment of the maximum length in array $a$. Note that a segment of length $1$ or $2$ is always good.

## Input

The first line contains a single integer $n$ ($1 ≤ n ≤ 10^5$) — the number of elements in the array. The second line contains integers: $a_1, a_2, ..., a_n$ ($0 ≤ a_i ≤ 10^9$).

## Output

Print the length of the longest good segment in array $a$.

## Examples

### Example 1

**Input:**
```
10
1 2 3 5 8 13 21 34 55 89
```
**Output:**
```
10
```

### Example 2

**Input:**
```
5
1 1 1 1 1
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
