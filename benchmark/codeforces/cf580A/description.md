# Kefa and First Steps

**Time limit:** 2 seconds  
**Memory limit:** 256 megabytes

Kefa decided to make some money doing business on the Internet for exactly `n` days. He knows that on the `i`-th day (`1 ≤ i ≤ n`) he makes `a_i` money. Kefa loves progress, so he wants to know the length of the **maximum non-decreasing subsegment** in the sequence `a`. A **subsegment** is a contiguous fragment of the sequence. A subsegment is **non-decreasing** if every pair of elements in it appears in non-decreasing order (equivalently, each step from left to right is non-decreasing).

## Input

The first line contains an integer `n` (`1 ≤ n ≤ 10^5`).

The second line contains `n` integers `a_1, a_2, …, a_n` (`1 ≤ a_i ≤ 10^9`).

## Output

Print a single integer: the length of the longest non-decreasing subsegment of `a`.

## Examples

### Example 1

**Input:**

```
6
2 2 1 3 4 1
```

**Output:**

```
3
```

### Example 2

**Input:**

```
3
2 2 9
```

**Output:**

```
3
```

## Note

In the first test, one maximum non-decreasing subsegment is the segment from the third to the fifth element.

In the second test, the whole array is non-decreasing.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn longest_non_decreasing_run(a: Vec<i64>) -> usize {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let mut a: Vec<i64> = Vec::with_capacity(n);
    for s in line.split_whitespace() {
        a.push(s.parse().unwrap());
    }
    let ans = Solution::longest_non_decreasing_run(a);
    println!("{}", ans);
}
```
