# Big Segment

Time limit: 2 seconds | Memory limit: 256 megabytes

A coordinate line has $n$ segments, the $i$-th segment starts at the position $l_i$ and ends at the position $r_i$. We will denote such a segment as $[l_i, r_i]$.

You have suggested that one of the defined segments covers all others. In other words, there is such segment in the given set, which contains all other ones. Now you want to test your assumption. Find in the given set the segment which covers all other segments, and print its number. If such a segment doesn't exist, print -1.

Formally we will assume that segment $[a, b]$ covers segment $[c, d]$, if they meet this condition $a ≤ c ≤ d ≤ b$.

## Input

The first line contains integer $n$ ($1 ≤ n ≤ 10^5$) — the number of segments. Next $n$ lines contain the descriptions of the segments. The $i$-th line contains two space-separated integers $l_i, r_i$ ($1 ≤ l_i ≤ r_i ≤ 10^9$) — the borders of the $i$-th segment.

It is guaranteed that no two segments coincide.

## Output

Print a single integer — the number of the segment that covers all other segments in the set. If there's no solution, print -1.

The segments are numbered starting from $1$ in the order in which they appear in the input.

## Examples

### Example 1

**Input:**
```
3
1 1
2 2
3 3
```
**Output:**
```
-1
```

### Example 2

**Input:**
```
6
1 5
2 3
1 10
7 10
7 7
10 10
```
**Output:**
```
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn find_covering_segment(left: Vec<i32>, right: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut it = input.split_whitespace();
    let n = it.next().expect("n").parse::<usize>().expect("usize");
    let mut left = Vec::with_capacity(n);
    let mut right = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        left.push(it.next().expect("left").parse::<i32>().expect("i32"));
        right.push(it.next().expect("right").parse::<i32>().expect("i32"));
        i += 1;
    }
    let ans = Solution::find_covering_segment(left, right);
    if ans == 0 {
        println!("-1");
    } else {
        println!("{}", ans);
    }
}
```
