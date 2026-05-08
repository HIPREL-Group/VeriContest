# Big Segment

Time limit: 2 seconds | Memory limit: 256 megabytes

A coordinate line has `n` segments. The `i`-th segment starts at position `l_i` and ends at position `r_i`, so it is written as `[l_i, r_i]`.

Determine whether one of the given segments covers all the others. Print the 1-based index of a segment that contains every segment in the input. If no such segment exists, print `-1`.

Formally, segment `[a, b]` covers segment `[c, d]` if `a <= c <= d <= b`.

## Input

The first line contains one integer `n` (`1 <= n <= 10^5`) — the number of segments.

Each of the next `n` lines contains two integers `l_i` and `r_i` (`1 <= l_i <= r_i <= 10^9`) — the endpoints of the `i`-th segment.

It is guaranteed that no two segments coincide.

## Output

Print a single integer — the number of a segment that covers all the others. If there is no such segment, print `-1`.

Segments are numbered from `1` in the order they appear in the input.

## Examples

**Input**
```text
3
1 1
2 2
3 3
```

**Output**
```text
-1
```

**Input**
```text
6
1 5
2 3
1 10
7 10
7 7
10 10
```

**Output**
```text
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
