# Second Order Statistics

Time limit: 2 seconds | Memory limit: 256 megabytes

Once Bob needed to find the second order statistics of a sequence of integer numbers. Lets choose each number from the sequence exactly once and sort them. The value on the second position is the second order statistics of the given sequence. In other words it is the smallest element strictly greater than the minimum. Help Bob solve this problem.

## Input

The first input line contains integer $*n*$ ($1 ≤ *n* ≤ 100$) — amount of numbers in the sequence. The second line contains $*n*$ space-separated integer numbers — elements of the sequence. These numbers don't exceed 100 in absolute value.

## Output

If the given sequence has the second order statistics, output this order statistics, otherwise output `NO`.

## Examples

### Example 1

**Input:**
```
4
1 2 2 -4
```

**Output:**
```
1
```

### Example 2

**Input:**
```
5
1 2 3 1 1
```

**Output:**
```
2
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn second_min(a: Vec<i32>, n: usize) -> Option<i32> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: usize = iter.next().unwrap().parse().unwrap();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let v: i32 = iter.next().unwrap().parse().unwrap();
        a.push(v);
    }
    match Solution::second_min(a, n) {
        Some(v) => writeln!(out, "{}", v).unwrap(),
        None => writeln!(out, "NO").unwrap(),
    }
}
```