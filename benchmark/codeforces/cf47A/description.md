# Triangular numbers

Time limit: 2 seconds | Memory limit: 256 megabytes

A triangular number is the number of dots in an equilateral triangle uniformly filled with dots. For example, three dots can be arranged in a triangle; thus three is a triangular number. The $*n*$-th triangular number is the number of dots in a triangle with $*n*$ dots on a side. . You can learn more about these numbers from Wikipedia (http://en.wikipedia.org/wiki/Triangular_number).

Your task is to find out if a given integer is a triangular number.

## Input

The first line contains the single number $*n*$ ($1 ≤ *n* ≤ 500$) — the given integer.

## Output

If the given integer is a triangular number output `YES`, otherwise output `NO`.

## Examples

### Example 1

**Input:**
```
1
```

**Output:**
```
YES
```

### Example 2

**Input:**
```
2
```

**Output:**
```
NO
```

### Example 3

**Input:**
```
3
```

**Output:**
```
YES
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn is_triangular(n: u32) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let n: u32 = input.trim().parse().unwrap();
    if Solution::is_triangular(n) {
        writeln!(out, "YES").unwrap();
    } else {
        writeln!(out, "NO").unwrap();
    }
}
```