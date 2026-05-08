# Perfect Permutation

Time limit: 2 seconds | Memory limit: 256 megabytes

A *permutation* is a sequence of integers $*p*1, *p*2, ..., *p**n*$, consisting of $*n*$ distinct positive integers, each of them doesn't exceed $*n*$. Let's denote the $*i*$-th element of permutation $*p*$ as $*p**i*$. We'll call number $*n*$ the size of permutation $*p*1, *p*2, ..., *p**n*$.

Nickolas adores permutations. He likes some permutations more than the others. He calls such permutations perfect. A *perfect* permutation is such permutation $*p*$ that for any $*i*$ $(1 ≤ *i* ≤ *n*)$ ($*n*$ is the permutation size) the following equations hold $*p**p**i* = *i*$ and $*p**i* ≠ *i*$. Nickolas asks you to print any perfect permutation of size $*n*$ for the given $*n*$.

## Input

A single line contains a single integer $*n*$ ($1 ≤ *n* ≤ 100$) — the permutation size.

## Output

If a perfect permutation of size $*n*$ doesn't exist, print a single integer -1. Otherwise print $*n*$ distinct integers from 1 to $*n*$, $*p*1, *p*2, ..., *p**n*$ — permutation $*p*$, that is perfect. Separate printed numbers by whitespaces.

## Examples

### Example 1

**Input:**
```
1
```

**Output:**
```
-1
```

### Example 2

**Input:**
```
2
```

**Output:**
```
2 1
```

### Example 3

**Input:**
```
4
```

**Output:**
```
2 1 4 3
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn perfect_permutation(n: u32) -> Option<Vec<u32>> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let n: u32 = iter.next().unwrap().parse().unwrap();
    match Solution::perfect_permutation(n) {
        None => writeln!(out, "-1").unwrap(),
        Some(v) => {
            let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
            writeln!(out, "{}", parts.join(" ")).unwrap();
        }
    }
}
```
