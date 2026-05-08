# Stones on the Table

Time limit: 2 seconds | Memory limit: 256 megabytes

There are $n$ stones on the table in a row, each of them can be red, green or blue. Count the minimum number of stones to take from the table so that any two neighboring stones had different colors. Stones in a row are considered neighboring if there are no other stones between them.

## Input

The first line contains integer $n$ $(1 ≤ n ≤ 50)$ — the number of stones on the table. 

The next line contains string $s$, which represents the colors of the stones. We'll consider the stones in the row numbered from $1$ to $n$ from left to right. Then the $i$-th character $s$ equals "`R`", if the $i$-th stone is red, "`G`", if it's green and "`B`", if it's blue.

## Output

Print a single integer — the answer to the problem.

## Examples

### Example 1

**Input:**
```
3
RRG
```

**Output:**
```
1
```

### Example 2

**Input:**
```
5
RRRRR
```

**Output:**
```
4
```

### Example 3

**Input:**
```
4
BRBG
```

**Output:**
```
0
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_stones_to_remove(colors: Vec<u8>, n: usize) -> usize {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let s = lines.next().unwrap().unwrap();
    let colors: Vec<u8> = s
        .trim()
        .bytes()
        .map(|b| match b {
            b'R' => 0u8,
            b'G' => 1u8,
            b'B' => 2u8,
            _ => 0u8,
        })
        .collect();
    let ans = Solution::min_stones_to_remove(colors, n);
    println!("{}", ans);
}
```
