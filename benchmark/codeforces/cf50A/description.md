# Domino piling

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given a rectangular board of $M × N$ squares. Also you are given an unlimited number of standard domino pieces of $2 × 1$ squares. You are allowed to rotate the pieces. You are asked to place as many dominoes as possible on the board so as to meet the following conditions:

1. Each domino completely covers two squares.

2. No two dominoes overlap.

3. Each domino lies entirely inside the board. It is allowed to touch the edges of the board.

Find the maximum number of dominoes, which can be placed under these restrictions.

## Input

In a single line you are given two integers $M$ and $N$ — board sizes in squares ($1 ≤ M ≤ N ≤ 16$).

## Output

Output one number — the maximal number of dominoes, which can be placed.

## Examples

### Example 1

**Input:**
```
2 4
```

**Output:**
```
4
```

### Example 2

**Input:**
```
3 3
```

**Output:**
```
4
```

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn max_dominoes(m: u32, n: u32) -> u32 {
        
    }
}

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read line");
    let parts: Vec<u32> = line
        .split_whitespace()
        .map(|s| s.parse().expect("integer"))
        .collect();
    let m = parts[0];
    let n = parts[1];
    println!("{}", Solution::max_dominoes(m, n));
}
```
