# Beautiful Matrix

Time limit: 2 seconds | Memory limit: 256 megabytes

You have a 5×5 matrix containing 24 zeroes and exactly one 1. The goal is to move the 1 to the center of the matrix (row 3, column 3 in 1-based indexing) using the minimum number of moves.

**Allowed operations:** Swap two adjacent rows, or swap two adjacent columns.

## Input

Five lines, each containing five space-separated integers (0 or 1). The matrix has exactly one 1 and 24 zeroes.

## Output

A single integer — the minimum number of moves needed to bring the 1 to the center (position (3,3) in 1-based indexing, i.e. (2,2) in 0-based).

## Examples

**Input:**
```
0 0 0 0 0
0 0 0 0 1
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
```

**Output:**
```
3
```

(The 1 is at 1-based (2,5); Manhattan distance to center (3,3) is |2-3| + |5-3| = 1 + 2 = 3.)

**Input:**
```
0 0 0 0 0
0 0 1 0 0
0 0 0 0 0
0 0 0 0 0
0 0 0 0 0
```

**Output:**
```
1
```

(1 is at (2,3); distance |2-3| + |3-3| = 1.)

## Note

The minimum number of moves equals the Manhattan distance from the current position of the 1 to the center (2,2) in 0-based indexing.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_moves_beautiful_matrix(grid: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut grid: Vec<i32> = Vec::new();
    for _ in 0..5 {
        let mut line = String::new();
        stdin.lock().read_line(&mut line).expect("read line");
        for s in line.split_whitespace() {
            grid.push(s.parse::<i32>().expect("integer"));
        }
    }
    let ans = Solution::min_moves_beautiful_matrix(grid);
    println!("{}", ans);
}
```
