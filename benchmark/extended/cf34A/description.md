# Reconnaissance 2

Time limit: 1 second | Memory limit: 256 megabytes

$n$ soldiers stand in a circle. For each soldier, his height $ai$ is known. A reconnaissance unit can be made of such two **neighbouring** soldiers, whose height difference is minimal, i.e. $|ai - aj|$ is minimal. So each of them will be less noticeable with the other. Output any pair of soldiers that can form a reconnaissance unit.

## Input

The first line contains an integer $n$ ($2 ≤ n ≤ 100$) — the number of soldiers. Then follow the heights of the soldiers in their order in the circle — $n$ space-separated integers $a1, a2, ..., an$ ($1 ≤ ai ≤ 1000$). The soldier heights are given in a clockwise or counterclockwise direction.

## Output

Output two integers — indices of **neighbouring** soldiers, who should form a reconnaissance unit. If there are many optimal solutions, output any of them. Remember that the soldiers stand in a circle.

## Examples

### Example 1

**Input:**
```
5
10 12 13 15 10
```

**Output:**
```
5 1
```

### Example 2

**Input:**
```
4
10 20 30 40
```

**Output:**
```
1 2
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_adjacent_pair(heights: Vec<i32>, n: usize) -> (usize, usize) {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let line = lines.next().unwrap().unwrap();
    let heights: Vec<i32> = line
        .split_whitespace()
        .map(|s| s.parse().unwrap())
        .collect();
    let (i, j) = Solution::min_adjacent_pair(heights, n);
    println!("{} {}", i + 1, j + 1);
}
```
