# Team (231A)

## Problem

One day three best friends Petya, Vasya and Tonya decided to form a team and take part in programming contests. Participants are usually offered several problems during programming contests. Long before the start the friends decided that they would implement a problem if at least two of them are sure about the solution. Otherwise, the friends won't write the problem's solution.

This contest offers n problems. For each problem we know Petya's view (1 if sure, 0 if not), Vasya's view, and Tonya's view. How many problems will the team implement?

## Input

- First line: single integer n (1 ≤ n ≤ 1000) — number of problems.
- Next n lines: each line has three space-separated integers (each 0 or 1) — Petya's, Vasya's, and Tonya's view for that problem.

## Output

Print a single integer — the number of problems the friends will implement (i.e. the number of rows where at least two of the three values are 1, i.e. the sum of the three elements is ≥ 2).

## Example

**Input:**
```
3
1 1 0
1 1 1
1 0 0
```

**Output:** 2

(Rows 0 and 1 have sum ≥ 2; row 2 has sum 1.)

## Constraints

- 1 ≤ n ≤ 1000
- Each of the three values per row is 0 or 1.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn count_teams_implement(grid: Vec<i32>, n: usize) -> usize {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let n: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut grid: Vec<i32> = Vec::with_capacity(3 * n);
    for _ in 0..n {
        let line = lines.next().unwrap().unwrap();
        let parts: Vec<i32> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        grid.push(parts[0]);
        grid.push(parts[1]);
        grid.push(parts[2]);
    }
    let ans = Solution::count_teams_implement(grid, n);
    println!("{}", ans);
}
```
