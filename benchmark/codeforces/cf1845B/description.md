# Come Together

Time limit: 2 seconds | Memory limit: 256 megabytes

Three people are located on an infinite integer grid at points $A(x_a, y_a)$, $B(x_b, y_b)$, and $C(x_c, y_c)$.

In one move, a person can move to one of the four neighboring cells (up, down, left, right).

You need to choose a meeting cell and move both $B$ and $C$ to that cell. Point $A$ is fixed and represents your position. Find the minimum total number of cells in a shortest common path segment that both $B$ and $C$ must share when moving toward $A$-aligned directions, which is the value required by the problem output.

Equivalent optimal formula:
- Start with $1$ (the meeting cell itself).
- Add overlap on the $x$-axis if $B$ and $C$ are on the same side of $A$ horizontally.
- Add overlap on the $y$-axis if $B$ and $C$ are on the same side of $A$ vertically.

## Input

The first line contains one integer $t$ ($1 \le t \le 1000$) — the number of test cases.

Each test case consists of one line with six integers:
$x_a, y_a, x_b, y_b, x_c, y_c$.

## Output

For each test case, print one integer — the minimum required value.

## Example

Input:
```text
4
0 0 1 1 2 2
0 0 1 1 -1 -1
0 0 2 0 5 0
1 3 2 2 3 1
```

Output:
```text
3
1
3
3
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_meeting_cells(ax: i64, ay: i64, bx: i64, by: i64, cx: i64, cy: i64) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let ax: i64 = it.next().unwrap().parse().unwrap();
        let ay: i64 = it.next().unwrap().parse().unwrap();
        let bx: i64 = it.next().unwrap().parse().unwrap();
        let by: i64 = it.next().unwrap().parse().unwrap();
        let cx: i64 = it.next().unwrap().parse().unwrap();
        let cy: i64 = it.next().unwrap().parse().unwrap();

        let ans = Solution::min_meeting_cells(ax, ay, bx, by, cx, cy);
        println!("{}", ans);
        i += 1;
    }
}
```
