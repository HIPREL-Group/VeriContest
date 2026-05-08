# Manhattan Circle

Time limit: 2 seconds | Memory limit: 256 megabytes

Given a $$$n$$$ by $$$m$$$ grid consisting of '.' and '#' characters, there exists a whole manhattan circle on the grid. The top left corner of the grid has coordinates $$$(1,1)$$$, and the bottom right corner has coordinates $$$(n, m)$$$.

Point ($$$a, b$$$) belongs to the manhattan circle centered at ($$$h, k$$$) if $$$|h - a| + |k - b|  \lt  r$$$, where $$$r$$$ is a positive constant.

On the grid, the set of points that are part of the manhattan circle is marked as '#'. Find the coordinates of the center of the circle.

## Input

The first line contains $$$t$$$ ($$$1 \leq t \leq 1000$$$)  — the number of test cases.

The first line of each test case contains $$$n$$$ and $$$m$$$ ($$$1 \leq n \cdot m \leq 2 \cdot 10^5$$$) — the height and width of the grid, respectively. 

The next $$$n$$$ lines contain $$$m$$$ characters '.' or '#'. If the character is '#', then the point is part of the manhattan circle.

It is guaranteed the sum of $$$n \cdot m$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$, and there is a whole manhattan circle on the grid.

## Output

For each test case, output the two integers, the coordinates of the center of the circle.

## Examples

**Input:**
```
6
5 5
.....
.....
..#..
.....
.....
5 5
..#..
.###.
#####
.###.
..#..
5 6
......
......
.#....
###...
.#....
1 1
#
5 6
...#..
..###.
.#####
..###.
...#..
2 10
..........
...#......
```

**Output:**
```
3 3
3 3
4 2
1 1
3 4
2 4
```

## Starter Code

```rust
use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn manhattan_circle_center(grid: Vec<Vec<i32>>) -> (i32, i32) {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    let mut case_idx = 0usize;
    while case_idx < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let _m: usize = it.next().unwrap().parse().unwrap();

        let mut grid: Vec<Vec<i32>> = Vec::with_capacity(n);
        let mut i = 0usize;
        while i < n {
            let row = it.next().unwrap().as_bytes();
            let mut vals: Vec<i32> = Vec::with_capacity(row.len());
            let mut j = 0usize;
            while j < row.len() {
                vals.push(if row[j] == b'#' { 1 } else { 0 });
                j += 1;
            }
            grid.push(vals);
            i += 1;
        }

        let (r, c) = Solution::manhattan_circle_center(grid);
        out.push_str(&format!("{} {}\n", r, c));
        case_idx += 1;
    }

    print!("{}", out);
}
```
