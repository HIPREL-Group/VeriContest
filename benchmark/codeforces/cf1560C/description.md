# Infinity Table

Time limit: 1 second | Memory limit: 256 megabytes

Polycarp has found a table having an infinite number of rows and columns. The rows are numbered from $$$1$$$, starting from the topmost one. The columns are numbered from $$$1$$$, starting from the leftmost one.

Initially, the table hasn't been filled and Polycarp wants to fix it. He writes integers from $$$1$$$ and so on to the table as follows.
  The figure shows the placement of the numbers from $$$1$$$ to $$$10$$$. The following actions are denoted by the arrows. 
The leftmost topmost cell of the table is filled with the number $$$1$$$. Then he writes in the table all positive integers beginning from $$$2$$$ sequentially using the following algorithm.

First, Polycarp selects the leftmost non-filled cell in the first row and fills it. Then, while the left neighbor of the last filled cell is filled, he goes down and fills the next cell. So he goes down until the last filled cell has a non-filled neighbor to the left (look at the vertical arrow going down in the figure above).

After that, he fills the cells from the right to the left until he stops at the first column (look at the horizontal row in the figure above). Then Polycarp selects the leftmost non-filled cell in the first row, goes down, and so on.

A friend of Polycarp has a favorite number $$$k$$$. He wants to know which cell will contain the number. Help him to find the indices of the row and the column, such that the intersection of the row and the column is the cell containing the number $$$k$$$.

## Input

The first line contains one integer $$$t$$$ ($$$1 \le t \le 100$$$) — the number of test cases. Then $$$t$$$ test cases follow.

Each test case consists of one line containing one integer $$$k$$$ ($$$1 \le k \le 10^9$$$) which location must be found.

## Output

For each test case, output in a separate line two integers $$$r$$$ and $$$c$$$ ($$$r, c \ge 1$$$) separated by spaces — the indices of the row and the column containing the cell filled by the number $$$k$$$, respectively.

## Examples

**Input:**
```
7
11
14
5
4
1
2
1000000000
```

**Output:**
```
2 4
4 3
1 3
2 1
1 1
1 2
31623 14130
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn infinity_table_cell(k: i64) -> (i64, i64) {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let k: i64 = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let (r, c) = Solution::infinity_table_cell(k);
        println!("{} {}", r, c);
        i = i + 1;
    }
}
```
