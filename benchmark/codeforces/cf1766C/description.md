# Hamiltonian Wall

Time limit: 2 seconds | Memory limit: 256 megabytes

Sir Monocarp Hamilton is planning to paint his wall. The wall can be represented as a grid, consisting of $$$2$$$ rows and $$$m$$$ columns. Initially, the wall is completely white.

Monocarp wants to paint a black picture on the wall. In particular, he wants cell $$$(i, j)$$$ (the $$$j$$$-th cell in the $$$i$$$-th row) to be colored black, if $$$c_{i, j} =$$$ '`B`', and to be left white, if $$$c_{i, j} =$$$ '`W`'. Additionally, he wants each column to have at least one black cell, so, for each $$$j$$$, the following constraint is satisfied: $$$c_{1, j}$$$, $$$c_{2, j}$$$ or both of them will be equal to '`B`'.

In order for the picture to turn out smooth, Monocarp wants to place down a paint brush in some cell $$$(x_1, y_1)$$$ and move it along the path $$$(x_1, y_1), (x_2, y_2), \dots, (x_k, y_k)$$$ so that:
- for each $$$i$$$, $$$(x_i, y_i)$$$ and $$$(x_{i+1}, y_{i+1})$$$ share a common side;
- all black cells appear in the path **exactly once**;
- white cells don't appear in the path.

Determine if Monocarp can paint the wall.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of testcases.

The first line of each testcase contains a single integer $$$m$$$ ($$$1 \le m \le 2 \cdot 10^5$$$) — the number of columns in the wall.

The $$$i$$$-th of the next two lines contains a string $$$c_i$$$, consisting of $$$m$$$ characters, where each character is either '`B`' or '`W`'. $$$c_{i, j}$$$ is '`B`', if the cell $$$(i, j)$$$ should be colored black, and '`W`', if the cell $$$(i, j)$$$ should be left white.

Additionally, for each $$$j$$$, the following constraint is satisfied: $$$c_{1, j}$$$, $$$c_{2, j}$$$ or both of them are equal to '`B`'.

The sum of $$$m$$$ over all testcases doesn't exceed $$$2 \cdot 10^5$$$.

## Output

For each testcase, print "`YES`" if Monocarp can paint a wall. Otherwise, print "`NO`".

## Examples

**Input:**
```
6
3
WBB
BBW
1
B
B
5
BWBWB
BBBBB
2
BW
WB
5
BBBBW
BWBBB
6
BWBBWB
BBBBBB
```

**Output:**
```
YES
YES
NO
NO
NO
YES
```

## Note

In the first testcase, Monocarp can follow a path $$$(2, 1)$$$, $$$(2, 2)$$$, $$$(1, 2)$$$, $$$(1, 3)$$$ with his brush. All black cells appear in the path exactly once, no white cells appear in the path.

In the second testcase, Monocarp can follow a path $$$(1, 1)$$$, $$$(2, 1)$$$.

In the third testcase:
- the path $$$(1, 1)$$$, $$$(2, 1)$$$, $$$(2, 2)$$$, $$$(2, 3)$$$, $$$(1, 3)$$$, $$$(2, 4)$$$, $$$(2, 5)$$$, $$$(1, 5)$$$ doesn't suffice because a pair of cells $$$(1, 3)$$$ and $$$(2, 4)$$$ doesn't share a common side;
- the path $$$(1, 1)$$$, $$$(2, 1)$$$, $$$(2, 2)$$$, $$$(2, 3)$$$, $$$(1, 3)$$$, $$$(2, 3)$$$, $$$(2, 4)$$$, $$$(2, 5)$$$, $$$(1, 5)$$$ doesn't suffice because cell $$$(2, 3)$$$ is visited twice;
- the path $$$(1, 1)$$$, $$$(2, 1)$$$, $$$(2, 2)$$$, $$$(2, 3)$$$, $$$(2, 4)$$$, $$$(2, 5)$$$, $$$(1, 5)$$$ doesn't suffice because a black cell $$$(1, 3)$$$ doesn't appear in the path;
- the path $$$(1, 1)$$$, $$$(2, 1)$$$, $$$(2, 2)$$$, $$$(2, 3)$$$, $$$(2, 4)$$$, $$$(2, 5)$$$, $$$(1, 5)$$$, $$$(1, 4)$$$, $$$(1, 3)$$$ doesn't suffice because a white cell $$$(1, 4)$$$ appears in the path.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_paint_wall(m: usize, row0: Vec<i64>, row1: Vec<i64>) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut iter = input.split_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    let mut i: usize = 0;
    while i < t {
        let m: usize = iter.next().unwrap().parse().unwrap();
        let s0: &str = iter.next().unwrap();
        let s1: &str = iter.next().unwrap();
        let b0 = s0.as_bytes();
        let b1 = s1.as_bytes();
        let mut row0: Vec<i64> = Vec::with_capacity(m);
        let mut row1: Vec<i64> = Vec::with_capacity(m);
        let mut j: usize = 0;
        while j < m {
            if b0[j] == b'B' { row0.push(1); } else { row0.push(0); }
            if b1[j] == b'B' { row1.push(1); } else { row1.push(0); }
            j = j + 1;
        }
        if Solution::can_paint_wall(m, row0, row1) {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
```
