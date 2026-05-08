# Square

Time limit: 1 second | Memory limit: 256 megabytes

A square of positive (strictly greater than $0$) area is located on the coordinate plane, with sides parallel to the coordinate axes. You are given the coordinates of its corners, in random order. Your task is to find the area of the square.

## Input

Each test consists of several testcases. The first line contains one integer $t$ ($1 \le t \le 100$) — the number of testcases. The following is a description of the testcases.

Each testcase contains four lines, each line contains two integers $x_i, y_i$ ($-1000\le x_i, y_i\le 1000$), coordinates of the corners of the square.

It is guaranteed that there is a square with sides parallel to the coordinate axes, with positive (strictly greater than $0$) area, with corners in given points.

## Output

For each test case, print a single integer, the area of the square.

## Examples

**Input:**

```
3
1 2
4 5
1 5
4 2
-1 1
1 -1
1 1
-1 -1
45 11
45 39
17 11
17 39
```

**Output:**

```
9
4
784
```

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut k = 0usize;
    while k < t {
        let mut xs: Vec<i64> = Vec::new();
        let mut ys: Vec<i64> = Vec::new();
        let mut r = 0usize;
        while r < 4 {
            let line = lines.next().unwrap().unwrap();
            let mut parts = line.split_whitespace();
            let xi: i64 = parts.next().unwrap().parse().unwrap();
            let yi: i64 = parts.next().unwrap().parse().unwrap();
            xs.push(xi);
            ys.push(yi);
            r = r + 1;
        }
        let ans = Solution::axis_aligned_square_area(xs, ys);
        println!("{}", ans);
        k = k + 1;
    }
}
```
