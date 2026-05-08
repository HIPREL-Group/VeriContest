# Matrix Rotation

Time limit: 2 seconds | Memory limit: 512 megabytes

You have a matrix $2 \times 2$ filled with **distinct** integers. You want your matrix to become beautiful. The matrix is beautiful if the following two conditions are satisfied:

- in each row, the first element is smaller than the second element;
- in each column, the first element is smaller than the second element.

You can perform the following operation on the matrix any number of times: rotate it clockwise by $90$ degrees, so the top left element shifts to the top right cell, the top right element shifts to the bottom right cell, and so on.

Determine if it is possible to make the matrix beautiful by applying zero or more operations.

## Input

The first line contains one integer $t$ ($1 \le t \le 1000$) — the number of test cases.

Each test case consists of two lines. Each of those lines contains two integers — the elements of the corresponding row of the matrix. In each matrix, all four elements are distinct integers from $1$ to $100$.

## Output

For each test case, print `YES` if the matrix can become beautiful, or `NO` otherwise. You may print each letter in any case (`YES`, `yes`, `Yes` will all be recognized as positive answer, `NO`, `no` and `nO` will all be recognized as negative answer).

## Examples

**Input:**

```
6
1 3
5 7
8 10
3 4
8 10
4 3
6 1
9 2
7 5
4 2
1 2
4 3
```

**Output:**

```
YES
YES
NO
YES
YES
NO
```

**Note:** In the first test case the matrix is already beautiful. In the second, no rotation yields a beautiful matrix. In the third, a $90^\circ$ clockwise rotation yields $\begin{pmatrix} 3 & 4 \\ 1 & 2 \end{pmatrix}$, which is beautiful.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn can_make_beautiful(a: i32, b: i32, c: i32, d: i32) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            let mut tc: usize = 0;
            while tc < t {
                if let Some(Ok(row1)) = lines.next() {
                    if let Some(Ok(row2)) = lines.next() {
                        let r1: Vec<i32> = row1.split_whitespace().map(|x| x.parse().unwrap()).collect();
                        let r2: Vec<i32> = row2.split_whitespace().map(|x| x.parse().unwrap()).collect();
                        if r1.len() >= 2 && r2.len() >= 2 {
                            let a = r1[0];
                            let b = r1[1];
                            let c = r2[0];
                            let d = r2[1];
                            if Solution::can_make_beautiful(a, b, c, d) {
                                println!("YES");
                            } else {
                                println!("NO");
                            }
                        }
                    }
                }
                tc += 1;
            }
        }
    }
}
```
