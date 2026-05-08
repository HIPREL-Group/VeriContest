# Limited Repainting

Time limit: 2 seconds | Memory limit: 512 megabytes

You are given a strip, consisting of $$$n$$$ cells, all cells are initially colored red.

In one operation, you can choose a segment of consecutive cells and paint them **blue**. Before painting, the chosen cells can be either red or blue. Note that it is not possible to paint them red. You are allowed to perform at most $$$k$$$ operations (possibly zero).

For each cell, the desired color after all operations is specified: red or blue.

It is clear that it is not always possible to satisfy all requirements within $$$k$$$ operations. Therefore, for each cell, a penalty is also specified, which is applied if the cell ends up the wrong color after all operations. For the $$$i$$$-th cell, the penalty is equal to $$$a_i$$$.

The penalty of the final painting is calculated as the **maximum penalty** among all cells that are painted the wrong color. If there are no such cells, the painting penalty is equal to $$$0$$$.

What is the minimum penalty of the final painting that can be achieved?

## Input

The first line contains a single integer $$$t$$$ ($$$1 \le t \le 10^4$$$) — the number of test cases.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$1 \le n \le 3 \cdot 10^5$$$; $$$0 \le k \le n$$$) — the length of the strip and the maximum number of operations.

The second line contains a string $$$s$$$, consisting of $$$n$$$ characters '`R`' and/or '`B`'. '`R`' means that the cell should be painted red. '`B`' means that the cell should be painted blue.

The third line contains $$$n$$$ integers $$$a_1, a_2, \dots, a_n$$$ ($$$1 \le a_i \le 10^9$$$) — the penalty for each cell.

The sum of $$$n$$$ over all test cases does not exceed $$$3 \cdot 10^5$$$.

## Output

For each test case, print a single integer — the minimum penalty of the final painting.

## Examples

**Input:**
```
5
4 1
BRBR
9 3 5 4
4 1
BRBR
9 5 3 4
4 2
BRBR
9 3 5 4
10 2
BRBRBBRRBR
5 1 2 4 5 3 6 1 5 4
5 5
RRRRR
5 3 1 2 4
```

**Output:**
```
3
3
0
4
0
```

## Note

In the first test case, you can paint the cells from $$$1$$$ to $$$3$$$. The painting will be `BBBR`. So, only cell $$$2$$$ is painted the wrong color. Therefore, the penalty for it is the final penalty and equals $$$3$$$.

In the second test case, the painting `BBBR` will now result in a penalty of $$$5$$$. However, if you paint the cells from $$$1$$$ to $$$1$$$, resulting in `BRRR`, then only cell $$$3$$$ is painted the wrong color. The final penalty is $$$3$$$.

In the third test case, you can paint the cells from $$$1$$$ to $$$1$$$ and from $$$3$$$ to $$$3$$$. Then all cells will be the correct color, the penalty equals $$$0$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_penalty(n: usize, k: i32, s: Vec<char>, a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            for _ in 0..t {
                if let Some(Ok(line1)) = lines.next() {
                    let parts: Vec<usize> = line1.split_whitespace().map(|x| x.parse().unwrap()).collect();
                    if parts.len() >= 2 {
                        let n = parts[0];
                        let k = parts[1] as i32;
                        
                        let s_str = lines.next().unwrap().unwrap();
                        let s: Vec<char> = s_str.trim().chars().collect();
                        
                        let a_str = lines.next().unwrap().unwrap();
                        let a: Vec<i32> = a_str.split_whitespace().map(|x| x.parse().unwrap()).collect();
                        
                        let ans = Solution::min_penalty(n, k, s, a);
                        println!("{}", ans);
                    }
                }
            }
        }
    }
}
```
