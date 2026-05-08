# Raspberries

Time limit: 2 seconds | Memory limit: 256 megabytes

You are given an array of integers $$$a_1, a_2, \ldots, a_n$$$ and a number $$$k$$$ ($$$2 \leq k \leq 5$$$). In one operation, you can do the following:

- Choose an index $$$1 \leq i \leq n$$$,
- Set $$$a_i = a_i + 1$$$.

Find the minimum number of operations needed to make the product of all the numbers in the array $$$a_1 \cdot a_2 \cdot \ldots \cdot a_n$$$ divisible by $$$k$$$.

## Input

Each test consists of multiple test cases. The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 10^4$$$) — the number of test cases. Then follows the description of the test cases.

The first line of each test case contains two integers $$$n$$$ and $$$k$$$ ($$$2 \leq n \leq 10^5$$$, $$$2 \leq k \leq 5$$$) — the size of the array $$$a$$$ and the number $$$k$$$.

The second line of each test case contains $$$n$$$ integers $$$a_1, a_2, \ldots, a_n$$$ ($$$1 \leq a_i \leq 10$$$).

It is guaranteed that the sum of $$$n$$$ over all test cases does not exceed $$$2 \cdot 10^5$$$.

## Output

For each test case, output the minimum number of operations needed to make the product of all the numbers in the array divisible by $$$k$$$.

## Examples

**Input:**

```
15
2 5
7 3
3 3
7 4 1
5 2
9 7 7 3 9
5 5
5 4 1 2 3
7 4
9 5 1 5 9 5 1
3 4
6 3 6
3 4
6 1 5
3 4
1 5 9
4 4
1 4 1 1
3 4
3 5 3
4 5
8 9 9 3
2 5
1 6
2 5
10 10
4 5
1 6 1 1
2 5
7 7
```

**Output:**

```
2
2
1
0
2
0
1
2
0
1
1
4
0
4
3
```

## Note

In the first test case, you can choose index $$$i = 2$$$ twice. After that, the array becomes $$$a = [7, 5]$$$. The product is $$$35$$$, which is divisible by $$$5$$$.

In the second test case, the product is already divisible by $$$5$$$, so no operations are needed.

In the third test case, the product $$$2 \cdot 2 = 4$$$ is already divisible by $$$4$$$.

In the fourth test case, the factor $$$12$$$ is already a multiple of $$$3$$$, so the product is divisible by $$$3$$$ without any operations.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_ops(n: usize, k: i32, a: Vec<i32>) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(t_str)) = lines.next() {
        if let Ok(t) = t_str.trim().parse::<usize>() {
            for _ in 0..t {
                if let Some(Ok(line1)) = lines.next() {
                    let parts: Vec<i32> = line1
                        .split_whitespace()
                        .map(|x| x.parse().unwrap())
                        .collect();
                    if parts.len() >= 2 {
                        let n = parts[0] as usize;
                        let k = parts[1];
                        if let Some(Ok(a_str)) = lines.next() {
                            let a: Vec<i32> = a_str
                                .split_whitespace()
                                .map(|x| x.parse().unwrap())
                                .collect();
                            let ans = Solution::min_ops(n, k, a);
                            println!("{}", ans);
                        }
                    }
                }
            }
        }
    }
}
```
