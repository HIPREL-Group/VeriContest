# Leftmost Below

Time limit: 2 seconds | Memory limit: 256 megabytes

Consider an array $a_1, \ldots, a_n$. Initially, $a_i = 0$ for every $i$.

You can do operations of the following form.

- You choose an integer $x$ greater than $\min(a)$.
- Then, $i$ is defined as the minimum index such that $a_i < x$. In other words, $i$ is the unique integer between $1$ and $n$ inclusive such that $a_i < x$ and $a_j \geq x$ for every $1 \leq j \leq i-1$.
- Finally, $a_i$ is incremented by $x$.

For example, if $a = [6, 8, 2, 1]$ and you choose $x = 6$, then $i$ will be equal to $3$ (since $a_1 \geq 6$, $a_2 \geq 6$, and $a_3 < 6$) and $a$ will become $[6, 8, 8, 1]$.

You can do as many operations as you want. Can you reach a target array $b_1, \ldots, b_n$?

## Input

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10\,000$). The description of the test cases follows.

The first line of each test case contains a single integer $n$ ($2 \leq n \leq 200\,000$).

The second line of each test case contains $n$ integers $b_1, b_2, \ldots, b_n$ ($1 \le b_i \le 10^9$).

The sum of $n$ over all test cases does not exceed $200\,000$.

## Output

For each test case, print `YES` if you can reach the target array and `NO` otherwise.

You can output the answer in any case (upper or lower). For example, the strings "`yEs`", "`yes`", "`Yes`", and "`YES`" will be recognized as positive responses.

## Examples

**Input:**
```
4
4
5 6 1 1
3
3 1 2
3
40 60 90
2
1 1
```

**Output:**
```
YES
NO
NO
YES
```

## Note

In the first test case, one valid sequence of operations is:

- choose $x=2$, $a$ becomes $[2, 0, 0, 0]$
- choose $x=2$, $a$ becomes $[2, 2, 0, 0]$
- choose $x=3$, $a$ becomes $[5, 2, 0, 0]$
- choose $x=4$, $a$ becomes $[5, 6, 0, 0]$
- choose $x=1$, $a$ becomes $[5, 6, 1, 0]$
- choose $x=1$, $a$ becomes $[5, 6, 1, 1]$

In the second test case, there is no way to reach $[3, 1, 2]$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn leftmost_below(n: usize, b: Vec<i64>) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t_line = lines.next().unwrap().unwrap();
    let t: usize = t_line.trim().parse().unwrap();
    let mut out = String::new();
    for _ in 0..t {
        let n_line = lines.next().unwrap().unwrap();
        let n: usize = n_line.trim().parse().unwrap();
        let b_line = lines.next().unwrap().unwrap();
        let mut b: Vec<i64> = Vec::new();
        for part in b_line.split_whitespace() {
            b.push(part.parse().unwrap());
        }
        let ok = Solution::leftmost_below(n, b);
        if ok {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }
    print!("{}", out);
}
```
