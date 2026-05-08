# Right Left Wrong

Time limit: 2 seconds | Memory limit: 256 megabytes

Vlad found a strip of $n$ cells, numbered from left to right from $1$ to $n$. In the $i$-th cell, there is a positive integer $a_i$ and a letter $s_i$, where all $s_i$ are either '`L`' or '`R`'.

Vlad invites you to try to score the maximum possible points by performing any (possibly zero) number of operations.

In one operation, you can choose two indices $l$ and $r$ ($1 \le l  \lt  r \le n$) such that $s_l$ = '`L`' and $s_r$ = '`R`' and do the following:

 -  add $a_l + a_{l + 1} + \dots + a_{r - 1} + a_r$ points to the current score; 
-  replace $s_i$ with '`.`' for all $l \le i \le r$, meaning you can no longer choose these indices. 

For example, consider the following strip:

 $3$$5$$1$$4$$3$$2$`L``R``L``L``L``R` You can first choose $l = 1$, $r = 2$ and add $3 + 5 = 8$ to your score.

 $3$$5$$1$$4$$3$$2$`.``.``L``L``L``R` Then choose $l = 3$, $r = 6$ and add $1 + 4 + 3 + 2 = 10$ to your score.

 $3$$5$$1$$4$$3$$2$`.``.``.``.``.``.` As a result, it is impossible to perform another operation, and the final score is $18$.

What is the maximum score that can be achieved?

## Input

The first line contains one integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

The first line of each test case contains one integer $n$ ($2 \le n \le 2 \cdot 10^5$) — the length of the strip.

The second line of each test case contains $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 10^5$) — the numbers written on the strip.

The third line of each test case contains a string $s$ of $n$ characters '`L`' and '`R`'.

It is guaranteed that the sum of the values of $n$ across all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case, output one integer — the maximum possible number of points that can be scored.

## Examples

**Input:**
```
4
6
3 5 1 4 3 2
LRLLLR
2
2 8
LR
2
3 9
RL
5
1 2 3 4 5
LRLRR
```

**Output:**
```
18
10
0
22
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_score(a: Vec<i64>, s: Vec<u8>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut it = input.split_ascii_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            a.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let s_str = it.next().unwrap();
        let s: Vec<u8> = s_str.bytes().map(|b| match b {
            b'L' => 1u8,
            b'R' => 2u8,
            _ => 0u8,
        }).collect();
        let _ = n;
        let ans = Solution::max_score(a, s);
        writeln!(out, "{}", ans).unwrap();
        tc = tc + 1;
    }
}
```
