# Showering

Time limit: 2 seconds | Memory limit: 256 megabytes

As a computer science student, Alex faces a hard challenge — showering. He tries to shower daily, but despite his best efforts there are always challenges. He takes $s$ minutes to shower and a day only has $m$ minutes! 

He already has $n$ tasks planned for the day. Task $i$ is represented as an interval $(l_i$, $r_i)$, which means that Alex is busy and can not take a shower in that time interval (at any point in time strictly between $l_i$ and $r_i$). **No two tasks overlap.**

Given all $n$ time intervals, will Alex be able to shower that day? In other words, will Alex have a free time interval of length at least $s$?

 In the first test case, Alex can shower for the first $3$ minutes of the day and not miss any of the tasks.

## Input

The first line contains a single integer $t$ ($1 \leq t \leq 10^4$) — the number of test cases.

The first line of each test case contains three integers $n$, $s$, and $m$ ($1 \leq n \leq 2 \cdot 10^5$; $1 \leq s, m \leq 10^9$) — the number of time intervals Alex already has planned, the amount of time Alex takes to take a shower, and the amount of minutes a day has.

Then $n$ lines follow, the $i$-th of which contains two integers $l_i$ and $r_i$ ($0 \leq l_i  \lt  r_i \leq m$) — the time interval of the $i$-th task. No two tasks overlap.

**Additional constraint on the input:** $l_i  \gt  r_{i-1}$ for every $i  \gt  1$.

The sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

## Output

For each test case output "`YES`" (without quotes) if Alex can take a shower for that given test case, and "`NO`" (also without quotes) otherwise.

You can output "`YES`" and "`NO`" in any case (for example, strings "`yEs`", "`yes`", and "`Yes`" will be recognized as a positive response).

## Examples

**Input:**
```
4
3 3 10
3 5
6 8
9 10
3 3 10
1 2
3 5
6 7
3 3 10
1 2
3 5
6 8
3 4 10
1 2
6 7
8 9
```

**Output:**
```
YES
YES
NO
YES
```

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn can_shower(s: i64, m: i64, l: Vec<i64>, r: Vec<i64>) -> bool {
        
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
        let s: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        let mut l: Vec<i64> = Vec::with_capacity(n);
        let mut r: Vec<i64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            l.push(it.next().unwrap().parse().unwrap());
            r.push(it.next().unwrap().parse().unwrap());
            i = i + 1;
        }
        let ans = Solution::can_shower(s, m, l, r);
        writeln!(out, "{}", if ans { "YES" } else { "NO" }).unwrap();
        tc = tc + 1;
    }
}
```
