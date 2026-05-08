# Bun Lover

Time limit: 3 seconds | Memory limit: 256 megabytes

Tema loves cinnabon rolls — buns with cinnabon and chocolate in the shape of a "snail".

Cinnabon rolls come in different sizes and are square when viewed from above. The most delicious part of a roll is the chocolate, which is poured in a thin layer over the cinnabon roll in the form of a spiral and around the bun.

For a cinnabon roll of size $n$, the length of the outer side of the square is $n$, and the length of the shortest vertical chocolate segment in the central part is one.

Formally, the bun consists of two dough spirals separated by chocolate. A cinnabon roll of size $n + 1$ is obtained from a cinnabon roll of size $n$ by wrapping each of the dough spirals around the cinnabon roll for another layer.

**It is important that a cinnabon roll of size $n$ is defined in a unique way.**

Tema is interested in how much chocolate is in his cinnabon roll of size $n$. Since Tema has long stopped buying small cinnabon rolls, it is guaranteed that $n \ge 4$.

Answer this question by calculating the total length of the chocolate layer.

## Input

The first line of the input contains a single integer $t$ ($1 \le t \le 10^5$) — the number of test cases.

The following $t$ lines describe the test cases.

Each test case is described by a single integer $n$ ($4 \le n \le 10^9$) — the size of the cinnabon roll.

## Output

Output $t$ integers. The $i$-th of them should be equal to the total length of the chocolate layer in the $i$-th test case.

## Examples

**Input:**
```
4
4
5
6
179179179
```

**Output:**
```
26
37
50
32105178545472401
```

## Note

For $n = 4$, $n(n+2)+2 = 26$. For $n = 5$, the answer is $37$. For $n = 6$, the answer is $50$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn bun_chocolate_total(n: i64) -> i64 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let n: i64 = lines.next().unwrap().unwrap().trim().parse().unwrap();
        let ans = Solution::bun_chocolate_total(n);
        println!("{}", ans);
        i = i + 1;
    }
}
```
