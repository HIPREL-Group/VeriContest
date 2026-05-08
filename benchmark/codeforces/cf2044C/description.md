# Hard Problem

Time limit: 1 second | Memory limit: 256 megabytes

Ball is the teacher in Paperfold University. The seats of his classroom are arranged in $2$ rows with $m$ seats each.

Ball is teaching $a + b + c$ monkeys, and he wants to assign as many monkeys to a seat as possible. Ball knows that $a$ of them only want to sit in row $1$, $b$ of them only want to sit in row $2$, and $c$ of them have no preference. Only one monkey may sit in each seat, and each monkey's preference must be followed if it is seated.

What is the maximum number of monkeys that Ball can seat?

## Input

The first line contains an integer $t$ ($1 \leq t \leq 10^4$) — the number of test cases.

Each test case contains four integers $m$, $a$, $b$, and $c$ ($1 \leq m, a, b, c \leq 10^8$).

## Output

For each test case, output the maximum number of monkeys you can seat.

## Examples

**Input:**
```
5
10 5 5 10
3 6 1 1
15 14 12 4
1 1 1 1
420 6 9 69
```

**Output:**
```
20
5
30
2
84
```

## Note

In the second test case, $6$ monkeys want to sit in the front row, but only $3$ seats are available. The monkeys that have no preference and the monkeys who prefer sitting in the second row can sit in the second row together. Thus, the answer is $3+2=5$.

## Starter Code

```rust
use std::io::{self, Read, Write, BufWriter};

struct Solution;

impl Solution {
    pub fn max_monkeys(m: u64, a: u64, b: u64, c: u64) -> u64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut iter = input.split_ascii_whitespace();
    let t: usize = iter.next().unwrap().parse().unwrap();
    for _ in 0..t {
        let m: u64 = iter.next().unwrap().parse().unwrap();
        let a: u64 = iter.next().unwrap().parse().unwrap();
        let b: u64 = iter.next().unwrap().parse().unwrap();
        let c: u64 = iter.next().unwrap().parse().unwrap();
        writeln!(out, "{}", Solution::max_monkeys(m, a, b, c)).unwrap();
    }
}
```
