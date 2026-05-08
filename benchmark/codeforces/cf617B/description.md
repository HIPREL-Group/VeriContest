# Chocolate

Time limit: 1 second | Memory limit: 256 megabytes

Bob loves everything sweet. His favorite chocolate bar consists of pieces; each piece may contain a nut. Bob wants to break the bar into multiple pieces so that each part contains **exactly** one nut and any break line goes between two adjacent pieces.

You are asked to calculate the number of ways he can do it. Two ways to break the chocolate are considered distinct if one of them contains a break between some two adjacent pieces and the other one does not.

Please note that if Bob does not make any breaks, the whole bar forms one piece and it still must have exactly one nut.

## Input

The first line contains an integer $n$ ($1 \le n \le 100$) — the number of pieces in the chocolate bar.

The second line contains $n$ integers $a_i$ ($0 \le a_i \le 1$), where $0$ represents a piece without a nut and $1$ stands for a piece with a nut.

## Output

Print the number of ways to break the chocolate into pieces so that each piece contains exactly one nut.

## Examples

### Example 1

**Input:**

```
3
0 1 0
```

**Output:**

```
1
```

### Example 2

**Input:**

```
5
1 0 1 0 1
```

**Output:**

```
4
```

## Note

In the first sample there is exactly one nut, so the number of ways equals $1$ — Bob should not make any breaks.

In the second sample you can break the bar in four ways:

`10|10|1`

`1|010|1`

`10|1|01`

`1|01|01`

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn chocolate_ways(n: usize, a: Vec<i32>) -> i128 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    lock.read_line(&mut line).expect("read line");
    let n: usize = line.trim().parse().expect("n");
    line.clear();
    lock.read_line(&mut line).expect("read line");
    let mut a: Vec<i32> = Vec::new();
    for s in line.split_whitespace() {
        a.push(s.parse::<i32>().expect("integer"));
    }
    println!("{}", Solution::chocolate_ways(n, a));
}
```
