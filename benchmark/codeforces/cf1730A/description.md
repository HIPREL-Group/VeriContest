# Planets

Time limit: 1 second | Memory limit: 256 megabytes

One day, Vogons wanted to build a new hyperspace highway through a distant system with $n$ planets. The $i$-th planet is on the orbit $a_i$; there could be multiple planets on the same orbit. All planets must be destroyed.

Vogons have two machines:

- The first machine destroys any single planet at cost $1$.
- The second machine destroys all planets on one orbit in a single operation at cost $c$.

Each machine may be used arbitrarily many times. Find the minimum total cost to destroy all planets.

## Input

The first line contains an integer $t$ ($1 \le t \le 100$) — the number of test cases.

Each test case has two lines:

- Two integers $n$ and $c$ ($1 \le n, c \le 100$).
- $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 100$).

## Output

For each test case print one integer — the minimum total cost.

## Examples

**Input:**

```
4
10 1
2 1 4 5 2 4 5 5 1 2
5 2
3 2 1 2 2
2 2
1 1
2 2
1 2
```

**Output:**

```
4
4
2
2
```

**Input:**

```
1
1 100
1
```

**Output:**

```
1
```

## Note

Orbits can be processed independently: for an orbit with $k$ planets, paying $k$ with the first machine or $c$ with the second yields cost $\min(k, c)$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn min_destroy_cost(orbits: Vec<i32>, c: i32) -> i32 {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut tc = 0usize;
    while tc < t {
        let nc: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let c = nc[1];
        let orbits: Vec<i32> = lines
            .next()
            .unwrap()
            .unwrap()
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let ans = Solution::min_destroy_cost(orbits, c);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
