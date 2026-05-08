# Dreamoon and Sets

Time limit: 1 second | Memory limit: 256 megabytes

Dreamoon likes to play with sets and integers. Let $\gcd(a,b)$ denote the largest positive integer that divides both $a$ and $b$.

Let $S$ be a set of exactly four distinct integers greater than $0$. Define $S$ to be of **rank** $k$ if and only if for every pair of distinct elements $s_i, s_j$ from $S$, $\gcd(s_i, s_j) = k$.

Given $k$ and $n$, Dreamoon wants to build $n$ sets of rank $k$ using integers from $1$ to $m$ such that no integer appears in two different sets (some integers may be unused). Find the **minimum** $m$ for which this is possible and print one valid construction.

## Input

The single line contains two space-separated integers $n$, $k$ ($1 \le n \le 10\,000$, $1 \le k \le 100$).

## Output

Print $m$ on the first line. Then print $n$ lines, each with four space-separated integers — the $i$-th set.

The order of sets and the order within each set does not matter. If several solutions achieve minimal $m$, print any.

## Examples

### Example 1

**Input:**
```
1 1
```

**Output:**
```
5
1 2 3 5
```

### Example 2

**Input:**
```
2 2
```

**Output:**
```
22
2 4 6 22
14 18 10 16
```

## Note

$\{1,2,3,4\}$ is not rank $1$ because $\gcd(2,4)=2 \ne 1$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn build_dreamoon_sets(n: usize, k: i32) -> Vec<Vec<i32>> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let line = lines.next().unwrap().unwrap();
    let mut parts = line.split_whitespace();
    let n: usize = parts.next().unwrap().parse().unwrap();
    let k: i32 = parts.next().unwrap().parse().unwrap();
    let m = k * (6 * n as i32 - 1);
    let sets = Solution::build_dreamoon_sets(n, k);
    println!("{}", m);
    let mut idx: usize = 0;
    while idx < sets.len() {
        let row = &sets[idx];
        println!("{} {} {} {}", row[0], row[1], row[2], row[3]);
        idx = idx + 1;
    }
}
```
