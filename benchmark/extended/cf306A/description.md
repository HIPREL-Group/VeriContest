# Candies

Time limit: 1 second | Memory limit: 256 megabytes

Polycarpus has got $n$ candies and $m$ friends ($n ≥ m$). He wants to make a New Year present with candies to each friend. Polycarpus is planning to present all candies and he wants to do this in the fairest (that is, most equal) manner. He wants to choose such $ai$, where $ai$ is the number of candies in the $i$-th friend's present, that the maximum $ai$ differs from the least $ai$ as little as possible.

For example, if $n$ is divisible by $m$, then he is going to present the same number of candies to all his friends, that is, the maximum $ai$ won't differ from the minimum one.

## Input

The single line of the input contains a pair of space-separated positive integers $n$, $m$ ($1 ≤ n, m ≤ 100;n ≥ m$) — the number of candies and the number of Polycarpus's friends.

## Output

Print the required sequence $a1, a2, ..., am$, where $ai$ is the number of candies in the $i$-th friend's present. All numbers $ai$ must be positive integers, total up to $n$, the maximum one should differ from the minimum one by the smallest possible value.

## Examples

### Example 1

**Input:**
```
12 3
```

**Output:**
```
4 4 4
```

### Example 2

**Input:**
```
15 4
```

**Output:**
```
3 4 4 4
```

### Example 3

**Input:**
```
18 7
```

**Output:**
```
2 2 2 3 3 3 3
```

## Note

Print $ai$ in any order, separate the numbers by spaces.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn fair_candy_split(n: i32, m: i32) -> Vec<i32> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let line = stdin.lock().lines().next().unwrap().unwrap();
    let mut it = line.split_whitespace();
    let n: i32 = it.next().unwrap().parse().unwrap();
    let m: i32 = it.next().unwrap().parse().unwrap();
    let v = Solution::fair_candy_split(n, m);
    let mut j: usize = 0;
    while j < v.len() {
        if j > 0 {
            print!(" ");
        }
        print!("{}", v[j]);
        j = j + 1;
    }
    println!();
}
```
