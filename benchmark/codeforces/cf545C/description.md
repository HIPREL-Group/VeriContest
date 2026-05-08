# Woodcutters

Time limit: 1 second | Memory limit: 256 megabytes

Little Susie listens to fairy tales before bed every day. Today's fairy tale was about wood cutters and the little girl immediately started imagining the choppers cutting wood. She imagined the situation that is described below.

There are $n$ trees located along the road at points with coordinates $x_1, x_2, \ldots, x_n$. Each tree has its height $h_i$. Woodcutters can cut down a tree and fell it to the left or to the right. After that it occupies one of the segments $[x_i - h_i, x_i]$ or $[x_i; x_i + h_i]$. The tree that is not cut down occupies a single point with coordinate $x_i$. Woodcutters can fell a tree if the segment to be occupied by the fallen tree doesn't contain any occupied point. The woodcutters want to process as many trees as possible, so Susie wonders, what is the maximum number of trees to fell.

## Input

The first line contains integer $n$ ($1 \le n \le 10^5$) — the number of trees.

Next $n$ lines contain pairs of integers $x_i, h_i$ ($1 \le x_i, h_i \le 10^9$) — the coordinate and the height of the $i$-th tree.

The pairs are given in the order of ascending $x_i$. No two trees are located at the point with the same coordinate.

## Output

Print a single number — the maximum number of trees that you can cut down by the given rules.

## Examples

### Example 1

**Input:**
```
5
1 2
2 1
5 10
10 9
19 1
```

**Output:**
```
3
```

### Example 2

**Input:**
```
5
1 2
2 1
5 10
10 9
20 1
```

**Output:**
```
4
```

## Note

In the first sample you can fell the trees like that: 
 - fell the $1$-st tree to the left — now it occupies segment $[ - 1;1]$ 
- fell the $2$-nd tree to the right — now it occupies segment $[2;3]$ 
- leave the $3$-rd tree — it occupies point $5$ 
- leave the $4$-th tree — it occupies point $10$ 
- fell the $5$-th tree to the right — now it occupies segment $[19;20]$ 

In the second sample you can also fell $4$-th tree to the right, after that it will occupy segment $[10;19]$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn max_felled_trees(x: Vec<i64>, h: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: usize = it.next().unwrap().parse().unwrap();
    let mut x: Vec<i64> = Vec::with_capacity(n);
    let mut h: Vec<i64> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n {
        let xi: i64 = it.next().unwrap().parse().unwrap();
        let hi: i64 = it.next().unwrap().parse().unwrap();
        x.push(xi);
        h.push(hi);
        j = j + 1;
    }
    let answer = Solution::max_felled_trees(x, h);
    println!("{}", answer);
}
```
