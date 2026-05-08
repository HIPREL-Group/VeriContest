# Roadside Trees (Simplified Edition)

Time limit: 2 seconds | Memory limit: 256 megabytes

Squirrel Liss loves nuts. There are $n$ trees (numbered $1$ to $n$ from west to east) along a street and there is a delicious nut on the top of each tree. The height of the tree $i$ is $h_i$. Liss wants to eat all nuts.

Now Liss is on the root of the tree with the number $1$. In one second Liss can perform one of the following actions:
 - Walk up or down one unit on a tree. 
- Eat a nut on the top of the current tree. 
- Jump to the next tree. In this action the height of Liss doesn't change. More formally, when Liss is at height $h$ of the tree $i$ ($1 ≤ i ≤ n - 1$), she jumps to height $h$ of the tree $i + 1$. This action can't be performed if $h > h_{i+1}$. 

Compute the minimal time (in seconds) required to eat all nuts.

## Input

The first line contains an integer $n$ ($1  ≤  n ≤ 10^5$) — the number of trees.

Next $n$ lines contains the height of trees: $i$-th line contains an integer $h_i$ ($1 ≤ h_i ≤ 10^4$) — the height of the tree with the number $i$.

## Output

Print a single integer — the minimal time required to eat all nuts in seconds.

## Examples

### Example 1

**Input:**
```
2
1
2
```

**Output:**
```
5
```

### Example 2

**Input:**
```
5
2
1
2
1
1
```

**Output:**
```
14
```

## Starter Code

```rust
use std::io;

struct Solution;

impl Solution {
    pub fn min_time(heights: Vec<i32>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let n: usize = input.trim().parse().unwrap();
    let mut heights = Vec::new();
    for _ in 0..n {
        let mut line = String::new();
        io::stdin().read_line(&mut line).unwrap();
        let h: i32 = line.trim().parse().unwrap();
        heights.push(h);
    }
    println!("{}", Solution::min_time(heights));
}
```
