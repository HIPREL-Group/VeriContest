# k-Tree

Time limit: 1 second | Memory limit: 256 megabytes

Quite recently a creative student Lesha had a lecture on trees. After the lecture, Lesha was inspired and came up with a tree of his own which he called a $k$-tree.

A $k$-tree is an infinite rooted tree where:

- each vertex has exactly $k$ children;
- each edge has some weight;
- if we look at the edges going from some vertex to its children, then their weights are exactly $1, 2, 3, \ldots, k$.

The original statement includes a picture showing part of a 3-tree.

As soon as Dima, a good friend of Lesha, found out about the tree, he immediately wondered: "How many paths of total weight $n$ (the sum of all edge weights on the path) are there, starting from the root of a $k$-tree and containing at least one edge of weight at least $d$?"

Help Dima find the answer. As the number of ways can be rather large, print it modulo $1000000007$ ($10^9 + 7$).

## Input

A single line contains three space-separated integers: $n$, $k$, and $d$ ($1 \le n, k \le 100$; $1 \le d \le k$).

## Output

Print a single integer: the answer to the problem modulo $1000000007$ ($10^9 + 7$).

## Examples

### Example 1

**Input:**
```
3 3 2
```

**Output:**
```
3
```

### Example 2

**Input:**
```
3 3 3
```

**Output:**
```
1
```

### Example 3

**Input:**
```
4 3 2
```

**Output:**
```
6
```

### Example 4

**Input:**
```
4 5 2
```

**Output:**
```
7
```

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn count_k_tree_paths(n: i32, k: i32, d: i32) -> i32 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let n: i32 = it.next().unwrap().parse().unwrap();
    let k: i32 = it.next().unwrap().parse().unwrap();
    let d: i32 = it.next().unwrap().parse().unwrap();
    let answer = Solution::count_k_tree_paths(n, k, d);
    println!("{}", answer);
}
```
