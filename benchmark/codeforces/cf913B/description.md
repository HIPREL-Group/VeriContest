# Christmas Spruce

Time limit: 1 second | Memory limit: 256 megabytes

Consider a rooted tree. A rooted tree has one special vertex called the root. All edges are directed from the root. Vertex $u$ is called a *child* of vertex $v$ and vertex $v$ is called a *parent* of vertex $u$ if there exists a directed edge from $v$ to $u$. A vertex is called a *leaf* if it doesn't have children and has a parent.

Let's call a rooted tree a *spruce* if its every non-leaf vertex has at least $3$ leaf children. You are given a rooted tree, check whether it's a spruce.

The definition of a rooted tree can be found here.

## Input

The first line contains one integer $n$ — the number of vertices in the tree ($3 ≤ n ≤ 1 000$). Each of the next $n - 1$ lines contains one integer $p_i$ ($1 ≤ i ≤ n - 1$) — the index of the parent of the $i + 1$-th vertex ($1 ≤ pi ≤ i$).

Vertex $1$ is the root. It's guaranteed that the root has at least $2$ children.

## Output

Print "`Yes`" if the tree is a spruce and "`No`" otherwise.

## Examples

### Example 1

**Input:**
```
4
1
1
1
```

**Output:**
```
Yes
```

### Example 2

**Input:**
```
7
1
1
1
2
2
2
```

**Output:**
```
No
```

### Example 3

**Input:**
```
8
1
1
1
1
3
3
3
```

**Output:**
```
Yes
```

## Note

The first example:

The second example:

It is not a spruce, because the non-leaf vertex $1$ has only $2$ leaf children.

The third example:

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn is_spruce(n: usize, p: Vec<usize>) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    if let Some(Ok(line1)) = lines.next() {
        if let Ok(n) = line1.trim().parse::<usize>() {
            let mut p = Vec::new();
            for _ in 0..(n - 1) {
                if let Some(Ok(line)) = lines.next() {
                    if let Ok(pi) = line.trim().parse::<usize>() {
                        p.push(pi - 1);
                    }
                }
            }
            let result = Solution::is_spruce(n, p);
            if result {
                println!("Yes");
            } else {
                println!("No");
            }
        }
    }
}
```
