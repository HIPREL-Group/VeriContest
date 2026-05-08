# Robin Hood and the Major Oak

Time limit: 1 second | Memory limit: 256 megabytes

*In Sherwood, the trees are our shelter, and we are all children of the forest.*

*The Major Oak in Sherwood is known for its majestic foliage, which provided shelter to Robin Hood and his band of merry men and women.*

The Major Oak grows $i^i$ new leaves in the $i$-th year. It starts with $1$ leaf in year $1$.

Leaves last for $k$ years on the tree. In other words, leaves grown in year $i$ last between years $i$ and $i+k-1$ inclusive.

Robin considers even numbers lucky. Help Robin determine whether the Major Oak will have an even number of leaves in year $n$.

## Input

The first line of the input contains a single integer $t$ ($1 \le t \le 10^4$) — the number of test cases.

Each test case consists of two integers $n$, $k$ ($1 \le n \le 10^9$, $1 \le k \le n$) — the requested year and the number of years during which the leaves remain.

## Output

For each test case, output one line, "`YES`" if in year $n$ the Major Oak will have an even number of leaves and "`NO`" otherwise.

You can output the answer in any case (upper or lower). For example, the strings "`yEs`", "`yes`", "`Yes`", and "`YES`" will be recognized as positive responses.

## Examples

**Input:**

```
5
1 1
2 1
2 2
3 2
4 4
```

**Output:**

```
NO
YES
NO
NO
YES
```

## Note

In the first test case, there is only $1$ leaf.

In the second test case, $k=1$, so in the $2$-nd year there will be $2^2=4$ leaves.

In the third test case, $k=2$, so in the $2$-nd year there will be $1+2^2=5$ leaves.

In the fourth test case, $k=2$, so in the $3$-rd year there will be $2^2 + 3^3 = 4 + 27 = 31$ leaves.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn major_oak_leaves_even(n: i64, k: i64) -> bool {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut i = 0usize;
    while i < t {
        let line = lines.next().unwrap().unwrap();
        let mut parts = line.split_whitespace();
        let n: i64 = parts.next().unwrap().parse().unwrap();
        let k: i64 = parts.next().unwrap().parse().unwrap();
        let yes = Solution::major_oak_leaves_even(n, k);
        if yes {
            println!("YES");
        } else {
            println!("NO");
        }
        i = i + 1;
    }
}
```
