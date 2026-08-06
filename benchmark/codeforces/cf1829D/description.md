# Gold Rush

Time limit: 2 seconds | Memory limit: 256 megabytes

Initially you have a single pile with $$$n$$$ gold nuggets. In an operation you can do the following: 
 - Take any pile and split it into two piles, so that one of the resulting piles has exactly twice as many gold nuggets as the other. (All piles should have an integer number of nuggets.) 
  
One possible move is to take a pile of size $$$6$$$ and split it into piles of sizes $$$2$$$ and $$$4$$$, which is valid since $$$4$$$ is twice as large as $$$2$$$. 
 Can you make a pile with **exactly** $$$m$$$ gold nuggets using zero or more operations?

## Input

The first line contains an integer $$$t$$$ ($$$1 \leq t \leq 1000$$$) — the number of test cases.

The only line of each test case contains two integers $$$n$$$ and $$$m$$$ ($$$1 \leq n, m \leq 10^7$$$) — the starting and target pile sizes, respectively.

## Output

For each test case, output "`YES`" if you can make a pile of size exactly $$$m$$$, and "`NO`" otherwise.

You can output the answer in any case (for example, the strings "`yEs`", "`yes`", "`Yes`" and "`YES`" will be recognized as a positive answer).

## Example

**Input:**
```
11
6 4
9 4
4 2
18 27
27 4
27 2
27 10
1 1
3 1
5 1
746001 2984004
```
**Output:**
```
YES
YES
NO
NO
YES
YES
NO
YES
YES
NO
NO
```

## Note

The first test case is pictured in the statement. We can make a pile of size $$$4$$$.

In the second test case, we can perform the following operations: $$$\{\color{red}{9}\} \to \{\color{red}{6},3\} \to \{4,2,3\}$$$. The pile that is split apart is colored red before each operation.

In the third test case, we can't perform a single operation.

In the fourth test case, we can't end up with a larger pile than we started with.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn can_obtain(n: i64, m: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: i64 = it.next().unwrap().parse().unwrap();
        let m: i64 = it.next().unwrap().parse().unwrap();
        if Solution::can_obtain(n, m) {
            out.push_str("YES\n");
        } else {
            out.push_str("NO\n");
        }
    }

    print!("{}", out);
}
```
