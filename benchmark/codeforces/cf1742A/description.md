# Sum

Time limit: 1 second | Memory limit: 256 megabytes

You are given three integers $$$a$$$, $$$b$$$, and $$$c$$$. Determine if one of them is the sum of the other two.

## Input

The first line contains a single integer $$$t$$$ ($$$1 \leq t \leq 9261$$$) — the number of test cases.

The description of each test case consists of three integers $$$a$$$, $$$b$$$, $$$c$$$ ($$$0 \leq a, b, c \leq 20$$$).

## Output

For each test case, output "`YES`" if one of the numbers is the sum of the other two, and "`NO`" otherwise.

You can output the answer in any case (for example, the strings "`yEs`", "`yes`", "`Yes`" and "`YES`" will be recognized as a positive answer).

## Examples

**Input:**

```
7
1 4 3
2 5 8
9 11 20
0 0 0
20 20 20
4 12 3
15 7 8
```

**Output:**

```
YES
NO
YES
YES
NO
NO
YES
```

## Note

In the first test case, $$$1 + 3 = 4$$$.

In the second test case, none of the numbers is the sum of the other two.

In the third test case, $$$9 + 11 = 20$$$.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn one_is_sum_of_others(a: i64, b: i64, c: i64) -> bool {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut k: usize = 0;
    while k < t {
        let a: i64 = it.next().unwrap().parse().unwrap();
        let b: i64 = it.next().unwrap().parse().unwrap();
        let c: i64 = it.next().unwrap().parse().unwrap();
        if Solution::one_is_sum_of_others(a, b, c) {
            println!("YES");
        } else {
            println!("NO");
        }
        k = k + 1;
    }
}
```
