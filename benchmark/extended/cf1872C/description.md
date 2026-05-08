# Non-coprime Split

Time limit: 1 second | Memory limit: 256 megabytes

You are given two integers $$$l \le r$$$. You need to find **positive** integers $$$a$$$ and $$$b$$$ such that the following conditions are simultaneously satisfied:
- $$$l \le a + b \le r$$$
- $$$\gcd(a, b) \neq 1$$$

or report that they do not exist.

$$$\gcd(a, b)$$$ denotes the greatest common divisor of numbers $$$a$$$ and $$$b$$$. For example, $$$\gcd(6, 9) = 3$$$, $$$\gcd(8, 9) = 1$$$, $$$\gcd(4, 2) = 2$$$.

## Input

The first line of the input contains an integer $$$t$$$ ($$$1 \le t \le 500$$$) — the number of test cases.

Then the descriptions of the test cases follow.

The only line of the description of each test case contains $$$2$$$ integers $$$l, r$$$ ($$$1 \le l \le r \le 10^7$$$).

## Output

For each test case, output the integers $$$a, b$$$ that satisfy all the conditions on a separate line. If there is no answer, instead output a single number $$$-1$$$.

If there are multiple answers, you can output any of them.

## Examples

**Input:**
```
1111 151 318 1941 43777 7778000000 100000002000 20231791791 17917911 42 39840769 9840769
```

**Output:**
```
6 9
-1
14 4
36 6
111 666
4000000 5000000 
2009 7
-1
2 2
-1
6274 9834495
```

## Note

In the first test case, $$$11 \le 6 + 9 \le 15$$$, $$$\gcd(6, 9) = 3$$$, and all conditions are satisfied. Note that this is not the only possible answer, for example, $$$\{4, 10\}, \{5, 10\}, \{6, 6\}$$$ are also valid answers for this test case.

In the second test case, the only pairs $$$\{a, b\}$$$ that satisfy the condition $$$1 \le a + b \le 3$$$ are $$$\{1, 1\}, \{1, 2\}, \{2, 1\}$$$, but in each of these pairs $$$\gcd(a, b)$$$ equals $$$1$$$, so there is no answer.

In the third sample test, $$$\gcd(14, 4) = 2$$$.

## Starter Code

```rust
use std::io::{self, BufRead};

struct Solution;

impl Solution {
    pub fn non_coprime_split(l: i32, r: i32) -> Option<(i32, i32)> {
        
    }
}

fn main() {
    let stdin = io::stdin();
    let mut lines = stdin.lock().lines();
    let t: usize = lines.next().unwrap().unwrap().trim().parse().unwrap();
    let mut j: usize = 0;
    while j < t {
        let line = lines.next().unwrap().unwrap();
        let mut it = line.split_whitespace();
        let l: i32 = it.next().unwrap().parse().unwrap();
        let r: i32 = it.next().unwrap().parse().unwrap();
        match Solution::non_coprime_split(l, r) {
            Some((a, b)) => {
                println!("{} {}", a, b);
            }
            None => {
                println!("-1");
            }
        }
        j = j + 1;
    }
}
```
