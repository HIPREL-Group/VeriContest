# Matching Numbers

Time limit: 1 second | Memory limit: 256 megabytes

You are given an integer $$$n$$$. Pair the integers $$$1$$$ to $$$2n$$$ (i.e. each integer should be in exactly one pair) so that each sum of matched pairs is consecutive and distinct. 

Formally, let $$$(a_i, b_i)$$$ be the pairs that you matched. $$$\{a_1, b_1, a_2, b_2, \ldots, a_n, b_n\}$$$ should be a permutation of $$$\{1, 2, \ldots, 2n\}$$$. Let the sorted list of $$$\{a_1+b_1, a_2+b_2, \ldots, a_n+b_n\}$$$ be $$$s_1  \lt  s_2  \lt  \ldots  \lt  s_n$$$. We must have $$$s_{i+1}-s_i = 1$$$ for $$$1 \le i \le n - 1$$$.

## Input

Each test contains multiple test cases. The first line contains the number of test cases $$$t$$$ ($$$1 \le t \le 500$$$). The description of the test cases follows.

For each test case, a single integer $$$n$$$ ($$$1 \leq n \leq 10^5$$$) is given.

It is guaranteed that the sum of $$$n$$$ over all test cases doesn't exceed $$$10^5$$$.

## Output

For each test case, if it is impossible to make such a pairing, print "`No`".

Otherwise, print "`Yes`" followed by $$$n$$$ lines.

At each line, print two integers that are paired.

You can output the answer in any case (upper or lower). For example, the strings "`yEs`", "`yes`", "`Yes`", and "`YES`" will be recognized as positive responses.

If there are multiple solutions, print any.

## Examples

**Input:**
```
4
1
2
3
4
```

**Output:**
```
Yes
1 2
No
Yes
1 6
3 5
4 2
No
```

## Note

For the third test case, each integer from $$$1$$$ to $$$6$$$ appears once. The sums of matched pairs are $$$4+2=6$$$, $$$1+6=7$$$, and $$$3+5=8$$$, which are consecutive and distinct.

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn matching_numbers(n: i32) -> Option<Vec<(i32, i32)>> {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut c: usize = 0;
    while c < t {
        let n: i32 = it.next().unwrap().parse().unwrap();
        let ans = Solution::matching_numbers(n);
        match ans {
            None => {
                println!("No");
            }
            Some(v) => {
                println!("Yes");
                let mut idx: usize = 0;
                while idx < v.len() {
                    let p = v[idx];
                    println!("{} {}", p.0, p.1);
                    idx = idx + 1;
                }
            }
        }
        c = c + 1;
    }
}
```
