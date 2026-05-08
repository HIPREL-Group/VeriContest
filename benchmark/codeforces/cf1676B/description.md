# Equal Candies

Time limit: 2 seconds | Memory limit: 256 megabytes

There are n boxes, and the i-th box contains a_i candies.

In one operation, you can choose any box and eat exactly one candy from it.
You want all boxes to end up with the same number of candies.

For each test case, find the minimum number of operations needed.

## Input

The first line contains an integer t — the number of test cases.

For each test case:
- The first line contains an integer n.
- The second line contains n integers a_1, a_2, ..., a_n.

## Output

For each test case, output one integer: the minimum number of operations.

## Note

Since operations only decrease candy counts, all boxes must be reduced to the minimum initial value. So the answer is:

sum(a_i - min(a)).

## Starter Code

```rust
use std::io::{self, Read};

pub struct Solution;

impl Solution {
    pub fn min_operations_to_equal(candies: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();

    let t: usize = it.next().unwrap().parse().unwrap();
    let mut out = String::new();

    for _ in 0..t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut candies: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let x: i64 = it.next().unwrap().parse().unwrap();
            candies.push(x);
        }
        let ans = Solution::min_operations_to_equal(candies);
        out.push_str(&format!("{}\n", ans));
    }

    print!("{}", out);
}
```
