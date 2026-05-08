# B. Mark the Dust Sweeper

You are given an array a of length n.

In one operation, choose an index i (1 <= i < n) such that a_i > 0, then do:
- a_i := a_i - 1
- a_{i+1} := a_{i+1} + 1

Find the minimum number of operations needed so that all first n-1 elements become zero, i.e. a_1 = a_2 = ... = a_{n-1} = 0.

## Input

The first line contains an integer t, the number of test cases.

For each test case:
- The first line contains an integer n.
- The second line contains n integers a_1, a_2, ..., a_n.

It is guaranteed that the sum of n over all test cases does not exceed 2 * 10^5.

## Output

For each test case, print one integer: the minimum number of operations.

## Example

Input:

4
3
2 0 0
5
0 2 0 2 0
6
2 0 3 0 4 6
4
0 0 0 10

Output:

3
5
11
0

## Starter Code

```rust
use std::io::{self, Read};

struct Solution;

impl Solution {
    pub fn min_operations(a: Vec<i64>) -> i64 {
        
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut it = input.split_whitespace();
    let t: usize = it.next().unwrap().parse().unwrap();
    let mut tc: usize = 0;
    while tc < t {
        let n: usize = it.next().unwrap().parse().unwrap();
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let v: i64 = it.next().unwrap().parse().unwrap();
            a.push(v);
            i = i + 1;
        }
        let ans = Solution::min_operations(a);
        println!("{}", ans);
        tc = tc + 1;
    }
}
```
